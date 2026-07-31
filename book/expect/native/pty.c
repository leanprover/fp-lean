/*
POSIX code for spawning and driving a child process on a pseudoterminal.

This is needed to cause Lean to not buffer its output.
*/

#define _XOPEN_SOURCE 700
#define _DARWIN_C_SOURCE
#define _DEFAULT_SOURCE

#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

/*
A running or finished child, reachable from Lean only as an opaque value, so that the process and
its terminal cannot be named by anything other than the calls below.
*/
typedef struct {
    pid_t pid;
    int fd;         /* -1 once the terminal has been released */
    bool reaped;
    uint32_t code;  /* meaningful once reaped */
} expect_pty_child;

static void expect_pty_reap(expect_pty_child *child) {
    int status = 0;
    while (waitpid(child->pid, &status, 0) < 0 && errno == EINTR) {}
    child->reaped = true;
    if (WIFEXITED(status)) child->code = (uint32_t)WEXITSTATUS(status);
    else if (WIFSIGNALED(status)) child->code = 128 + (uint32_t)WTERMSIG(status);
}

static void expect_pty_child_finalize(void *ptr) {
    expect_pty_child *child = (expect_pty_child *)ptr;
    if (child->fd >= 0) close(child->fd);
    if (!child->reaped) {
        kill(child->pid, SIGKILL);
        expect_pty_reap(child);
    }
    free(child);
}

static void expect_pty_child_foreach(void *ptr, b_lean_obj_arg f) {
    (void)ptr;
    (void)f;
}

static lean_external_class *g_expect_pty_child_class = NULL;
static pthread_once_t g_expect_pty_child_class_once = PTHREAD_ONCE_INIT;

static void expect_pty_register_child_class(void) {
    g_expect_pty_child_class =
        lean_register_external_class(expect_pty_child_finalize, expect_pty_child_foreach);
}

static lean_external_class *expect_pty_child_class(void) {
    pthread_once(&g_expect_pty_child_class_once, expect_pty_register_child_class);
    return g_expect_pty_child_class;
}

static expect_pty_child *expect_pty_unwrap(b_lean_obj_arg child) {
    return (expect_pty_child *)lean_get_external_data(child);
}

static lean_obj_res expect_pty_errno(const char *what, int err) {
    char buf[512];
    snprintf(buf, sizeof(buf), "%s: %s", what, strerror(err));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static lean_obj_res expect_pty_error(const char *what) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

/* Copies a Lean `Array String` into a NULL-terminated array of C strings. */
static char **expect_pty_strings(b_lean_obj_arg arr, size_t *count) {
    size_t n = lean_array_size(arr);
    char **out = (char **)calloc(n + 1, sizeof(char *));
    if (out == NULL) return NULL;
    for (size_t i = 0; i < n; i++) {
        const char *s = lean_string_cstr(lean_array_get_core(arr, i));
        out[i] = strdup(s);
        if (out[i] == NULL) {
            for (size_t j = 0; j < i; j++) free(out[j]);
            free(out);
            return NULL;
        }
    }
    if (count != NULL) *count = n;
    return out;
}

static void expect_pty_free_strings(char **strs) {
    if (strs == NULL) return;
    for (size_t i = 0; strs[i] != NULL; i++) free(strs[i]);
    free(strs);
}

/* The length of the name in a "NAME=VALUE" environment entry. */
static size_t expect_pty_name_len(const char *entry) {
    const char *eq = strchr(entry, '=');
    return eq == NULL ? strlen(entry) : (size_t)(eq - entry);
}

/* Whether a "NAME=VALUE" entry has the given name. */
static bool expect_pty_named(const char *entry, const char *name, size_t name_len) {
    return strncmp(entry, name, name_len) == 0 && entry[name_len] == '=';
}

/*
The environment for the child: the current one, less the names in `unset`, with the "NAME=VALUE"
entries of `overrides` replacing or extending what remains.

Built before forking, because the child may only use async-signal-safe calls.
*/
static char **expect_pty_child_env(b_lean_obj_arg overrides, b_lean_obj_arg unset) {
    size_t inherited = 0;
    while (environ[inherited] != NULL) inherited++;
    size_t override_count = lean_array_size(overrides);
    size_t unset_count = lean_array_size(unset);

    char **env = (char **)calloc(inherited + override_count + 1, sizeof(char *));
    if (env == NULL) return NULL;

    size_t n = 0;
    for (size_t i = 0; i < inherited; i++) {
        const char *entry = environ[i];
        size_t name_len = expect_pty_name_len(entry);
        bool drop = false;
        for (size_t j = 0; j < unset_count && !drop; j++) {
            const char *name = lean_string_cstr(lean_array_get_core(unset, j));
            drop = strlen(name) == name_len && strncmp(entry, name, name_len) == 0;
        }
        for (size_t j = 0; j < override_count && !drop; j++) {
            const char *o = lean_string_cstr(lean_array_get_core(overrides, j));
            drop = expect_pty_named(o, entry, name_len);
        }
        if (drop) continue;
        env[n] = strdup(entry);
        if (env[n] == NULL) goto fail;
        n++;
    }
    for (size_t j = 0; j < override_count; j++) {
        env[n] = strdup(lean_string_cstr(lean_array_get_core(overrides, j)));
        if (env[n] == NULL) goto fail;
        n++;
    }
    env[n] = NULL;
    return env;

fail:
    expect_pty_free_strings(env);
    return NULL;
}

/*
Allocates a pseudoterminal, returning the controlling end and, in `child_end`, the end that the
child runs on. On failure the result is -1, and the call that failed and its `errno` are reported in
`failed` and `err`.

A terminal whose far end nobody holds reports end of input, so the parent takes both ends at once
and keeps the far one until the child has inherited it. Every moment between the fork and that
point has a holder, so a read early in the session sees the session as running.

`ptsname` returns a pointer to storage that belongs to the process rather than to the caller, and
the next call to it overwrites that storage. Lean elaborates in more than one thread, so the whole
allocation is done under a lock.

Neither descriptor is inherited across an exec, so a process spawned elsewhere in the elaborator
cannot hold a terminal open behind our back.
*/
static int expect_pty_open(int *child_end, const char **failed, int *err) {
    static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
    pthread_mutex_lock(&lock);

    int controller = posix_openpt(O_RDWR | O_NOCTTY);
    if (controller < 0) {
        *failed = "posix_openpt";
        *err = errno;
        pthread_mutex_unlock(&lock);
        return -1;
    }
    fcntl(controller, F_SETFD, FD_CLOEXEC);
    if (grantpt(controller) < 0) {
        *failed = "grantpt";
        *err = errno;
        goto fail;
    }
    if (unlockpt(controller) < 0) {
        *failed = "unlockpt";
        *err = errno;
        goto fail;
    }
    const char *name = ptsname(controller);
    if (name == NULL) {
        *failed = "ptsname";
        *err = errno;
        goto fail;
    }
    *child_end = open(name, O_RDWR | O_NOCTTY);
    if (*child_end < 0) {
        *failed = "open";
        *err = errno;
        goto fail;
    }
    fcntl(*child_end, F_SETFD, FD_CLOEXEC);

    pthread_mutex_unlock(&lock);
    return controller;

fail:
    close(controller);
    pthread_mutex_unlock(&lock);
    return -1;
}

/*
Finds `command` on the `PATH` that the child will be given, returning a path to run, or NULL if
there is nothing to run.

The search happens in the parent, where allocation is safe: a forked child may use only
async-signal-safe calls until it execs, and `execvp` allocates while searching, so a child that
forked while another thread held the allocator's lock would wait for a thread that does not exist
in it. Searching here also lets a program that is missing be reported by name.

The entries that name a directory outright are the ones searched, so that the file tested here is
the file that runs once the child has changed to the directory it was given. A file that can be
executed is what counts as a match, so that a directory whose name happens to be the command's
leaves the rest of the `PATH` to be searched.
*/
static char *expect_pty_resolve(const char *command, char *const *env) {
    if (strchr(command, '/') != NULL) return strdup(command);

    const char *path = NULL;
    for (size_t i = 0; env[i] != NULL; i++) {
        if (strncmp(env[i], "PATH=", 5) == 0) path = env[i] + 5;
    }
    if (path == NULL) path = "/usr/bin:/bin";

    size_t command_len = strlen(command);
    const char *entry = path;
    while (true) {
        const char *sep = strchr(entry, ':');
        size_t len = sep == NULL ? strlen(entry) : (size_t)(sep - entry);

        if (len > 0 && entry[0] == '/') {
            char *candidate = (char *)malloc(len + command_len + 2);
            if (candidate == NULL) return NULL;
            memcpy(candidate, entry, len);
            candidate[len] = '/';
            memcpy(candidate + len + 1, command, command_len);
            candidate[len + command_len + 1] = '\0';
            struct stat info;
            if (stat(candidate, &info) == 0 && S_ISREG(info.st_mode) &&
                access(candidate, X_OK) == 0) {
                return candidate;
            }
            free(candidate);
        }

        if (sep == NULL) return NULL;
        entry = sep + 1;
    }
}

/* Starts `argv` on a new pseudoterminal in `cwd`. */
LEAN_EXPORT lean_obj_res expect_pty_spawn(b_lean_obj_arg argv, b_lean_obj_arg env_overrides,
                                          b_lean_obj_arg env_unset, b_lean_obj_arg cwd,
                                          lean_object *world) {
    (void)world;

    if (lean_array_size(argv) == 0) return expect_pty_error("No command to spawn");

    int child_end = -1;
    const char *failed = NULL;
    int err = 0;
    int controller = expect_pty_open(&child_end, &failed, &err);
    if (controller < 0) return expect_pty_errno(failed, err);

    /* A fixed size keeps the output of programs that wrap their output reproducible. */
    struct winsize size;
    memset(&size, 0, sizeof(size));
    size.ws_row = 24;
    size.ws_col = 80;
    ioctl(controller, TIOCSWINSZ, &size);

    char **args = expect_pty_strings(argv, NULL);
    char **child_env = expect_pty_child_env(env_overrides, env_unset);
    char *dir = strdup(lean_string_cstr(cwd));
    char *program = args == NULL || child_env == NULL ? NULL : expect_pty_resolve(args[0], child_env);
    if (args == NULL || child_env == NULL || dir == NULL || program == NULL) {
        bool missing = args != NULL && child_env != NULL && dir != NULL;
        char message[512];
        if (missing) snprintf(message, sizeof(message), "Not found on the PATH: %s", args[0]);
        expect_pty_free_strings(args);
        expect_pty_free_strings(child_env);
        free(dir);
        free(program);
        close(controller);
        close(child_end);
        return expect_pty_error(missing ? message : "Out of memory");
    }
    size_t program_len = strlen(program);

    /* Everything that can fail is done before the fork, so that a failure has no child to tidy */
    expect_pty_child *child = (expect_pty_child *)malloc(sizeof(expect_pty_child));
    if (child == NULL) {
        expect_pty_free_strings(args);
        expect_pty_free_strings(child_env);
        free(dir);
        free(program);
        close(controller);
        close(child_end);
        return expect_pty_error("Out of memory");
    }

    pid_t pid = fork();
    if (pid < 0) {
        int fork_err = errno;
        expect_pty_free_strings(args);
        expect_pty_free_strings(child_env);
        free(dir);
        free(program);
        free(child);
        close(controller);
        close(child_end);
        return expect_pty_errno("fork", fork_err);
    }

    if (pid == 0) {
        if (setsid() < 0) _exit(127);
#ifdef TIOCSCTTY
        if (ioctl(child_end, TIOCSCTTY, 0) < 0) _exit(127);
#endif
        if (dup2(child_end, STDIN_FILENO) < 0) _exit(127);
        if (dup2(child_end, STDOUT_FILENO) < 0) _exit(127);
        if (dup2(child_end, STDERR_FILENO) < 0) _exit(127);
        /*
        The terminal was opened to close on an exec, and a descriptor that already was one of the
        three keeps that from the open rather than from a copy, so the exec is allowed for each.
        */
        for (int fd = STDIN_FILENO; fd <= STDERR_FILENO; fd++) {
            int fd_flags = fcntl(fd, F_GETFD, 0);
            if (fd_flags >= 0) fcntl(fd, F_SETFD, fd_flags & ~FD_CLOEXEC);
        }
        if (child_end > STDERR_FILENO) close(child_end);
        /* A controlling end numbered among the three is a copy of the terminal by now */
        if (controller > STDERR_FILENO) close(controller);
        environ = child_env;
        if (chdir(dir) < 0) _exit(127);
        execv(program, args);
        /* The terminal is all that the parent can hear, so say why nothing else will arrive */
        write(STDERR_FILENO, "Could not start ", 16);
        write(STDERR_FILENO, program, program_len);
        write(STDERR_FILENO, "\n", 1);
        _exit(127);
    }

    /* The child holds its end of the terminal now */
    close(child_end);
    expect_pty_free_strings(args);
    expect_pty_free_strings(child_env);
    free(dir);
    free(program);

    child->pid = pid;
    child->fd = controller;
    child->reaped = false;
    child->code = 0;
    return lean_io_result_mk_ok(lean_alloc_external(expect_pty_child_class(), child));
}

/* Whether the terminal has output to be read, waiting up to `timeout_ms` for some to arrive. */
LEAN_EXPORT lean_obj_res expect_pty_poll(b_lean_obj_arg c, uint32_t timeout_ms,
                                         lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    if (child->fd < 0) return lean_io_result_mk_ok(lean_box(0));
    struct pollfd p;
    p.fd = child->fd;
    p.events = POLLIN;
    p.revents = 0;
    /* A negative timeout would mean "wait forever" */
    int wait_ms = timeout_ms > (uint32_t)INT_MAX ? INT_MAX : (int)timeout_ms;
    int ready;
    do {
        ready = poll(&p, 1, wait_ms);
    } while (ready < 0 && errno == EINTR);
    if (ready < 0) return expect_pty_errno("poll", errno);
    return lean_io_result_mk_ok(lean_box(ready > 0 ? 1 : 0));
}

/*
Reads up to `max` bytes. The result is empty at end of input, which a terminal reports as `EIO`
once the child has exited.
*/
LEAN_EXPORT lean_obj_res expect_pty_read(b_lean_obj_arg c, uint32_t max, lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    if (child->fd < 0) return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    uint8_t *buf = (uint8_t *)malloc(max == 0 ? 1 : max);
    if (buf == NULL) return expect_pty_error("Out of memory");
    ssize_t got;
    do {
        got = read(child->fd, buf, (size_t)max);
    } while (got < 0 && errno == EINTR);
    if (got < 0 && errno != EIO) {
        int err = errno;
        free(buf);
        return expect_pty_errno("read", err);
    }
    size_t size = got < 0 ? 0 : (size_t)got;
    lean_object *arr = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(arr), buf, size);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

/*
Sends `size` bytes to the terminal, taking up to `timeout_ms` altogether. The result is NULL once
all of them have been sent, and the reason the rest were not otherwise.

A terminal accepts only as much as its input buffer holds, and it stays full while the program has
yet to read, so the terminal is written to without blocking and waited for in between.
*/
static lean_obj_res expect_pty_send(expect_pty_child *child, const uint8_t *data, size_t size,
                                    uint32_t timeout_ms) {
    int flags = fcntl(child->fd, F_GETFL, 0);
    if (flags < 0) return expect_pty_errno("fcntl", errno);
    if (fcntl(child->fd, F_SETFL, flags | O_NONBLOCK) < 0) return expect_pty_errno("fcntl", errno);
    struct timespec started;
    clock_gettime(CLOCK_MONOTONIC, &started);
    lean_obj_res result = NULL;
    size_t written = 0;
    while (written < size) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        long waited = (now.tv_sec - started.tv_sec) * 1000 +
                      (now.tv_nsec - started.tv_nsec) / 1000000;
        long left = (long)timeout_ms - waited;
        if (left <= 0) {
            result = expect_pty_error("Timed out sending to the program");
            break;
        }
        struct pollfd p;
        p.fd = child->fd;
        p.events = POLLOUT;
        p.revents = 0;
        int ready;
        do {
            ready = poll(&p, 1, left > (long)INT_MAX ? INT_MAX : (int)left);
        } while (ready < 0 && errno == EINTR);
        if (ready < 0) {
            result = expect_pty_errno("poll", errno);
            break;
        }
        if (ready == 0) {
            result = expect_pty_error("Timed out sending to the program");
            break;
        }
        ssize_t n = write(child->fd, data + written, size - written);
        if (n < 0) {
            if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) continue;
            result = expect_pty_errno("write", errno);
            break;
        }
        written += (size_t)n;
    }
    /* The other calls read the terminal as a blocking one */
    fcntl(child->fd, F_SETFL, flags);
    return result;
}

/* Sends `bytes` to the terminal, taking up to `timeout_ms` altogether. */
LEAN_EXPORT lean_obj_res expect_pty_write(b_lean_obj_arg c, b_lean_obj_arg bytes,
                                          uint32_t timeout_ms, lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    if (child->fd < 0) return expect_pty_error("The terminal has been released");
    lean_obj_res failed = expect_pty_send(child, lean_sarray_cptr((lean_object *)bytes),
                                          lean_sarray_size((lean_object *)bytes), timeout_ms);
    return failed == NULL ? lean_io_result_mk_ok(lean_box(0)) : failed;
}

/*
Sends the character that ends the program's input, taking up to `timeout_ms`.

Echo is off for the length of the write, so that the transcript holds what the program wrote and
what was typed for it to read. A terminal that echoes this character writes it in a form of its own
choosing, and one platform's form is another's silence.
*/
LEAN_EXPORT lean_obj_res expect_pty_write_eof(b_lean_obj_arg c, uint32_t timeout_ms,
                                              lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    if (child->fd < 0) return expect_pty_error("The terminal has been released");

    struct termios settings;
    struct termios quiet;
    bool quieted = false;
    if (tcgetattr(child->fd, &settings) == 0) {
        quiet = settings;
        quiet.c_lflag &= ~(tcflag_t)ECHO;
        quieted = tcsetattr(child->fd, TCSANOW, &quiet) == 0;
    }

    const uint8_t eot = 0x04;
    lean_obj_res failed = expect_pty_send(child, &eot, 1, timeout_ms);

    if (quieted) tcsetattr(child->fd, TCSANOW, &settings);
    return failed == NULL ? lean_io_result_mk_ok(lean_box(0)) : failed;
}

/*
Waits up to `timeout_ms` for the child to terminate, giving its exit code, or `none` if it is
still running. A child killed by a signal reports 128 plus the signal number, as a shell does.
*/
LEAN_EXPORT lean_obj_res expect_pty_wait(b_lean_obj_arg c, uint32_t timeout_ms,
                                         lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    /* A signal cuts a sleep short, so the time that has passed is read from the clock. */
    struct timespec started;
    clock_gettime(CLOCK_MONOTONIC, &started);
    while (true) {
        if (child->reaped) {
            lean_object *some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, lean_box_uint32(child->code));
            return lean_io_result_mk_ok(some);
        }
        int status = 0;
        pid_t done = waitpid(child->pid, &status, WNOHANG);
        if (done < 0) {
            if (errno == EINTR) continue;
            return expect_pty_errno("waitpid", errno);
        }
        if (done > 0) {
            child->reaped = true;
            if (WIFEXITED(status)) child->code = (uint32_t)WEXITSTATUS(status);
            else if (WIFSIGNALED(status)) child->code = 128 + (uint32_t)WTERMSIG(status);
            continue;
        }
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        long waited = (now.tv_sec - started.tv_sec) * 1000 +
                      (now.tv_nsec - started.tv_nsec) / 1000000;
        if (waited >= (long)timeout_ms) return lean_io_result_mk_ok(lean_box(0));
        struct timespec pause;
        pause.tv_sec = 0;
        pause.tv_nsec = 2000000;
        nanosleep(&pause, NULL);
    }
}

LEAN_EXPORT lean_obj_res expect_pty_kill(b_lean_obj_arg c, lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    if (!child->reaped) {
        kill(child->pid, SIGKILL);
        expect_pty_reap(child);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res expect_pty_close(b_lean_obj_arg c, lean_object *world) {
    (void)world;
    expect_pty_child *child = expect_pty_unwrap(c);
    if (child->fd >= 0) {
        close(child->fd);
        child->fd = -1;
    }
    return lean_io_result_mk_ok(lean_box(0));
}
