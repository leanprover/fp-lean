import json
import re
from pathlib import Path
import os
import shlex
import subprocess
import sys

def eprint(val):
    print(val, file=sys.stderr)

command_re = re.compile(r'\{\{#command\s+\{(?P<dir>[^}]+)\}\s*\{(?P<container>[^}]+)\}\s*\{(?P<command>[^}]+)\}\s*(\{(?P<show>[^}]+)\}\s*)?\}\}')
command_out_re = re.compile(r'\{\{#command_out\s+\{(?P<container>[^}]+)\}\s*\{(?P<command>[^}]+)\}\s*\}\}')


class ContainerContext:

    def __init__(self, project_root):
        self.project_root = project_root
        subprocess.run(["podman", "build", "-f", "cmdline", "-t", "leanbook"], cwd = f"{project_root}{os.path.sep}examples", capture_output=True)
        self.containers = set()
        self.outputs = {}

    def __enter__(self):
        subprocess.run(["podman", "build", "-f", "cmdline", "-t", "leanbook"], cwd = f"{self.project_root}{os.path.sep}examples", capture_output=True, check=True)
        return self

    def __exit__(self, _type, _value, _traceback):
        # delete all created containers
        for i in self.containers:
            subprocess.run(["podman", "stop", i], capture_output=True)
            subprocess.run(["podman", "rm", i], capture_output=True)

    def ensure_container(self, name):
        if name not in self.containers:
            podman_cmd = f"podman run -d -it --name {name} leanbook:latest"
            try:
                subprocess.run(["podman", "run", "-d", "-it", "--name", name, "leanbook:latest"], check=True, capture_output=True)
            except subprocess.CalledProcessError as e:
                eprint("Output:")
                eprint(e.output)
                eprint("Stderr:")
                eprint(e.stderr)

                raise e
            self.containers.add(name)

    def rewrite_command(self, project_root):
        def rewrite(found):
            container = found.group('container')
            self.ensure_container(container)
            directory = found.group('dir')
            command = found.group('command')
            show = found.group('show')
            try:
                val = subprocess.run(["podman", "exec", "-w", f"/lean-book/{directory}", container] + shlex.split(command), check=True, capture_output=True)
            except subprocess.CalledProcessError as e:
                eprint("Output:")
                eprint(e.output)
                eprint("Stderr:")
                eprint(e.stderr)
                raise e

            if container not in self.outputs: self.outputs[container] = {}
            self.outputs[container][command] = val.stdout.decode('utf-8')
            if show is None:
                return command
            else:
                return show

        return rewrite

    def rewrite_command_out(self, project_root):
        def rewrite(found):
            container = found.group('container')
            command = found.group('command')
            return self.outputs[container][command]
        return rewrite

    def run_examples(self, context, book):
        project_root = Path(context['root']).parent
        def test_chapters(chapters):
            for ch in chapters:
                ch['Chapter']['content'] = command_re.sub(self.rewrite_command(project_root), ch['Chapter']['content'])
                ch['Chapter']['content'] = command_out_re.sub(self.rewrite_command_out(project_root), ch['Chapter']['content'])
                test_chapters(ch['Chapter']['sub_items'])

        test_chapters(book['sections'])
        return book

def main():
    if len(sys.argv) > 1:
        if sys.argv[1] == "supports":
            sys.exit(0)
    context, book_contents = json.load(sys.stdin)
    with ContainerContext(Path(context['root']).parent) as ctx:
        print(json.dumps(ctx.run_examples(context, book_contents)))

if __name__ == '__main__':
    main()
