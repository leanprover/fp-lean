(require 'project)

(defun fp-lean--wrap (start end)
  (if (use-region-p)
      (progn (save-excursion
               (goto-char (region-beginning))
               (beginning-of-line)
               (unless (looking-at-p "^$")
                 (newline))
               (insert start)
               (newline))
             (goto-char (region-end))
             (unless (looking-at-p "^$")
               (end-of-line)
               (newline))
             (insert end))
    (end-of-line)
    (unless (looking-at-p "^$")
      (newline))
    (insert start)
    (newline)
    (insert end)
    (save-excursion (newline))
    (beginning-of-line)
    (save-excursion (newline))))

(defun fp-lean-decl (name)
  "Use a book declaration called NAME."
  (interactive "MName: ")
  (fp-lean--wrap (format "book declaration {{{ %s }}}" name) "stop book declaration"))

(defun fp-lean-info (name)
  "Expect info named NAME."
  (interactive "MName: ")
  (fp-lean--wrap (format "expect info {{{ %s }}}" name) "message\n\"\"\nend expect"))

(defun fp-lean-error (name)
  "Expect error named NAME."
  (interactive "MName: ")
  (fp-lean--wrap (format "expect error {{{ %s }}}" name) "message\n\"\"\nend expect"))

(defun fp-lean-eval (name)
  "Evaluation steps named NAME."
  (interactive "MName: ")
  (fp-lean--wrap (format "evaluation steps {{{ %s }}}" name) "end evaluation steps"))

(defun fp-lean-example (name)
  "Book example named NAME."
  (interactive "MName: ")
  (fp-lean--wrap (format "bookExample {{{ %s }}}" name) "end bookExample"))

(defun fp-lean-example-type (name)
  "Book example for type named NAME."
  (interactive "MName: ")
  (fp-lean--wrap (format "bookExample type {{{ %s }}}" name) "end bookExample"))


(defun fp-lean-code ()
  (interactive)
  (fp-lean--wrap "```lean" "```"))

(defun fp-lean-output-info ()
  (interactive)
  (fp-lean--wrap "```output info" "```"))

(defun fp-lean-output-error ()
  (interactive)
  (fp-lean--wrap "```output error" "```"))


(defvar-local fp-lean--current-file nil)

(defun fp-lean--examples-dir ()
  "Get the root of the examples."
  (file-name-as-directory (concat (file-name-as-directory (project-root (project-current))) "examples")))

(defun fp-lean--mdbook-dir ()
  "Get the root of the mdbook project."
  (file-name-as-directory
   (concat (file-name-as-directory (project-root (project-current)))
           "functional-programming-lean")))

(defun fp-lean--make-file-examples-relative (filename)
  "Make a FILENAME be relative to the Lean examples for the book."
  (file-relative-name (expand-file-name filename) (fp-lean--examples-dir)))

(defun fp-lean-get-file ()
  "Get the examples filename to use, defaulting to the last one."
  (read-file-name
   (if fp-lean--current-file
       (format "File (%s): " fp-lean--current-file)
     "File: ")
   (fp-lean--examples-dir)
   fp-lean--current-file
   'confirm
   fp-lean--current-file
   (lambda (f)
     (and
      (or (file-directory-p f)
          (string= (file-name-extension f) "lean"))
      (not (string-suffix-p "~" f))))))

(defun fp-lean-name-from-file (filename)
  "Get a name of a defined thing from FILENAME."
  (completing-read "Name: "
                   (with-temp-buffer
                     (insert-file-contents filename)
                     (let ((results (list)))
                       (goto-char (point-min))
                       (while (re-search-forward "{{{\s*\\([^\s]+\\)\s*}}}" nil t nil)
                         (push (match-string 1) results))
                       results))
                   nil nil nil nil nil t))

(defun fp-lean-get-file-and-name ()
  "Read an examples file and a named anchor from it."
  (let ((file (fp-lean-get-file)))
    (list (fp-lean--make-file-examples-relative file)
          (fp-lean-name-from-file file))))

(defun fp-lean-text-decl (file name)
  "Insert a declaration from FILE called NAME."
  (interactive (fp-lean-get-file-and-name))
  (setq fp-lean--current-file file)
  (insert (format "{{#example_decl %s %s}}" file name)))

(defun fp-lean-text-example (file name)
  "Insert a declaration from FILE called NAME."
  (interactive (fp-lean-get-file-and-name))
  (setq fp-lean--current-file file)
  (insert (format "{{#example_in %s %s}}" file name))
  (insert (format "{{#example_out %s %s}}" file name)))

(defun fp-lean-text-interaction (file name)
  "Insert an example interaction from FILE called NAME."
  (interactive (fp-lean-get-file-and-name))
  (setq fp-lean--current-file file)
  (insert "```lean")
  (newline)
  (insert (format "{{#example_in %s %s}}" file name))
  (newline)
  (insert "```\n```output info")
  (newline)
  (insert (format "{{#example_out %s %s}}" file name))
  (newline)
  (insert "```"))

(defun fp-lean-text-error (file name)
  "Insert an error example from FILE called NAME."
  (interactive (fp-lean-get-file-and-name))
  (setq fp-lean--current-file file)
  (insert "```lean")
  (newline)
  (insert (format "{{#example_in %s %s}}" file name))
  (newline)
  (insert "```\n```output error")
  (newline)
  (insert (format "{{#example_out %s %s}}" file name))
  (newline)
  (insert "```"))

(defvar fp-lean-process nil
  "Process under which the book is being served (to avoid duplication).")

(defun fp-lean-serve-book ()
  "Start or restart the server."
  (interactive)
  (let ((buffer (if (processp fp-lean-process)
                    (process-buffer fp-lean-process)
                  "*FP-Lean-Server*")))
    (when fp-lean-process
      (when (processp fp-lean-process)
        (let ((buf (process-buffer fp-lean-process)))
          (when (and buf (buffer-live-p buf))
            (with-current-buffer buf
              (goto-char (point-max))
              (insert "\n")
              (insert (format-time-string "%Y-%m-%d %H:%M:%S - Process killed" (current-time))))))
        (kill-process fp-lean-process))
      (setq fp-lean-process nil))
    (let* ((default-directory (fp-lean--mdbook-dir)))
      (setq fp-lean-process (start-process "Lean book server" buffer "mdbook" "serve"))
      (message "Lean book server running in buffer %s" (buffer-name (process-buffer fp-lean-process))))))

(defun fp-lean-ensure-server ()
   "Ensure a server is running."
  (interactive)
  (unless (and fp-lean-process
               (processp fp-lean-process)
               (process-live-p fp-lean-process))
    (fp-lean-serve-book)))

(defun fp-lean-browse-book ()
  "Open the book."
  (interactive)
  (fp-lean-ensure-server)
  (browse-url "localhost:3000"))
