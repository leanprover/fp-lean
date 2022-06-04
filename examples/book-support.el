(defun fp-lean--wrap (start end)
  (if (use-region-p)
      (progn (save-excursion
               (goto-char (region-beginning))
               (beginning-of-line)
               (newline)
               (insert start)
               (newline))
             (goto-char (region-end))
             (end-of-line)
             (newline)
             (insert end))
    (beginning-of-line)
    (newline)
    (insert start)
    (newline)
    (insert end)))

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

(defun fp-lean-code ()
  (interactive)
  (insert "```Lean")
  (newline)
  (save-excursion
    (newline)
    (insert "```")))

(defvar-local fp-lean--current-file nil)

(defun fp-lean-get-file ()
  (read-string (if fp-lean--current-file (format "File (%s): " fp-lean--current-file) "File: ") nil nil fp-lean--current-file))

(defun fp-lean-text-decl (file name)
  "Insert a declaration from FILE called NAME."
  (interactive
   (list (fp-lean-get-file) (read-string "Name: ")))
  (setq fp-lean--current-file file)
  (insert (format "{{#example_decl %s %s}}" file name)))

(defun fp-lean-text-example (file name)
  "Insert a declaration from FILE called NAME."
  (interactive
   (list (fp-lean-get-file) (read-string "Name: ")))
  (setq fp-lean--current-file file)
  (insert (format "{{#example_in %s %s}}" file name))
  (insert (format "{{#example_out %s %s}}" file name)))

(defun fp-lean-text-interaction (file name)
  "Insert an example interaction from FILE called NAME."
  (interactive
   (list (fp-lean-get-file) (read-string "Name: ")))
  (setq fp-lean--current-file file)
  (insert "```Lean")
  (newline)
  (insert (format "{{#example_in %s %s}}" file name))
  (newline)
  (insert "```\n```Lean info")
  (newline)
  (insert (format "{{#example_out %s %s}}" file name))
  (newline)
  (insert "```"))

(defun fp-lean-text-error (file name)
  "Insert an error example from FILE called NAME."
  (interactive
   (list (fp-lean-get-file) (read-string "Name: ")))
  (setq fp-lean--current-file file)
  (insert "```Lean")
  (newline)
  (insert (format "{{#example_in %s %s}}" file name))
  (newline)
  (insert "```\n```Lean error")
  (newline)
  (insert (format "{{#example_out %s %s}}" file name))
  (newline)
  (insert "```"))
