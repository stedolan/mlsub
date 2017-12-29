(defconst polytope-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; " is a string delimiter too
    (modify-syntax-entry ?\" "\"" table)

    (modify-syntax-entry ?\' "_" table)

    ;; / is punctuation, but // is a comment starter
    (modify-syntax-entry ?/ ". 12" table)
    ;; \n is a comment ender
    (modify-syntax-entry ?\n ">" table)
    table))

(defconst polytope-font-lock-keywords
  `(
    (,(rx symbol-start
         (or "def" "let" "if" "else" "match" "type" "rec" "case") symbol-end)
     0 font-lock-keyword-face)
    (,(rx symbol-start
         (or "true" "false") symbol-end)
     0 font-lock-constant-face)
    (,(rx symbol-start
          "'" (any "a-zA-Z_") (zero-or-more (any "a-zA-Z_0-9")) symbol-end)
     0 font-lock-constant-face)
    (,(rx symbol-start "def" symbol-end (one-or-more space)
          (group symbol-start (any "a-zA-Z_") (zero-or-more (any "a-zA-Z_0-9")) symbol-end))
     1 font-lock-function-name-face)
    (,(rx symbol-start "let" symbol-end (one-or-more space)
          (group symbol-start (any "a-zA-Z_") (zero-or-more (any "a-zA-Z_0-9")) symbol-end))
     1 font-lock-variable-name-face)
    ))

(define-derived-mode polytope-mode prog-mode "Polytope" ()
  (setq font-lock-defaults '((polytope-font-lock-keywords) nil nil))
  (setq syntax-table polytope-mode-syntax-table)
  (setq comment-start "// ")
  (setq comment-end "")
  )
