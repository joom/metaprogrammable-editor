;;; -*- lexical-binding: t -*-

(defun run-action (a)
  (pcase a
    (`(Editor\.ret ,x)          x)
    (`(Editor\.message ,s)      (message s) "tt")
    (`(Editor\.message_box ,s)  (message-box s) "tt")
    (`(Editor\.insert_char ,c)  (insert c) "tt")
    ('Editor\.get_char          (prin1-to-string (string (following-char))))
    ('Editor\.remove_char       (delete-char 1) "tt")
    ('Editor\.move_right        (right-char) "tt")
    ('Editor\.move_left         (left-char) "tt")
    ('Editor\.move_up           (previous-line) "tt")
    ('Editor\.move_down         (next-line) "tt")
    ('Editor\.move_beginning    (move-beginning-of-line) "tt")
    ('Editor\.move_end          (move-end) "tt")
    (l                          (message "Unrecognized action") nil)
  ))

(defun parse-response (s)
  (let*
    (
     (untail (substring s 0 (string-match-p (regexp-quote ": Editor.edit unit") s)))
    )
    (pcase (read-from-string untail)
      (`(= . ,m)
       (let* ((uneq (substring untail (+ m 1)))
              (parenned (if (not (string-match-p (regexp-quote "(fun") untail))
                            (concat "(" uneq ")")
                          uneq))
              (paren-necessary (if (not (string-match-p (regexp-quote "Editor.bind") uneq))
                                   parenned uneq)))
          (pcase (read-from-string paren-necessary)
            (`(Editor\.bind . ,n)
              (pcase (read-from-string (substring untail (+ m n 1)))
                (`(,act . ,p) (run-edit (concat (substring untail (+ m n p 1)) " " (run-action act))))
              )
            )
            (`(,act . ,m) (run-action act))
            (l (message "Error: Expecting either a bind or an action."))
          )
       )
      )
      (l (message "Error: Expecting = in the beginning of the output."))
    )
  )
)


(defun run-edit (s)
  (let*
    ((res (proof-shell-invisible-cmd-get-result
            (concat "Eval cbn in (" s ")."))))
    (parse-response res)))

(defun run (s) (run-edit (concat "(Editor.right_assoc (" s "))")))
