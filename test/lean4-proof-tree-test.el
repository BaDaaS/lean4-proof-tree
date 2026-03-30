;;; lean4-proof-tree-test.el --- Tests for lean4-proof-tree  -*- lexical-binding: t; -*-

;; Licensed under the Apache License, Version 2.0.

;;; Code:

(require 'ert)
(require 'lean4-proof-tree)

;;; Test helpers

(defmacro lean4-proof-tree-test--with-buffer (content &rest body)
  "Insert CONTENT into a temp buffer and execute BODY."
  (declare (indent 1))
  `(with-temp-buffer
     (insert ,content)
     (goto-char (point-max))
     ,@body))

;;; Tests for lean4-proof-tree--find-by-block

(ert-deftest lean4-proof-tree-find-by-block-simple ()
  "Find a simple by block."
  (lean4-proof-tree-test--with-buffer
      "theorem foo : True := by\n  trivial\n"
    (goto-char (point-min))
    (forward-line 1)
    (let ((block (lean4-proof-tree--find-by-block)))
      (should block)
      (should (= (car block) 1))
      (should (= (cdr block) 2)))))

(ert-deftest lean4-proof-tree-find-by-block-multiline ()
  "Find a multi-line by block."
  (lean4-proof-tree-test--with-buffer
      (concat "theorem foo : P /\\ Q := by\n"
              "  constructor\n"
              "  exact h.1\n"
              "  exact h.2\n")
    (goto-char (point-min))
    (forward-line 2)
    (let ((block (lean4-proof-tree--find-by-block)))
      (should block)
      (should (= (car block) 1))
      (should (= (cdr block) 4)))))

(ert-deftest lean4-proof-tree-find-by-block-multiline-signature ()
  "Find by block when theorem signature wraps across lines."
  (lean4-proof-tree-test--with-buffer
      (concat "theorem trans_tactic (P Q R : Prop) :\n"
              "    (P -> Q) -> (Q -> R) -> P -> R := by\n"
              "  intro hpq hqr hp\n"
              "  apply hqr\n"
              "  apply hpq\n"
              "  exact hp\n")
    (goto-char (point-min))
    (forward-line 4)
    (let ((block (lean4-proof-tree--find-by-block)))
      (should block)
      (should (= (car block) 2))
      (should (= (cdr block) 6)))))

(ert-deftest lean4-proof-tree-find-by-block-outside ()
  "Return nil when point is outside any by block."
  (lean4-proof-tree-test--with-buffer
      (concat "def foo := 42\n"
              "\n"
              "theorem bar : True := by\n"
              "  trivial\n")
    (goto-char (point-min))
    (should-not (lean4-proof-tree--find-by-block))))

(ert-deftest lean4-proof-tree-find-by-block-no-by ()
  "Return nil when there is no by block."
  (lean4-proof-tree-test--with-buffer
      "def foo := 42\n"
    (should-not (lean4-proof-tree--find-by-block))))

;;; Tests for lean4-proof-tree--extract-tactics

(ert-deftest lean4-proof-tree-extract-tactics-basic ()
  "Extract tactics from a simple block."
  (lean4-proof-tree-test--with-buffer
      (concat "theorem foo := by\n"
              "  intro h\n"
              "  exact h\n")
    (let ((tactics (lean4-proof-tree--extract-tactics 1 3)))
      (should (= (length tactics) 2))
      (should (string= (cdar tactics) "intro h"))
      (should (string= (cdadr tactics) "exact h")))))

(ert-deftest lean4-proof-tree-extract-tactics-skips-blanks ()
  "Blank lines are skipped."
  (lean4-proof-tree-test--with-buffer
      (concat "theorem foo := by\n"
              "  intro h\n"
              "\n"
              "  exact h\n")
    (let ((tactics (lean4-proof-tree--extract-tactics 1 4)))
      (should (= (length tactics) 2)))))

(ert-deftest lean4-proof-tree-extract-tactics-skips-comments ()
  "Comment lines are skipped."
  (lean4-proof-tree-test--with-buffer
      (concat "theorem foo := by\n"
              "  -- introduce hypothesis\n"
              "  intro h\n"
              "  exact h\n")
    (let ((tactics (lean4-proof-tree--extract-tactics 1 4)))
      (should (= (length tactics) 2))
      (should (string= (cdar tactics) "intro h")))))

(ert-deftest lean4-proof-tree-extract-tactics-skips-by ()
  "The `by' keyword itself is skipped."
  (lean4-proof-tree-test--with-buffer
      (concat "theorem foo := by\n"
              "  trivial\n")
    (let ((tactics (lean4-proof-tree--extract-tactics 1 2)))
      (should (= (length tactics) 1))
      (should (string= (cdar tactics) "trivial")))))

;;; Tests for lean4-proof-tree--render-rpc-tree

(defun lean4-proof-tree-test--make-node
    (tactic goals-after children &optional range)
  "Build a hash table mimicking an RPC tree node."
  (let ((ht (make-hash-table :test 'equal)))
    (puthash "tactic" tactic ht)
    (puthash "goalsAfter" goals-after ht)
    (puthash "children" children ht)
    (puthash "goalsBefore" [] ht)
    (puthash "range" range ht)
    ht))

(defun lean4-proof-tree-test--make-goal (target)
  "Build a hash table mimicking an RPC goal."
  (let ((ht (make-hash-table :test 'equal)))
    (puthash "id" "m1" ht)
    (puthash "hypotheses" [] ht)
    (puthash "target" target ht)
    ht))

(ert-deftest lean4-proof-tree-render-rpc-nil ()
  "Render nil root shows help text."
  (with-temp-buffer
    (lean4-proof-tree--render-rpc nil 1)
    (should (string-match-p "No proof tree"
                            (buffer-string)))))

(ert-deftest lean4-proof-tree-render-rpc-closed-leaf ()
  "Render a closed leaf node shows [done]."
  (with-temp-buffer
    (let ((node (lean4-proof-tree-test--make-node
                 "exact hp" [] [])))
      (lean4-proof-tree--render-rpc node 1)
      (should (string-match-p "exact hp" (buffer-string)))
      (should (string-match-p "\\[done\\]" (buffer-string))))))

(ert-deftest lean4-proof-tree-render-rpc-open-leaf ()
  "Render an open leaf shows goals."
  (with-temp-buffer
    (let* ((goal (lean4-proof-tree-test--make-goal "Q"))
           (node (lean4-proof-tree-test--make-node
                  "intro h" (vector goal) [])))
      (lean4-proof-tree--render-rpc node 1)
      (should (string-match-p "intro h" (buffer-string)))
      (should (string-match-p "Q" (buffer-string))))))

(ert-deftest lean4-proof-tree-render-rpc-tree-with-children ()
  "Render a tree with children draws branches."
  (with-temp-buffer
    (let* ((child1 (lean4-proof-tree-test--make-node
                    "exact h.2" [] []))
           (child2 (lean4-proof-tree-test--make-node
                    "exact h.1" [] []))
           (root (lean4-proof-tree-test--make-node
                  "constructor" []
                  (vector child1 child2))))
      (lean4-proof-tree--render-rpc root 1)
      (let ((text (buffer-string)))
        (should (string-match-p "constructor" text))
        (should (string-match-p "exact h.2" text))
        (should (string-match-p "exact h.1" text))
        (should (string-match-p "\\[done\\]" text))))))

(ert-deftest lean4-proof-tree-render-rpc-nested ()
  "Render a nested tree preserves structure."
  (with-temp-buffer
    (let* ((leaf (lean4-proof-tree-test--make-node
                  "exact hp" [] []))
           (mid (lean4-proof-tree-test--make-node
                 "apply hqr" []
                 (vector leaf)))
           (root (lean4-proof-tree-test--make-node
                  "intro h" []
                  (vector mid))))
      (lean4-proof-tree--render-rpc root 1)
      (let ((text (buffer-string)))
        (should (string-match-p "intro h" text))
        (should (string-match-p "apply hqr" text))
        (should (string-match-p "exact hp" text))))))

;;; Tests for JSON accessor

(ert-deftest lean4-proof-tree-json-get-hash ()
  "Access hash table keys."
  (let ((ht (make-hash-table :test 'equal)))
    (puthash "foo" 42 ht)
    (should (= (lean4-proof-tree--json-get ht "foo") 42))))

(ert-deftest lean4-proof-tree-json-get-plist ()
  "Access plist keys."
  (should (= (lean4-proof-tree--json-get '(:foo 42) "foo") 42)))

(provide 'lean4-proof-tree-test)
;;; lean4-proof-tree-test.el ends here
