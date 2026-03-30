;;; lean4-proof-tree-test.el --- Tests for lean4-proof-tree  -*- lexical-binding: t; -*-

;; Licensed under the Apache License, Version 2.0.

;;; Code:

(require 'ert)
(require 'lean4-proof-tree)

;;; Test helpers

(defmacro lean4-proof-tree-test--with-buffer (content &rest body)
  "Insert CONTENT into a temp buffer and execute BODY.
Point is placed at the end of CONTENT."
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
    (forward-line 1)  ;; on `trivial`
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
    (forward-line 2)  ;; on `exact h.1`
    (let ((block (lean4-proof-tree--find-by-block)))
      (should block)
      (should (= (car block) 1))
      (should (= (cdr block) 4)))))

(ert-deftest lean4-proof-tree-find-by-block-outside ()
  "Return nil when point is outside any by block."
  (lean4-proof-tree-test--with-buffer
      (concat "def foo := 42\n"
              "\n"
              "theorem bar : True := by\n"
              "  trivial\n")
    (goto-char (point-min))  ;; on `def foo`
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

;;; Tests for lean4-proof-tree--render-goal-short

(ert-deftest lean4-proof-tree-render-goal-with-turnstile ()
  "Extract target after turnstile."
  (should (string= (lean4-proof-tree--render-goal-short
                     "h : Nat |- True")
                    "True")))

(ert-deftest lean4-proof-tree-render-goal-without-turnstile ()
  "Return the goal as-is if no turnstile."
  (should (string= (lean4-proof-tree--render-goal-short "True")
                    "True")))

(ert-deftest lean4-proof-tree-render-goal-trims-whitespace ()
  "Trim whitespace around the target."
  (should (string= (lean4-proof-tree--render-goal-short
                     "h : Nat |-  True  ")
                    "True")))

;;; Tests for lean4-proof-tree--render

(ert-deftest lean4-proof-tree-render-empty ()
  "Render nil nodes shows placeholder text."
  (with-temp-buffer
    (lean4-proof-tree--render nil 1)
    (should (string-match-p "No tactic block"
                            (buffer-string)))))

(ert-deftest lean4-proof-tree-render-closed-node ()
  "Render a closed node shows [done]."
  (with-temp-buffer
    (let ((node (make-lean4-proof-tree-node
                 :tactic "trivial"
                 :goals-after nil
                 :line 2
                 :closed-p t)))
      (lean4-proof-tree--render (list node) 1)
      (should (string-match-p "trivial"
                              (buffer-string)))
      (should (string-match-p "\\[done\\]"
                              (buffer-string))))))

(ert-deftest lean4-proof-tree-render-open-node-shows-goals ()
  "Render an open node shows remaining goals."
  (with-temp-buffer
    (let ((node (make-lean4-proof-tree-node
                 :tactic "constructor"
                 :goals-after '("h : P |- Q" "h : P |- R")
                 :line 2
                 :closed-p nil)))
      (lean4-proof-tree--render (list node) 1)
      (should (string-match-p "constructor"
                              (buffer-string)))
      (should (string-match-p "|- Q"
                              (buffer-string)))
      (should (string-match-p "|- R"
                              (buffer-string))))))

;;; Tests for node struct

(ert-deftest lean4-proof-tree-node-accessors ()
  "Node struct accessors work."
  (let ((node (make-lean4-proof-tree-node
               :tactic "intro h"
               :goals-after '("goal1")
               :line 5
               :closed-p nil)))
    (should (string= (lean4-proof-tree-node-tactic node) "intro h"))
    (should (equal (lean4-proof-tree-node-goals-after node)
                   '("goal1")))
    (should (= (lean4-proof-tree-node-line node) 5))
    (should-not (lean4-proof-tree-node-closed-p node))))

(provide 'lean4-proof-tree-test)
;;; lean4-proof-tree-test.el ends here
