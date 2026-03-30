;;; lean4-proof-tree.el --- Proof tree visualization for Lean 4  -*- lexical-binding: t; -*-

;; Copyright (c) 2026 BaDaaS. All rights reserved.

;; Author: BaDaaS contributors
;; Maintainer: Danny Willems
;; Keywords: languages, lean, proof, tree
;; Package-Requires: ((emacs "29.1") (lean4-mode "1.1.0") (dash "2.18.0"))
;; URL: https://github.com/BaDaaS/lean4-proof-tree
;; SPDX-License-Identifier: Apache-2.0
;; Version: 0.1.0

;; This file is not part of GNU Emacs.

;; Licensed under the Apache License, Version 2.0 (the "License"); you
;; may not use this file except in compliance with the License.  You
;; may obtain a copy of the License at
;;
;;     http://www.apache.org/licenses/LICENSE-2.0

;;; Commentary:

;; Visualize Lean 4 tactic proofs as derivation trees.
;;
;; When editing a tactic proof (a `by' block), this package queries
;; the Lean LSP server for the goal state at each tactic step and
;; renders a tree showing how goals are created, split, and closed.
;;
;; Usage:
;;   M-x lean4-proof-tree-show   (or C-c C-t in lean4-mode)

;;; Code:

(require 'cl-lib)
(require 'dash)

;; Forward declarations
(declare-function lsp-request "ext:lsp-mode")
(declare-function lsp--text-document-identifier "ext:lsp-mode")
(defvar lean4-mode-map)

;;; Customization

(defgroup lean4-proof-tree nil
  "Proof tree visualization for Lean 4."
  :group 'lean4
  :prefix "lean4-proof-tree-")

(defcustom lean4-proof-tree-buffer-name "*Lean Proof Tree*"
  "Name of the proof tree buffer."
  :type 'string
  :group 'lean4-proof-tree)

;;; Faces

(defface lean4-proof-tree-tactic-face
  '((t :inherit font-lock-keyword-face :weight bold))
  "Face for tactic names."
  :group 'lean4-proof-tree)

(defface lean4-proof-tree-goal-face
  '((t :inherit font-lock-type-face))
  "Face for goal types."
  :group 'lean4-proof-tree)

(defface lean4-proof-tree-closed-face
  '((t :inherit success :weight bold))
  "Face for closed (proved) goals."
  :group 'lean4-proof-tree)

(defface lean4-proof-tree-open-face
  '((t :inherit warning))
  "Face for open (unproved) goals."
  :group 'lean4-proof-tree)

(defface lean4-proof-tree-cursor-face
  '((((class color) (background light))
     :background "lightyellow")
    (((class color) (background dark))
     :background "#3a3a00"))
  "Face for the tactic at the current cursor position."
  :group 'lean4-proof-tree)

;;; Data structures

(cl-defstruct lean4-proof-tree-node
  "A node in the proof tree."
  tactic        ;; string: the tactic text
  goals-after   ;; list of goal strings after this tactic
  line          ;; integer: source line number
  closed-p)     ;; boolean: all goals resolved

;;; Tactic block parsing

(defun lean4-proof-tree--find-by-block ()
  "Find the `by' block surrounding point.
Return (START-LINE . END-LINE) or nil."
  (save-excursion
    (let ((orig (line-number-at-pos))
          (start nil)
          (end nil))
      (when (re-search-backward
             (rx word-start "by" word-end) nil t)
        (setq start (line-number-at-pos))
        (let ((by-col (current-indentation)))
          (forward-line 1)
          (while (and (not (eobp))
                      (or (looking-at-p "^\\s-*$")
                          (> (current-indentation) by-col)))
            (forward-line 1))
          (setq end (1- (line-number-at-pos))))
        (when (and (<= start orig) (>= end orig))
          (cons start end))))))

(defun lean4-proof-tree--extract-tactics (beg end)
  "Extract tactic lines between BEG and END.
Return a list of (LINE . TEXT) pairs, skipping blanks,
comments, and the `by' keyword."
  (save-excursion
    (goto-char (point-min))
    (forward-line (1- beg))
    (let ((result nil))
      (dotimes (_ (1+ (- end beg)))
        (let ((ln (line-number-at-pos))
              (text (string-trim
                     (buffer-substring-no-properties
                      (line-beginning-position)
                      (line-end-position)))))
          (unless (or (string-empty-p text)
                      (string= text "by")
                      (string-suffix-p ":= by" text)
                      (string-suffix-p "=> by" text)
                      (string-prefix-p "--" text))
            (push (cons ln text) result)))
        (forward-line 1))
      (nreverse result))))

;;; LSP goal querying

(defun lean4-proof-tree--query-goals (line)
  "Query goals at the end of LINE (1-indexed) synchronously.
Return a list of goal strings, or nil."
  (require 'lsp-mode)
  (condition-case nil
      (let* ((col (save-excursion
                    (goto-char (point-min))
                    (forward-line (1- line))
                    (end-of-line)
                    (current-column)))
             (params
              (list :textDocument (lsp--text-document-identifier)
                    :position (list :line (1- line)
                                    :character col)))
             (result (lsp-request "$/lean/plainGoal" params)))
        (when result
          (append (gethash "goals" result) nil)))
    (error nil)))

;;; Tree building

(defun lean4-proof-tree--build (tactics)
  "Build proof tree nodes from TACTICS.
TACTICS is a list of (LINE . TEXT) pairs."
  (let ((nodes nil))
    (dolist (tac tactics)
      (let* ((line (car tac))
             (text (cdr tac))
             (goals (lean4-proof-tree--query-goals line)))
        (push (make-lean4-proof-tree-node
               :tactic text
               :goals-after goals
               :line line
               :closed-p (null goals))
              nodes)))
    (nreverse nodes)))

;;; Rendering

(defun lean4-proof-tree--render-goal-short (goal)
  "Extract the target type from GOAL, after the turnstile."
  (if (string-match "|-\\s-*\\(.+\\)" goal)
      (string-trim (match-string 1 goal))
    (string-trim goal)))

(defun lean4-proof-tree--render (nodes cursor-line)
  "Render NODES into the current buffer.
Highlight the node at CURSOR-LINE."
  (let ((inhibit-read-only t))
    (erase-buffer)
    (if (null nodes)
        (insert "No tactic block found at point.\n")
      (dolist (node nodes)
        (let* ((tactic (lean4-proof-tree-node-tactic node))
               (goals (lean4-proof-tree-node-goals-after node))
               (closed (lean4-proof-tree-node-closed-p node))
               (at-cursor (= (lean4-proof-tree-node-line node)
                             cursor-line))
               (status (if closed " [done]" ""))
               (line-beg (point)))
          (insert (propertize tactic
                              'face 'lean4-proof-tree-tactic-face)
                  (propertize status
                              'face (if closed
                                        'lean4-proof-tree-closed-face
                                      'lean4-proof-tree-open-face))
                  "\n")
          (when at-cursor
            (put-text-property line-beg (point)
                               'face 'lean4-proof-tree-cursor-face))
          (when (and goals (not closed))
            (dolist (g goals)
              (insert "  "
                      (propertize
                       (concat "|- "
                               (lean4-proof-tree--render-goal-short g))
                       'face 'lean4-proof-tree-goal-face)
                      "\n"))))))
    (goto-char (point-min))))

;;; Mode

(define-derived-mode lean4-proof-tree-mode special-mode
  "Proof-Tree"
  "Major mode for displaying Lean 4 proof trees."
  :group 'lean4-proof-tree
  (setq-local revert-buffer-function
              #'lean4-proof-tree--revert)
  (setq truncate-lines t))

(defvar-local lean4-proof-tree--source-buffer nil
  "Source buffer this proof tree tracks.")

(defvar-local lean4-proof-tree--update-timer nil
  "Debounce timer for proof tree updates.")

(defun lean4-proof-tree--revert (&rest _)
  "Refresh the proof tree."
  (lean4-proof-tree--update))

;;; Update

(defun lean4-proof-tree--update ()
  "Rebuild and render the proof tree."
  (when-let ((source lean4-proof-tree--source-buffer))
    (when (buffer-live-p source)
      (with-current-buffer source
        (let* ((block (lean4-proof-tree--find-by-block))
               (cursor-line (line-number-at-pos)))
          (if block
              (let* ((tactics (lean4-proof-tree--extract-tactics
                               (car block) (cdr block)))
                     (nodes (lean4-proof-tree--build tactics)))
                (with-current-buffer
                    lean4-proof-tree-buffer-name
                  (lean4-proof-tree--render nodes cursor-line)))
            (with-current-buffer lean4-proof-tree-buffer-name
              (lean4-proof-tree--render nil cursor-line))))))))

(defun lean4-proof-tree--update-debounced ()
  "Debounced proof tree update."
  (when (and (eq major-mode 'lean4-mode)
             (get-buffer-window lean4-proof-tree-buffer-name t))
    (when lean4-proof-tree--update-timer
      (cancel-timer lean4-proof-tree--update-timer))
    (let ((buf (current-buffer)))
      (setq lean4-proof-tree--update-timer
            (run-with-idle-timer
             0.5 nil
             (lambda ()
               (when (buffer-live-p buf)
                 (with-current-buffer buf
                   (lean4-proof-tree--update)))))))))

;;; Public API

;;;###autoload
(defun lean4-proof-tree-show ()
  "Show the proof tree for the tactic block at point."
  (interactive)
  (unless (eq major-mode 'lean4-mode)
    (user-error "Not in a lean4-mode buffer"))
  (let ((source (current-buffer))
        (buf (get-buffer-create lean4-proof-tree-buffer-name)))
    (with-current-buffer buf
      (lean4-proof-tree-mode)
      (setq lean4-proof-tree--source-buffer source))
    (display-buffer-in-side-window
     buf '((side . right) (window-width . 0.35)))
    (add-hook 'post-command-hook
              #'lean4-proof-tree--update-debounced nil t)
    (lean4-proof-tree--update)))

;;;###autoload
(defun lean4-proof-tree-hide ()
  "Hide the proof tree window."
  (interactive)
  (when-let ((win (get-buffer-window
                   lean4-proof-tree-buffer-name t)))
    (quit-window nil win))
  (remove-hook 'post-command-hook
               #'lean4-proof-tree--update-debounced t))

;;;###autoload
(defun lean4-proof-tree-toggle ()
  "Toggle the proof tree display."
  (interactive)
  (if (get-buffer-window lean4-proof-tree-buffer-name t)
      (lean4-proof-tree-hide)
    (lean4-proof-tree-show)))

;; Keybinding
(with-eval-after-load 'lean4-mode
  (define-key lean4-mode-map (kbd "C-c C-t")
              #'lean4-proof-tree-toggle))

(provide 'lean4-proof-tree)
;;; lean4-proof-tree.el ends here
