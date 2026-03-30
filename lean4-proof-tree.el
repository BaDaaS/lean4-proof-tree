;;; lean4-proof-tree.el --- Proof tree visualization for Lean 4  -*- lexical-binding: t; -*-

;; Copyright (c) 2026 BaDaaS. All rights reserved.

;; Author: BaDaaS contributors
;; Maintainer: Danny Willems
;; Keywords: languages, lean, proof, tree
;; Package-Requires: ((emacs "29.1") (lean4-mode "1.1.0") (dash "2.18.0"))
;; URL: https://github.com/BaDaaS/lean4-proof-tree
;; SPDX-License-Identifier: Apache-2.0
;; Version: 0.3.0

;; This file is not part of GNU Emacs.

;; Licensed under the Apache License, Version 2.0 (the "License"); you
;; may not use this file except in compliance with the License.  You
;; may obtain a copy of the License at
;;
;;     http://www.apache.org/licenses/LICENSE-2.0

;;; Commentary:

;; Visualize Lean 4 tactic proofs as derivation trees.
;;
;; This package uses a server-side Lean 4 library that traverses
;; the InfoTree to build real proof trees with parent-child
;; relationships between tactics.
;;
;; Setup:
;;   1. Add the ProofTree Lake dependency to your Lean project
;;   2. Import ProofTree in your Lean files
;;   3. Use C-c C-t to toggle the proof tree panel
;;
;; The tree is built from the Lean elaborator's InfoTree, giving
;; correct parent-child edges even for complex tactics.

;;; Code:

(require 'cl-lib)
(require 'dash)

;; Forward declarations
(declare-function lsp-request "ext:lsp-mode")
(declare-function lsp-request-async "ext:lsp-mode")
(declare-function lsp--text-document-identifier "ext:lsp-mode")
(declare-function lsp--buffer-uri "ext:lsp-mode")
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

(defcustom lean4-proof-tree-use-rpc t
  "Use the server-side RPC endpoint for proof trees.
When non-nil, calls ProofTree.getProofTree via RPC (requires
the ProofTree Lake dependency). When nil, falls back to
per-line plainGoal queries."
  :type 'boolean
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

(defface lean4-proof-tree-branch-face
  '((t :inherit shadow))
  "Face for tree branch drawing characters."
  :group 'lean4-proof-tree)

;;; RPC session management

(defvar-local lean4-proof-tree--rpc-session nil
  "RPC session ID for the current buffer.")

(defun lean4-proof-tree--rpc-connect ()
  "Connect to the Lean RPC server for the current buffer.
Return the session ID string."
  (require 'lsp-mode)
  (or lean4-proof-tree--rpc-session
      (let* ((params (list :uri (lsp--buffer-uri)))
             (result (lsp-request "$/lean/rpc/connect" params)))
        (setq lean4-proof-tree--rpc-session
              (gethash "sessionId" result)))))

(defun lean4-proof-tree--rpc-call (method params)
  "Call RPC METHOD with PARAMS via $/lean/rpc/call.
Return the result hash table."
  (require 'lsp-mode)
  (let* ((session (lean4-proof-tree--rpc-connect))
         (rpc-params (list :sessionId session
                           :method method
                           :params params)))
    (condition-case err
        (lsp-request "$/lean/rpc/call" rpc-params)
      (error
       ;; Session might have expired, reconnect and retry once
       (setq lean4-proof-tree--rpc-session nil)
       (let* ((session2 (lean4-proof-tree--rpc-connect))
              (rpc-params2 (list :sessionId session2
                                 :method method
                                 :params params)))
         (lsp-request "$/lean/rpc/call" rpc-params2))))))

;;; RPC-based tree querying

(defun lean4-proof-tree--query-rpc (line col)
  "Query the proof tree at LINE (1-indexed) and COL via RPC.
Return the parsed tree as a nested alist, or nil."
  (condition-case nil
      (let* ((pos (list :line (1- line) :character col))
             (params (list :pos pos))
             (result (lean4-proof-tree--rpc-call
                      "ProofTree.getProofTree" params)))
        (when result
          (gethash "root" result)))
    (error nil)))

;;; Fallback: per-line plainGoal queries (Option A)

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
        (forward-line 1)
        (while (and (not (eobp))
                    (looking-at-p "^\\s-*$"))
          (forward-line 1))
        (let ((tactic-col (if (eobp) 0 (current-indentation))))
          (when (> tactic-col 0)
            (forward-line 1)
            (while (and (not (eobp))
                        (or (looking-at-p "^\\s-*$")
                            (>= (current-indentation)
                                tactic-col)))
              (forward-line 1)))
          (setq end (1- (line-number-at-pos))))
        (when (and (<= start orig) (>= end orig))
          (cons start end))))))

(defun lean4-proof-tree--extract-tactics (beg end)
  "Extract tactic lines between BEG and END."
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

(defun lean4-proof-tree--query-goals-fallback (line)
  "Query goals at end of LINE via plainGoal (fallback)."
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

;;; Tree rendering

(defun lean4-proof-tree--json-get (obj key)
  "Get KEY from JSON OBJ (hash table or plist)."
  (if (hash-table-p obj)
      (gethash key obj)
    (plist-get obj (intern (concat ":" key)))))

(defun lean4-proof-tree--render-rpc-tree (node depth prefix
                                                last-p
                                                cursor-line)
  "Render a single RPC tree NODE at DEPTH with PREFIX.
LAST-P is non-nil if this is the last sibling.
CURSOR-LINE highlights the active tactic."
  (let* ((tactic (lean4-proof-tree--json-get node "tactic"))
         (goals-after (lean4-proof-tree--json-get node "goalsAfter"))
         (children (lean4-proof-tree--json-get node "children"))
         (range (lean4-proof-tree--json-get node "range"))
         (closed (or (null goals-after)
                     (= (length goals-after) 0)))
         ;; Determine if cursor is on this tactic
         (at-cursor
          (when range
            (let* ((start (lean4-proof-tree--json-get range "start"))
                   (start-line
                    (1+ (lean4-proof-tree--json-get start "line"))))
              (= start-line cursor-line))))
         ;; Branch characters
         (connector
          (if (= depth 0) ""
            (propertize (if last-p "`-- " "|-- ")
                        'face 'lean4-proof-tree-branch-face)))
         (child-prefix
          (if (= depth 0) ""
            (concat prefix
                    (propertize (if last-p "    " "|   ")
                                'face
                                'lean4-proof-tree-branch-face))))
         (status (if closed " [done]" ""))
         (line-beg (point)))
    ;; Tactic line
    (insert prefix connector
            (propertize (or tactic "?")
                        'face 'lean4-proof-tree-tactic-face)
            (propertize status
                        'face (if closed
                                  'lean4-proof-tree-closed-face
                                'lean4-proof-tree-open-face))
            "\n")
    (when at-cursor
      (put-text-property line-beg (point)
                         'face 'lean4-proof-tree-cursor-face))
    ;; Show goals if open and no children
    (when (and goals-after (not closed)
               (or (null children) (= (length children) 0)))
      (let ((goals-list (append goals-after nil)))
        (dolist (g goals-list)
          (let ((target (lean4-proof-tree--json-get g "target")))
            (when target
              (insert child-prefix "  "
                      (propertize target
                                  'face 'lean4-proof-tree-goal-face)
                      "\n"))))))
    ;; Render children
    (when children
      (let* ((child-list (append children nil))
             (len (length child-list)))
        (cl-loop for child in child-list
                 for idx from 0
                 do (lean4-proof-tree--render-rpc-tree
                     child (1+ depth) child-prefix
                     (= idx (1- len))
                     cursor-line))))))

(defun lean4-proof-tree--render-rpc (root cursor-line)
  "Render the RPC proof tree ROOT into the current buffer."
  (let ((inhibit-read-only t))
    (erase-buffer)
    (if (null root)
        (insert "No proof tree found at point.\n"
                "\n"
                "Make sure your Lean file imports ProofTree:\n"
                "  import ProofTree\n")
      (lean4-proof-tree--render-rpc-tree
       root 0 "" t cursor-line))
    (goto-char (point-min))))

(defun lean4-proof-tree--render-fallback (tactics cursor-line)
  "Render flat tactic list TACTICS (fallback mode)."
  (let ((inhibit-read-only t))
    (erase-buffer)
    (if (null tactics)
        (insert "No tactic block found at point.\n")
      (dolist (tac tactics)
        (let* ((line (car tac))
               (text (cdr tac))
               (goals (lean4-proof-tree--query-goals-fallback line))
               (closed (null goals))
               (at-cursor (= line cursor-line))
               (line-beg (point)))
          (insert (propertize text
                              'face 'lean4-proof-tree-tactic-face)
                  (propertize (if closed " [done]" "")
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
                       (concat "|- " (string-trim g))
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
  (when lean4-proof-tree--source-buffer
    (lean4-proof-tree--update-from
     lean4-proof-tree--source-buffer)))

;;; Update

(defun lean4-proof-tree--update-from (source)
  "Rebuild and render the proof tree from SOURCE buffer."
  (when (buffer-live-p source)
    (with-current-buffer source
      (let ((cursor-line (line-number-at-pos))
            (tree-buf (get-buffer lean4-proof-tree-buffer-name)))
        (when tree-buf
          (if lean4-proof-tree-use-rpc
              ;; Option C: RPC-based tree from InfoTree
              (let ((root (lean4-proof-tree--query-rpc
                           cursor-line 0)))
                (with-current-buffer tree-buf
                  (lean4-proof-tree--render-rpc
                   root cursor-line)))
            ;; Fallback: per-line plainGoal
            (let ((block (lean4-proof-tree--find-by-block)))
              (if block
                  (let ((tactics
                         (lean4-proof-tree--extract-tactics
                          (car block) (cdr block))))
                    (with-current-buffer tree-buf
                      (lean4-proof-tree--render-fallback
                       tactics cursor-line)))
                (with-current-buffer tree-buf
                  (lean4-proof-tree--render-fallback
                   nil cursor-line))))))))))

(defun lean4-proof-tree--update-debounced ()
  "Debounced proof tree update."
  (when (and (eq major-mode 'lean4-mode)
             (get-buffer-window lean4-proof-tree-buffer-name t))
    (when lean4-proof-tree--update-timer
      (cancel-timer lean4-proof-tree--update-timer))
    (let ((source (current-buffer)))
      (setq lean4-proof-tree--update-timer
            (run-with-idle-timer
             0.5 nil
             (lambda ()
               (lean4-proof-tree--update-from source)))))))

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
    (lean4-proof-tree--update-from source)))

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
  "Show or refresh the proof tree display."
  (interactive)
  (lean4-proof-tree-show))

;; Keybinding
(with-eval-after-load 'lean4-mode
  (define-key lean4-mode-map (kbd "C-c C-t")
              #'lean4-proof-tree-toggle))

(provide 'lean4-proof-tree)
;;; lean4-proof-tree.el ends here
