# lean4-proof-tree

Emacs plugin for visualizing Lean 4 tactic proofs as derivation trees.

Uses a server-side Lean 4 library that traverses the elaborator's
InfoTree to build real proof trees with correct parent-child edges
between tactics.

```
constructor
|-- exact h.2 [done]
`-- exact h.1 [done]
```

## Requirements

- Emacs 29.1+
- [lean4-mode](https://github.com/leanprover-community/lean4-mode)
- Lean 4 v4.29.0+

## Setup

### 1. Add the Lake dependency to your Lean project

In your `lakefile.lean`:

```lean
require proofTree from git
  "https://github.com/BaDaaS/lean4-proof-tree" @ "main" / "lean"
```

Then run:

```bash
lake update
lake build proofTree
```

### 2. Import ProofTree in your Lean files

Add at the top of any file where you want proof trees:

```lean
import ProofTree
```

### 3. Install the Emacs plugin

With use-package + vc:

```elisp
(use-package lean4-proof-tree
  :vc (:url "https://github.com/BaDaaS/lean4-proof-tree"
       :branch "main")
  :after lean4-mode)
```

Or manually:

```elisp
(add-to-list 'load-path "/path/to/lean4-proof-tree")
(require 'lean4-proof-tree)
```

## Usage

| Key       | Command                   | Description             |
|-----------|---------------------------|-------------------------|
| `C-c C-t` | `lean4-proof-tree-toggle` | Show/refresh proof tree |

The proof tree panel opens on the right side and updates as you
move your cursor within a tactic block. The current tactic is
highlighted.

- `M-x lean4-proof-tree-show` to open the panel
- `M-x lean4-proof-tree-hide` to close it
- `g` in the proof tree buffer to refresh

## How it works

The Lean 4 library (`lean/` directory) registers an RPC endpoint
`ProofTree.getProofTree` that:

1. Finds the elaboration snapshot at the cursor position
2. Traverses the InfoTree built by the Lean elaborator
3. Extracts TacticInfo nodes with goalsBefore/goalsAfter
4. Builds a tree using the InfoTree's own parent-child structure
5. Pretty-prints goals using ContextInfo.ppGoals
6. Returns the tree as JSON via RPC

The Emacs plugin calls this endpoint via `$/lean/rpc/connect` and
`$/lean/rpc/call`, then renders the result as an ASCII tree.

## Fallback mode

If you don't want to add the Lake dependency, set:

```elisp
(setq lean4-proof-tree-use-rpc nil)
```

This falls back to per-line `$/lean/plainGoal` queries (flat
list, no tree structure).

## Faces

Customize via `M-x customize-group lean4-proof-tree`:

- `lean4-proof-tree-tactic-face` - tactic names
- `lean4-proof-tree-goal-face` - goal types
- `lean4-proof-tree-closed-face` - proved goals
- `lean4-proof-tree-open-face` - unproved goals
- `lean4-proof-tree-cursor-face` - active tactic highlight
- `lean4-proof-tree-branch-face` - tree branch characters

## Running tests

```bash
emacs --batch -L . -l test/lean4-proof-tree-test.el \
  -f ert-run-tests-batch-and-exit
```

## License

Apache 2.0
