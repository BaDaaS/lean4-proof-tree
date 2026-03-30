# lean4-proof-tree

Emacs plugin for visualizing Lean 4 tactic proofs as derivation trees.

When editing a tactic proof (`by` block), this package queries the Lean
LSP server for the goal state at each tactic step and renders a tree
showing how goals are created, split, and closed.

## Requirements

- Emacs 29.1+
- [lean4-mode](https://github.com/leanprover-community/lean4-mode)
- A running Lean 4 LSP server (started by lean4-mode)

## Installation

### With use-package + vc

```elisp
(use-package lean4-proof-tree
  :vc (:url "https://github.com/BaDaaS/lean4-proof-tree")
  :after lean4-mode)
```

### Manual

Clone this repository and add it to your `load-path`:

```elisp
(add-to-list 'load-path "/path/to/lean4-proof-tree")
(require 'lean4-proof-tree)
```

## Usage

| Key       | Command                   | Description             |
|-----------|---------------------------|-------------------------|
| `C-c C-t` | `lean4-proof-tree-toggle` | Toggle proof tree panel |

The proof tree panel opens on the right side and updates as you move
your cursor within a tactic block. The current tactic is highlighted.

You can also use:

- `M-x lean4-proof-tree-show` to open the panel
- `M-x lean4-proof-tree-hide` to close it
- `g` in the proof tree buffer to refresh

## How it works

1. Finds the `by` block surrounding the cursor
2. Extracts each tactic line
3. Queries `$/lean/plainGoal` at each tactic position via LSP
4. Renders each tactic with its resulting goals
5. Marks completed branches as `[done]`

## Faces

Customize via `M-x customize-group lean4-proof-tree`:

- `lean4-proof-tree-tactic-face` - tactic names
- `lean4-proof-tree-goal-face` - goal types
- `lean4-proof-tree-closed-face` - proved goals
- `lean4-proof-tree-open-face` - unproved goals
- `lean4-proof-tree-cursor-face` - active tactic highlight

## Running tests

```bash
emacs --batch -L . -l test/lean4-proof-tree-test.el \
  -f ert-run-tests-batch-and-exit
```

## License

Apache 2.0
