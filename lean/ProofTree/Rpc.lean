/-
Copyright (c) 2026 BaDaaS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.Server.Requests
import ProofTree.Types
import ProofTree.Traverse

namespace ProofTree

open Lean Lean.Server Lean.Server.RequestM

/-- RPC endpoint: returns the proof tree at the given cursor position.

Called from Emacs via:
  $/lean/rpc/call { method: "ProofTree.getProofTree", ... }
-/
@[server_rpc_method]
def getProofTree (params : GetProofTreeParams)
    : RequestM (RequestTask ProofTreeResult) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    let doc <- readDoc
    let fileMap := doc.meta.text
    let tree := snap.infoTree
    let trees := PersistentArray.empty.push tree
    let result <- findProofTreeAtPos trees fileMap params.pos
    return { root := result }

end ProofTree
