/-
Copyright (c) 2026 BaDaaS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

open Lean (FromJson ToJson)

namespace ProofTree

/-- A hypothesis in a proof goal. -/
structure Hypothesis where
  name : String
  type : String
  deriving Inhabited, FromJson, ToJson

/-- A single proof goal. -/
structure Goal where
  id : String
  hypotheses : List Hypothesis
  target : String
  deriving Inhabited, FromJson, ToJson

/-- A node in the proof tree. -/
structure Node where
  tactic : String
  goalsBefore : List Goal
  goalsAfter : List Goal
  children : List Node
  range : Option Lean.Lsp.Range
  deriving Inhabited, FromJson, ToJson

/-- The full proof tree returned by the RPC endpoint. -/
structure ProofTreeResult where
  root : Option Node
  deriving Inhabited, FromJson, ToJson

/-- Parameters for the RPC request. -/
structure GetProofTreeParams where
  pos : Lean.Lsp.Position
  deriving FromJson, ToJson

end ProofTree
