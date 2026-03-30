/-
Copyright (c) 2026 BaDaaS. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import ProofTree.Types

namespace ProofTree

open Lean Elab Server

/-- Pretty-print goals using ContextInfo.ppGoals. -/
def ppGoalStrings (ctx : ContextInfo) (mctx : MetavarContext)
    (goals : List MVarId) : IO (List Goal) := do
  if goals.isEmpty then return []
  let ctx' := { ctx with mctx := mctx }
  let fmt <- ctx'.ppGoals goals
  -- Return one Goal per MVarId with the full formatted output
  let fmtStr := toString fmt
  return goals.map fun mvarId =>
    { id := toString mvarId.name
      hypotheses := []
      target := fmtStr }

/-- Pretty-print goals individually. -/
def ppGoalsIndividual (ctx : ContextInfo) (mctx : MetavarContext)
    (goals : List MVarId) : IO (List Goal) := do
  let ctx' := { ctx with mctx := mctx }
  goals.mapM fun mvarId => do
    let fmt <- ctx'.ppGoals [mvarId]
    return { id := toString mvarId.name
             hypotheses := []
             target := toString fmt }

/-- Get the source range for a tactic's syntax. -/
def tacticRange (ctx : ContextInfo) (stx : Syntax)
    : Option Lean.Lsp.Range :=
  match stx.getPos?, stx.getTailPos? with
  | some startPos, some endPos =>
    let startLsp := ctx.fileMap.leanPosToLspPos
                      (ctx.fileMap.toPosition startPos)
    let endLsp := ctx.fileMap.leanPosToLspPos
                    (ctx.fileMap.toPosition endPos)
    some { start := startLsp, «end» := endLsp }
  | _, _ => none

/-- Build a proof tree by traversing the InfoTree bottom-up.

For each TacticInfo node, we record:
- The tactic syntax as a string
- Goals before and after (pretty-printed)
- Child nodes (from sub-tactics in the InfoTree)

The InfoTree structure gives us the parent-child relationship
between tactics. -/
partial def buildTree (tree : InfoTree)
    (ctx? : Option ContextInfo := none)
    : IO (List Node) := do
  match tree with
  | .context pctx t =>
    let ctx' := pctx.mergeIntoOuter? ctx?
    buildTree t ctx'
  | .node info children =>
    let ctx' := info.updateContext? ctx?
    -- Recurse into children first (bottom-up)
    let mut childNodes : List Node := []
    for child in children do
      let nodes <- buildTree child ctx'
      childNodes := childNodes ++ nodes
    -- If this is a tactic node, wrap children into a tree node
    match info, ctx? with
    | .ofTacticInfo ti, some ctx =>
      let stxStr := ti.stx.reprint.getD (toString ti.stx)
      let stxTrimmed := stxStr.trimAscii.toString
      -- Skip synthetic or internal tactics (empty syntax)
      if stxTrimmed.isEmpty then
        return childNodes
      let goalsBefore <- ppGoalsIndividual ctx
                           ti.mctxBefore ti.goalsBefore
      let goalsAfter <- ppGoalsIndividual ctx
                          ti.mctxAfter ti.goalsAfter
      let range := tacticRange ctx ti.stx
      return [{ tactic := stxTrimmed
                goalsBefore := goalsBefore
                goalsAfter := goalsAfter
                children := childNodes
                range := range }]
    | _, _ =>
      return childNodes
  | .hole _ => return []

/-- Find the proof tree from InfoTrees at a given position. -/
def findProofTreeAtPos (trees : PersistentArray InfoTree)
    (fileMap : FileMap) (pos : Lean.Lsp.Position)
    : IO (Option Node) := do
  let cursorPos := fileMap.lspPosToUtf8Pos pos
  let mut allNodes : List Node := []
  for tree in trees do
    let nodes <- buildTree tree
    allNodes := allNodes ++ nodes
  -- Find nodes whose range contains the cursor
  let filtered := allNodes.filter fun node =>
    match node.range with
    | some r =>
      let startPos := fileMap.lspPosToUtf8Pos r.start
      let endPos := fileMap.lspPosToUtf8Pos r.«end»
      decide (startPos <= cursorPos && cursorPos <= endPos)
    | none => false
  -- Return the first matching node, or first overall
  match filtered.head? with
  | some n => return some n
  | none => return allNodes.head?

end ProofTree
