import Lake
open Lake DSL

package proofTree where
  leanOptions := #[
    { name := `autoImplicit, value := .ofBool false }
  ]

@[default_target]
lean_lib ProofTree where
  srcDir := "."
