import Lake
open Lake DSL

package «complexified-qft» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «ComplexifiedQFT» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
