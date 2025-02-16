import Lake
open Lake DSL

package monoid.space where

  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

@[default_target]
lean_lib MonoidSpace where

  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

meta if get_config? doc = some "on" then
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
