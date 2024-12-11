import Lake
open Lake DSL

package "test" where
  -- add package configuration options here

lean_lib «Test» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe "test" where
  root := `Main
