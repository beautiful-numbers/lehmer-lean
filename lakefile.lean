-- FILE: lakefile.lean
import Lake
open Lake DSL

package «lehmer» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Lehmer» where
  srcDir := "Lean"

@[default_target]
lean_exe «lehmer» where
  root := `Main
  srcDir := "."