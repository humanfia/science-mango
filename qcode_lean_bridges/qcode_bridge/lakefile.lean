import Lake
open Lake DSL

package qcode_bridge where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib QCode where
