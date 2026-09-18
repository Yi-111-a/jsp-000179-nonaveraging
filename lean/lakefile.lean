import Lake
open Lake DSL

package nonaveraging where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

@[default_target]
lean_lib Nonaveraging where
