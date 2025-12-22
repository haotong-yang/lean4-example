import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.2"

package «lean4-example» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Lean4Example2» {
  -- add library configuration options here
}
