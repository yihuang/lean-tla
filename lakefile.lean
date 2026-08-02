import Lake
open Lake DSL

package lean_tla

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib TlaDsl
