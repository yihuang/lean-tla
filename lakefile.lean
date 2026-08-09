import Lake
open Lake DSL

package lean_tla

require cslib from git "https://github.com/leanprover/cslib" @ "main"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib TlaDsl

lean_lib Bft
