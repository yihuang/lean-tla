import Lake
open Lake DSL

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.27.0"

require lintLlmProofs from git
  "https://github.com/jessealama/lint-llm-proofs" @ "main"

-- Added in M0 spike for randomized-leslie extension. Pinned to v4.27.0
-- (matches lean-toolchain). See docs/randomized-leslie-spike/01-trace-measure.md.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

package «leslie» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Leslie» where
  -- add any library configuration options here
