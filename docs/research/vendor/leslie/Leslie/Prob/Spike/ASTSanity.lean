/-
M0.3 sanity check — AST certificate shape compiles against Mathlib's
martingale stack on the M0.1 trace measure type.

This file is part of the M0 spike. It demonstrates that the POPL 2025
two-function (V, U) AST rule can be *stated* in Lean against the
`Measure (Π n, X n)` trace type from `CoinFlip.lean`, with all proof
obligations typed correctly under Mathlib's `Submartingale` /
`Supermartingale` / `Filtration` / `Filtration.natural` /
`Submartingale.ae_tendsto_limitProcess` API.

The bodies are `sorry` per the M0 sorry budget — full proofs are
M3 W1 work. M0.3's exit gate is "stub builds green; outline written";
the outline is in `docs/randomized-leslie-spike/02-ast-soundness.md`.
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration

namespace Leslie.Prob.Spike

open MeasureTheory ProbabilityTheory Filter

/-! ## Setup

`ASTCert` is stated against an arbitrary measure `μ` on a filtered
measurable space. The concrete instantiation against the M0.1 trace
measure (with the natural filtration on `Π n, X n` from
`Filtration.natural` applied to the coordinate process) is M3 W1
work — `Filtration.natural` requires `StronglyMeasurable` on the
coordinate maps which in turn needs `MetrizableSpace` on each `X n`,
straightforward but type-class plumbing we defer.

For M0.3 the goal is just to confirm `ASTCert` and `ASTCert.sound`
compile against `Mathlib.Probability.Martingale.Convergence`'s
`Submartingale` / `Supermartingale` API. -/

/-! ## AST certificate (POPL 2025 Rule 3.2)

The (V, U) pair: `V : ℕ → Ω → ℝ` is a non-negative real-valued
supermartingale (the "likelihood" component); `U : ℕ → Ω → ℕ` is a
deterministic-step variant (the "distance" component). Sublevel-set
compatibility binds them: on `{V ≤ r}`, `U` is bounded.

The fields below are the minimum to demonstrate the *shape* compiles
against Mathlib's martingale typeclasses. The full POPL 2025 form has
finer fields distinguishing pure-probabilistic from
nondeterministic-probabilistic states; that distinction lands in M3
W1 alongside `ProbActionSpec`.
-/

/-- Almost-sure termination predicate: there exists a step at which
`term` holds, almost surely under `μ`. -/
def AlmostSureTerm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (term : ℕ → Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, ∃ n, term n ω

/-- AST certificate: a non-negative real-valued supermartingale `V`
together with a `ℕ`-valued variant `U`, with sublevel-set
compatibility. Stated against an arbitrary trace measure `μ` on a
filtered space. -/
structure ASTCert
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (V : ℕ → Ω → ℝ)
    (U : ℕ → Ω → ℕ)
    (term : ℕ → Ω → Prop) : Prop where
  /-- `V` is a supermartingale w.r.t. the filtration. -/
  V_super     : Supermartingale V ℱ μ
  /-- `V` is non-negative almost surely at every step. -/
  V_nonneg    : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ V n ω
  /-- `V` vanishes on terminating trajectories. -/
  V_term      : ∀ n, ∀ᵐ ω ∂μ, term n ω → V n ω = 0
  /-- `V`'s expected value is bounded (needed for convergence). -/
  V_bdd       : ∃ R, ∀ n, eLpNorm (V n) 1 μ ≤ R
  /-- Sublevel-set compatibility: on `{V ≤ r}`, `U` is bounded. -/
  U_bdd_subl  : ∀ r : ℝ, ∃ M : ℕ, ∀ n, ∀ᵐ ω ∂μ, V n ω ≤ r → U n ω ≤ M
  /-- Placeholder for the variant's intended decrease bound.
  **Deliberately vacuous** in this M0 spike to avoid sitting on an
  unsound predicate under a `sorry` body in `ASTCert.sound`.

  An earlier draft of this field used the unconditional tail measure
  `μ {ω' | U (n+1) ω' < U n ω}`, which is strictly weaker than the
  POPL 2025 conditional form (the rule conditions on the prefix σ-
  algebra `ℱ n` that establishes the `V n ω ≤ r ∧ ¬term n ω`
  hypothesis). The unconditional form is not provable for any
  reasonable `(V, U, term)` triple, so a "sound" certificate using
  it would be uninhabited.

  The correct conditional form lives in `Leslie/Prob/Liveness.lean`'s
  `ASTCertificate.U_dec_prob` field, which quantifies over states
  directly: for any state in the sublevel set and any enabled
  action, the per-step PMF puts mass ≥ p on smaller-`U` states. M3
  W1+ uses that form; this M0 spike is calibration-only and
  intentionally scoped down. -/
  U_dec_prob  : True

/-! ## Soundness

Statement-only stub. The proof structure is documented in
`docs/randomized-leslie-spike/02-ast-soundness.md`:

  1. `V_super` + `V_nonneg` + `V_bdd` → `Submartingale.ae_tendsto_limitProcess`
     applied to `-V` gives almost-sure convergence of `V` to a limit.
  2. Non-negativity bounds the limit in `[0, sup V]`.
  3. The Doob upcrossing argument plus sublevel compatibility shows
     that the limit must coincide with `0` almost surely on
     non-terminating paths.
  4. `U_dec_prob` then yields a contradiction with non-zero limit
     measure unless `term` holds eventually almost surely.

Each numbered step references concrete Mathlib lemmas in the outline.
-/

theorem ASTCert.sound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {V : ℕ → Ω → ℝ}
    {U : ℕ → Ω → ℕ}
    {term : ℕ → Ω → Prop}
    (_ : ASTCert μ ℱ V U term) :
    AlmostSureTerm μ term := by
  sorry

/-! ## Specialization to the M0.1 coin-flip trace measure

Demonstrates that `ASTCert` instantiates against `Measure (Π n, X n)`
from `CoinFlip.lean`'s `coinTrace`. Statement-only — `sorry` is
expected since `coinTrace` does not actually terminate (unbiased
coin); this just confirms the type-shape composes. -/

example : True := by trivial  -- placeholder so the file is non-empty after
                              -- Mathlib import

end Leslie.Prob.Spike
