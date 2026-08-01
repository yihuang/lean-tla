/-
M0.1 spike — verify Option A (Measure + Ionescu-Tulcea) compiles and
gives a usable trace measure on a trivial example.

This file is part of the M0 spike for the randomized-leslie extension.
It is *not* production code; it lives under `Leslie/Prob/Spike/` to
emphasize that. After the spike closes, this file is either:
  - promoted into `Leslie/Prob/` proper (if the design holds), or
  - deleted and replaced (if a different design is chosen).

Goal of this file:

  1. Construct a coin-flip Markov chain on `Bool` using a constant
     `Kernel` family.
  2. Lift to a `Measure (Π n, Bool)` via `ProbabilityTheory.Kernel.trajMeasure`.
  3. Witness the `IsProbabilityMeasure` instance.
  4. State (and ideally prove) that the marginal at step `n+1` is
     uniform on `Bool`, by reducing to `map_traj_succ_self`.

All four items now build with `0` `sorry`s — the marginal lemma
(item 4) was closed using the Mathlib lemma chain `traj_comp_partialTraj`
+ `Kernel.map_comp` + `map_traj_succ_self` + `Kernel.const_comp'`. The
AST-certificate scaffolding lives in `Leslie/Prob/Spike/ASTSanity.lean`
(M0.3); this file is focused purely on the trace-measure construction.

See `docs/randomized-leslie-spike/01-trace-measure.md` for the
decision rationale and the API references this file relies on.
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Distributions.Uniform

namespace Leslie.Prob.Spike

open MeasureTheory ProbabilityTheory

/-! ## Coin-flip kernel family

`X : ℕ → Type` is the constant family `fun _ => Bool`. The kernel
`κ n : Kernel (Π i : Iic n, Bool) Bool` is history-independent uniform.
-/

/-- The constant state family — every "coordinate" is `Bool`. -/
abbrev X : ℕ → Type := fun _ => Bool

/-- Uniform distribution on `Bool`, as a `Measure`. -/
noncomputable def uniformBool : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure uniformBool := by
  unfold uniformBool
  infer_instance

/-- The history-independent uniform-coin kernel family. -/
noncomputable def coinKernel :
    (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)) :=
  fun _ => Kernel.const _ uniformBool

instance (n : ℕ) : IsMarkovKernel (coinKernel n) := by
  unfold coinKernel
  infer_instance

/-! ## Trace measure

`coinTrace μ₀ : Measure (Π n, Bool)` is the distribution over infinite
coin-flip trajectories starting from initial distribution `μ₀`.
-/

/-- Trace measure over `Π n, Bool` from initial distribution `μ₀`. -/
noncomputable def coinTrace (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] :
    Measure (Π n, X n) :=
  Kernel.trajMeasure μ₀ coinKernel

instance (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (coinTrace μ₀) := by
  unfold coinTrace
  infer_instance

/-! ## Marginal at step `n + 1` is uniform on Bool

This is the headline correctness fact for the prototype. We use
`map_traj_succ_self` from Mathlib: the (a+1)-th marginal of
`traj κ a` equals `κ a` itself. Since our kernel is constant uniform,
every step's marginal is uniform — regardless of the initial
distribution `μ₀`. The proof reduces `traj κ 0` to
`traj κ n ∘ₖ partialTraj κ 0 n` so that `map_traj_succ_self` applies
to the outer `traj κ n`, then collapses the resulting constant kernel
composition with `Kernel.const_comp'`.
-/

/-- For any step `n + 1`, the marginal of the trace measure is uniform
on `Bool`, regardless of the initial distribution.

Proof outline: unfold `coinTrace` to `(traj coinKernel 0) ∘ₘ ν₀`, push the
marginal map through the measure-kernel composition (`Measure.map_comp`),
then compute the kernel marginal via the chain
`traj κ 0 = traj κ n ∘ₖ partialTraj κ 0 n` (`traj_comp_partialTraj`),
`Kernel.map_comp`, and `map_traj_succ_self` (giving `coinKernel n`).
Since `coinKernel n = Kernel.const _ uniformBool` and `partialTraj` is a
Markov kernel, `Kernel.const_comp'` collapses the composition; then
`Measure.const_comp` plus `measure_univ` finishes. -/
theorem coinTrace_marginal_succ_uniform
    (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] (n : ℕ) :
    (coinTrace μ₀).map (fun (x : Π n, X n) => x (n + 1)) = uniformBool := by
  unfold coinTrace Kernel.trajMeasure
  have hν : IsProbabilityMeasure
      (μ₀.map (MeasurableEquiv.piUnique ((fun i : Finset.Iic 0 ↦ X i))).symm) :=
    Measure.isProbabilityMeasure_map <| by fun_prop
  rw [Measure.map_comp _ _ (by fun_prop : Measurable (fun (x : Π n, X n) => x (n + 1)))]
  -- It suffices to show the marginal kernel equals the constant `uniformBool` kernel.
  rw [show (Kernel.traj coinKernel 0).map (fun (x : Π n, X n) => x (n + 1))
        = Kernel.const _ uniformBool from ?_]
  · rw [Measure.const_comp, measure_univ, one_smul]
  -- Reduce `traj coinKernel 0` to `traj coinKernel n ∘ₖ partialTraj coinKernel 0 n`
  -- so that `map_traj_succ_self` applies to the outer `traj coinKernel n`.
  rw [show (Kernel.traj coinKernel 0)
        = (Kernel.traj coinKernel n) ∘ₖ (Kernel.partialTraj coinKernel 0 n) from
       (Kernel.traj_comp_partialTraj (Nat.zero_le n)).symm]
  rw [Kernel.map_comp _ _ _, Kernel.map_traj_succ_self]
  -- `coinKernel n = Kernel.const _ uniformBool`; `partialTraj` is Markov, so
  -- `const_comp'` collapses the composition.
  show (Kernel.const _ uniformBool) ∘ₖ _ = Kernel.const _ uniformBool
  rw [Kernel.const_comp']

/-! ## Scope

The AST-certificate shape was previously stubbed in this file as a
placeholder; it has moved to `Leslie/Prob/Spike/ASTSanity.lean` in its
full POPL 2025 (V, U) form. This file's responsibility is purely the
*trace-measure construction* — `coinKernel`, `coinTrace`, and the
marginal lemma. AST stuff lives next door.
-/

end Leslie.Prob.Spike
