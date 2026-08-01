/-
M1 W1 — `ProbActionSpec`: probabilistic counterpart of `ActionSpec`.

The shape mirrors `Leslie.Action.ActionSpec σ ι` (function-indexed by
`ι`, no per-action parameter). This is the core abstraction for
`Refinement.lean`, `Liveness.lean`, `Coupling.lean` (M2–M3).

Design choices:

  * `effect : (s : σ) → gate s → PMF σ` is functional — given the
    chosen action and pre-state, the post-state distribution is
    determined. Action-choice non-determinism is the `Adversary`'s
    job (M2 W1); pre-state non-determinism (e.g., `∃ v, s' = ...`)
    must be refined into per-choice action labels before embedding.
    See M0.1 trace-measure decision.

  * The field name `gate` matches `Leslie.GatedAction.gate` (the
    design plan called it `guard`; vocabulary aligned with the rest
    of Leslie).

  * Disjoint-state `parallel` is included as the trivial baseline.
    Distributed protocols share a network and use `parallelWithNet`
    (M2 W1; sketch in `Leslie/Prob/Spike/ParallelShape.lean`).
-/

import Leslie.Prob.PMF

namespace Leslie.Prob

/-! ## ProbGatedAction -/

/-- A gated probabilistic action over state `σ`: a precondition
`gate` and an effect distribution `effect` whose pre-state argument
carries a proof that the gate holds. -/
structure ProbGatedAction (σ : Type*) where
  gate   : σ → Prop
  effect : (s : σ) → gate s → PMF σ

/-! ## ProbActionSpec -/

/-- A probabilistic specification: an initial-state predicate plus a
family of gated probabilistic actions indexed by `ι`. -/
structure ProbActionSpec (σ : Type*) (ι : Type*) where
  init    : σ → Prop
  actions : ι → ProbGatedAction σ

namespace ProbActionSpec

variable {σ ι : Type*}

/-! ### Single-step semantics

`step spec i s` is the next-state distribution if action `i` fires
at `s`, or `none` if its gate is unmet. Classical decidability is
needed because `gate : σ → Prop` carries no `Decidable` witness. -/

open Classical in
/-- Single-step transition under action `i` from state `s`. -/
noncomputable def step (spec : ProbActionSpec σ ι) (i : ι) (s : σ) : Option (PMF σ) :=
  if h : (spec.actions i).gate s
  then some ((spec.actions i).effect s h)
  else none

@[simp] theorem step_eq_some {spec : ProbActionSpec σ ι} {i : ι} {s : σ}
    (h : (spec.actions i).gate s) :
    spec.step i s = some ((spec.actions i).effect s h) := by
  classical exact dif_pos h

@[simp] theorem step_eq_none {spec : ProbActionSpec σ ι} {i : ι} {s : σ}
    (h : ¬ (spec.actions i).gate s) :
    spec.step i s = none := by
  classical exact dif_neg h

/-- Action `i` is enabled at `s` iff its gate holds. -/
def is_enabled (spec : ProbActionSpec σ ι) (i : ι) (s : σ) : Prop :=
  (spec.actions i).gate s

/-! ### Disjoint-state parallel composition

The trivial baseline. Distributed protocols share a network and use
`parallelWithNet` (M2 W1). -/

/-- Disjoint-state parallel composition: each step fires exactly one
side's action and frames the other side's local state. -/
noncomputable def parallel
    {σ₁ σ₂ ι₁ ι₂ : Type*}
    (spec₁ : ProbActionSpec σ₁ ι₁) (spec₂ : ProbActionSpec σ₂ ι₂) :
    ProbActionSpec (σ₁ × σ₂) (ι₁ ⊕ ι₂) where
  init := fun s => spec₁.init s.1 ∧ spec₂.init s.2
  actions := fun
    | .inl i =>
      { gate   := fun s => (spec₁.actions i).gate s.1
        effect := fun s h =>
          ((spec₁.actions i).effect s.1 h).map (·, s.2) }
    | .inr i =>
      { gate   := fun s => (spec₂.actions i).gate s.2
        effect := fun s h =>
          ((spec₂.actions i).effect s.2 h).map (s.1, ·) }

end ProbActionSpec

end Leslie.Prob
