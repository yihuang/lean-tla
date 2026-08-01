/-
M1 W1 — Project-local PMF utilities.

Mathlib already provides `PMF.pure`, `PMF.bind`, `PMF.map`,
`PMF.support`, `PMF.uniformOfFintype`, `PMF.filter`, plus the
expected algebraic lemmas. This module adds vocabulary aliases that
match the design plan:

  * `PMF.uniform` ⇐ `PMF.uniformOfFintype` (shorter)
  * `PMF.product`  — independent joint via `bind` + `map`
  * `PMF.condition` ⇐ `PMF.filter` (design plan vocabulary)
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

open scoped ENNReal

namespace PMF

variable {α β : Type*}

/-- Uniform distribution on a finite, nonempty type. -/
noncomputable abbrev uniform (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformOfFintype α

@[simp] theorem uniform_apply [Fintype α] [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ :=
  uniformOfFintype_apply a

/-- Independent joint distribution: sample `μ`, then independently
`ν`, return the pair. -/
noncomputable def product (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind fun a => ν.map (a, ·)

/-- Conditional distribution restricted to a positive-measure set
(alias for `PMF.filter`). -/
noncomputable abbrev condition (μ : PMF α) (s : Set α)
    (h : ∃ a ∈ s, a ∈ μ.support) : PMF α :=
  μ.filter s h

/-! ## Translation-invariance of uniform

The general `PMF.uniform_map_of_bijective` (`α → β`) lives in
`Leslie.Prob.Polynomial`; it specializes to the `α = β` case
needed by `Coupling.lean` and the one-time pad. -/

end PMF
