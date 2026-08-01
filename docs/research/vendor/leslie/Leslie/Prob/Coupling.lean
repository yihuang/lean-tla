/-
M1 W2 — pRHL-style coupling judgment for `PMF`.

A *coupling* of two PMFs `μ : PMF α` and `ν : PMF β` is a joint
distribution on `α × β` whose marginals are `μ` and `ν`. Couplings
that support a relation `R : α → β → Prop` lift relational reasoning
from sample-pairs to distributions — the foundation of probabilistic
relational Hoare logic (pRHL).

This module provides the structure plus the most-used constructors:

  * `PMF.Coupling μ ν` — the structure (joint + marginal proofs)
  * `PMF.Coupling.supports c R` — `R` holds on the joint's support
  * `PMF.eq_of_coupling_id` — an `Eq`-supporting coupling proves
    `μ = ν`
  * `PMF.Coupling.pure_id` — Dirac on the diagonal
  * `PMF.Coupling.bijection` — bijection-induced coupling
  * `PMF.Coupling.self` — `μ` coupled with itself

More combinators (`bind`, `swap`, `up_to_bad`) and tactics that wrap
them land later. Mathlib does not have a direct `PMF.Coupling`
structure (it has measure-theoretic couplings elsewhere); we define
our own in the `PMF` namespace.
-/

import Leslie.Prob.PMF

namespace PMF

variable {α β : Type*}

/-! ## The Coupling structure -/

/-- A coupling of `μ : PMF α` and `ν : PMF β`: a joint distribution
on `α × β` whose marginals are `μ` and `ν`. -/
structure Coupling (μ : PMF α) (ν : PMF β) where
  joint      : PMF (α × β)
  marg_left  : joint.map Prod.fst = μ
  marg_right : joint.map Prod.snd = ν

namespace Coupling

variable {μ : PMF α} {ν : PMF β}

/-- A coupling *supports* a relation `R : α → β → Prop` if every pair
in the joint's support is `R`-related. -/
def supports (c : Coupling μ ν) (R : α → β → Prop) : Prop :=
  ∀ p ∈ c.joint.support, R p.1 p.2

end Coupling

/-! ## Constructors -/

/-- The diagonal coupling: `μ` coupled with itself by sampling once
and pairing with the same value. -/
noncomputable def Coupling.self (μ : PMF α) : Coupling μ μ where
  joint      := μ.bind fun a => PMF.pure (a, a)
  marg_left  := by simp [PMF.map_bind, PMF.pure_map, PMF.bind_pure]
  marg_right := by simp [PMF.map_bind, PMF.pure_map, PMF.bind_pure]

/-- The diagonal coupling supports equality. -/
theorem Coupling.self_supports_eq (μ : PMF α) :
    (Coupling.self μ).supports (· = ·) := by
  intro p hp
  -- joint = μ.bind (fun a => pure (a, a)); support is {(a, a) | a ∈ μ.support}
  simp [Coupling.self, PMF.support_bind, PMF.support_pure] at hp
  obtain ⟨a, _, rfl⟩ := hp
  rfl

/-- Dirac on the diagonal: `pure a` is coupled with itself. -/
noncomputable def Coupling.pure_id (a : α) : Coupling (PMF.pure a) (PMF.pure a) :=
  Coupling.self (PMF.pure a)

/-- Bijection-induced coupling: from `f : α → β`, `μ` is coupled with
`μ.map f` via the joint `μ.bind (fun a => pure (a, f a))`, supporting
`fun a b => b = f a`. -/
noncomputable def Coupling.bijection (μ : PMF α) (f : α → β) :
    Coupling μ (μ.map f) where
  joint      := μ.bind fun a => PMF.pure (a, f a)
  marg_left  := by simp [PMF.map_bind, PMF.pure_map, PMF.bind_pure]
  marg_right := by
    simp only [PMF.map_bind, PMF.pure_map]
    exact PMF.bind_pure_comp f μ

/-- The bijection coupling supports `b = f a`. -/
theorem Coupling.bijection_supports (μ : PMF α) (f : α → β) :
    (Coupling.bijection μ f).supports (fun a b => b = f a) := by
  intro p hp
  -- joint = μ.bind (fun a => pure (a, f a))
  simp [Coupling.bijection, PMF.support_bind, PMF.support_pure] at hp
  obtain ⟨a, _, rfl⟩ := hp
  rfl

/-! ## Marginal pushforward helpers

`Coupling`'s `marg_left` / `marg_right` fields are dependent
equalities (`c.joint.map Prod.fst = μ`), so direct `rw [c.marg_left]`
fails with motive-not-type-correct in many goals. The two lemmas
below repackage the marginal facts at the outer-measure level,
where `μ.toOuterMeasure S = c.joint.toOuterMeasure (Prod.fst ⁻¹' S)`
elaborates cleanly without `conv` workarounds. -/

/-- A coupling's first marginal at the outer-measure level. -/
theorem Coupling.toOuterMeasure_left {μ : PMF α} {ν : PMF β}
    (c : Coupling μ ν) (S : Set α) :
    μ.toOuterMeasure S = c.joint.toOuterMeasure (Prod.fst ⁻¹' S) := by
  conv_lhs => rw [← c.marg_left]
  rw [PMF.toOuterMeasure_map_apply]

/-- A coupling's second marginal at the outer-measure level. -/
theorem Coupling.toOuterMeasure_right {μ : PMF α} {ν : PMF β}
    (c : Coupling μ ν) (S : Set β) :
    ν.toOuterMeasure S = c.joint.toOuterMeasure (Prod.snd ⁻¹' S) := by
  conv_lhs => rw [← c.marg_right]
  rw [PMF.toOuterMeasure_map_apply]

/-! ## eq_of_coupling_id

Cornerstone of "rewrite by coupling": equality of marginals follows
from a coupling supporting `(· = ·)`. -/

/-- A coupling that supports `(· = ·)` proves `μ = ν`. -/
theorem eq_of_coupling_id {μ ν : PMF α} (c : Coupling μ ν)
    (h : c.supports (· = ·)) : μ = ν := by
  apply PMF.ext
  intro a
  -- Reduce μ a and ν a to coordinate-projected forms.
  have hL : μ a = (c.joint.map Prod.fst) a := by rw [c.marg_left]
  have hR : ν a = (c.joint.map Prod.snd) a := by rw [c.marg_right]
  rw [hL, hR, PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ c.joint.support
  · -- supports (·=·) gives p.1 = p.2 on support
    have heq : p.1 = p.2 := h p hp
    by_cases ha : a = p.1
    · simp [ha, heq]
    · have ha2 : a ≠ p.2 := heq ▸ ha
      simp [ha, ha2]
  · -- off support, joint p = 0 (use apply_eq_zero_iff)
    have hzero : c.joint p = 0 := (PMF.apply_eq_zero_iff c.joint p).mpr hp
    rw [hzero]
    simp

/-! ## coupling_up_to_bad — pRHL "up-to-bad"

The classical "fundamental lemma of game-playing" in the
information-theoretic setting: if a coupling `c` of `μ` and `ν`
agrees on coordinates everywhere outside a "bad" event `B` on the
joint, then for any event `S ⊆ α`,

    `μ.toOuterMeasure S ≤ ν.toOuterMeasure S + Pr_joint[B]`.

(And by symmetry, the same with `μ` and `ν` swapped.)

This is the cleanest statement that supports cryptographic
reductions: replace one game by another, and pay the probability
of the bad event as the gap. The hypothesis `h_good` says: on the
joint's support, `¬ B p → p.1 = p.2` — outside `B`, the coupling
witnesses equality of coordinates.

Compare with `eq_of_coupling_id`: when `B = ⊥` (no bad event), the
bound collapses to `μ S ≤ ν S`, and applying the same combinator
in both directions yields `μ S = ν S`, hence `μ = ν`.

This combinator is the M2.5 W2 deliverable; the Wegman–Carter
ITMAC bound (`Examples/Prob/ITMAC.lean`) is its first non-trivial
client. -/

/-- "Up-to-bad" probability bound for a coupling of two PMFs on
the same type.

Let `μ ν : PMF α` and `c : Coupling μ ν`. If `B : α × α → Prop` is
a "bad" predicate on the joint such that on the joint's support,
`¬ B p` implies `p.1 = p.2`, then for any event `S ⊆ α`,
`μ.toOuterMeasure S ≤ ν.toOuterMeasure S + Pr_joint[B]`. -/
theorem coupling_up_to_bad {μ ν : PMF α}
    (c : Coupling μ ν) (B : α × α → Prop)
    (h_good : ∀ p ∈ c.joint.support, ¬ B p → p.1 = p.2)
    (S : Set α) :
    μ.toOuterMeasure S ≤
      ν.toOuterMeasure S + c.joint.toOuterMeasure {p | B p} := by
  -- Rewrite both marginal measures as joint preimage measures via the
  -- outer-measure helpers (avoids the dependent-`c.marg_*` motive issue).
  rw [c.toOuterMeasure_left S, c.toOuterMeasure_right S]
  -- All three measures are tsums of indicators of subsets of α × α
  -- against `c.joint`. We do the inequality pointwise on each `p`.
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro p
  by_cases hp : p ∈ c.joint.support
  · -- On support, decide on `B p`.
    by_cases hB : B p
    · -- Bad case: bound LHS by the bad-set indicator alone.
      have h_bad : (Set.indicator {p | B p} (⇑c.joint)) p = c.joint p := by
        simp [Set.indicator_of_mem, hB]
      calc Set.indicator (Prod.fst ⁻¹' S) (⇑c.joint) p
          ≤ c.joint p := Set.indicator_le_self _ _ p
        _ = (Set.indicator {p | B p} (⇑c.joint)) p := h_bad.symm
        _ ≤ Set.indicator (Prod.snd ⁻¹' S) (⇑c.joint) p
            + Set.indicator {p | B p} (⇑c.joint) p := le_add_self
    · -- Good case: `p.1 = p.2` by `h_good`, so the two preimage
      -- indicators are equal and LHS = RHS-left ≤ RHS.
      have heq : p.1 = p.2 := h_good p hp hB
      have h_pre : (Prod.fst ⁻¹' S) p ↔ (Prod.snd ⁻¹' S) p := by
        constructor <;> intro h
        · show p.2 ∈ S; rw [← heq]; exact h
        · show p.1 ∈ S; rw [heq]; exact h
      have h_ind_eq :
          Set.indicator (Prod.fst ⁻¹' S) (⇑c.joint) p
            = Set.indicator (Prod.snd ⁻¹' S) (⇑c.joint) p := by
        by_cases hPS : p.1 ∈ S
        · have hPS' : p.2 ∈ S := h_pre.mp hPS
          simp [Set.indicator_of_mem, hPS, hPS']
        · have hPS' : p.2 ∉ S := fun h => hPS (h_pre.mpr h)
          simp [Set.indicator_of_notMem, hPS, hPS']
      rw [h_ind_eq]
      exact le_self_add
  · -- Off support: `joint p = 0`, so all indicators are 0.
    have hzero : c.joint p = 0 := (PMF.apply_eq_zero_iff c.joint p).mpr hp
    have h0L : Set.indicator (Prod.fst ⁻¹' S) (⇑c.joint) p = 0 := by
      by_cases h : p ∈ Prod.fst ⁻¹' S
      · simp [Set.indicator_of_mem, h, hzero]
      · simp [Set.indicator_of_notMem, h]
    rw [h0L]
    exact zero_le _

/-- Symmetric form of `coupling_up_to_bad`: bound `ν S` in terms
of `μ S` plus the bad-event probability. -/
theorem coupling_up_to_bad_symm {μ ν : PMF α}
    (c : Coupling μ ν) (B : α × α → Prop)
    (h_good : ∀ p ∈ c.joint.support, ¬ B p → p.1 = p.2)
    (S : Set α) :
    ν.toOuterMeasure S ≤
      μ.toOuterMeasure S + c.joint.toOuterMeasure {p | B p} := by
  -- Build the swapped coupling and apply `coupling_up_to_bad`.
  let c' : Coupling ν μ :=
    { joint := c.joint.map Prod.swap
      marg_left := by
        rw [PMF.map_comp]
        show c.joint.map (Prod.fst ∘ Prod.swap) = ν
        have : (Prod.fst ∘ Prod.swap : α × α → α) = Prod.snd := rfl
        rw [this, c.marg_right]
      marg_right := by
        rw [PMF.map_comp]
        show c.joint.map (Prod.snd ∘ Prod.swap) = μ
        have : (Prod.snd ∘ Prod.swap : α × α → α) = Prod.fst := rfl
        rw [this, c.marg_left] }
  have h_good' : ∀ p ∈ c'.joint.support,
      ¬ (fun q : α × α => B q.swap) p → p.1 = p.2 := by
    intro p hp hB
    have hp' : p.swap ∈ c.joint.support := by
      change p ∈ (c.joint.map Prod.swap).support at hp
      rw [PMF.support_map] at hp
      obtain ⟨q, hq, hpq⟩ := hp
      have : p.swap = q := by rw [← hpq]; exact Prod.swap_swap q
      rw [this]; exact hq
    exact (h_good p.swap hp' hB).symm
  have h := coupling_up_to_bad c' (fun q : α × α => B q.swap) h_good' S
  have h_bad_swap :
      c'.joint.toOuterMeasure {q | B q.swap}
        = c.joint.toOuterMeasure {p | B p} := by
    show (c.joint.map Prod.swap).toOuterMeasure {q | B q.swap}
        = c.joint.toOuterMeasure {p | B p}
    rw [PMF.toOuterMeasure_map_apply]
    -- The preimage `Prod.swap ⁻¹' {q | B q.swap}` is `{p | B p}`
    -- because `q.swap.swap = q`.
    congr 1
  show ν.toOuterMeasure S ≤
      μ.toOuterMeasure S + c.joint.toOuterMeasure {p | B p}
  rw [← h_bad_swap]
  exact h

end PMF
