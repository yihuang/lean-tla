import Leslie.Refinement

/-! ## Product Construction for Specifications

    Given a `Spec σ` for a single component, the product construction
    builds a `Spec (Fin m → σ)` for `m` independent copies.

    Each action operates on exactly one component; all others are unchanged.

    Key theorems:
    - `product_invariant_lift`: base invariants lift to each component
    - `product_refines_component`: base refinement lifts to each component
-/

open TLA

namespace ProductSpec

/-- Product of `m` independent copies of a specification. -/
def product (base : Spec σ) (m : Nat) : Spec (Fin m → σ) where
  init := fun s => ∀ k : Fin m, base.init (s k)
  next := fun s s' =>
    ∃ k : Fin m, base.next (s k) (s' k) ∧ ∀ j : Fin m, j ≠ k → s' j = s j

/-- Product initial states project to component initial states. -/
theorem product_init_project (base : Spec σ) (m : Nat)
    (s : Fin m → σ) (hinit : (product base m).init s) (k : Fin m) :
    base.init (s k) :=
  hinit k

/-- If P is an invariant of the base spec, then `fun s => P (s k)` is an
    invariant of the product spec. -/
theorem product_invariant_lift (base : Spec σ) (m : Nat) (k : Fin m)
    (P : σ → Prop)
    (hinit : ∀ s, base.init s → P s)
    (hpres : ∀ s s', P s → base.next s s' → P s') :
    pred_implies (product base m).safety [tlafml| □ ⌜ fun s => P (s k) ⌝] := by
  apply init_invariant
  · intro s hsinit
    exact hinit (s k) (hsinit k)
  · intro s s' hnext hP
    rcases hnext with ⟨k', hstep, hframe⟩
    by_cases hkk' : k = k'
    · subst hkk'
      exact hpres (s k) (s' k) hP hstep
    · rw [hframe k hkk']
      exact hP

/-- The projection of a product execution to component k satisfies
    the base spec's safety_stutter. -/
theorem product_project_stutter (base : Spec σ) (m : Nat) (k : Fin m) :
    refines_via (· k) (product base m).safety base.safety_stutter := by
  intro e ⟨hinit, hnext⟩
  refine ⟨hinit k, ?_⟩
  intro t
  simp only [action_pred, exec.drop, exec.map]
  have ht := hnext t
  simp only [action_pred, exec.drop] at ht
  rcases ht with ⟨k', hstep, hframe⟩
  by_cases hkk' : k = k'
  · subst hkk'; exact Or.inl hstep
  · exact Or.inr (hframe k hkk').symm

/-- If the base spec refines an abstract spec via `f`, then each component
    of the product refines the abstract spec via `f ∘ (· k)`.

    The proof constructs the abstract execution directly: each product step
    either advances the target component (mapped through `f` via `href`) or
    leaves it unchanged (stuttering). -/
theorem product_refines_component (base : Spec σ) (m : Nat)
    {τ : Type} (abstract : Spec τ) (f : σ → τ)
    (hinit_ref : ∀ s, base.init s → abstract.init (f s))
    (hstep_ref : ∀ s s', base.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s')
    (k : Fin m) :
    refines_via (fun s => f (s k))
      (product base m).safety abstract.safety_stutter := by
  intro e ⟨hinit, hnext⟩
  refine ⟨hinit_ref (e 0 k) (hinit k), ?_⟩
  intro t
  simp only [action_pred, exec.drop, exec.map]
  have ht := hnext t
  simp only [action_pred, exec.drop] at ht
  rcases ht with ⟨k', hstep, hframe⟩
  by_cases hkk' : k = k'
  · subst hkk'
    exact hstep_ref _ _ hstep
  · right
    exact congrArg f (hframe k hkk').symm

end ProductSpec
