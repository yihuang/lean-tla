import Leslie.Refinement

/-! ## Counter Refinement Example

    Abstract spec: a counter that increments by 2.
      State: Nat
      Init:  n = 0
      Next:  n' = n + 2

    Concrete spec: a counter that increments by 1, with a phase bit.
      State: Nat × Bool
      Init:  (0, false)
      Next:  if ¬phase then (n + 1, true)    -- first half-step
             else          (n + 1, false)     -- second half-step

    Refinement mapping: f (n, phase) = if phase then n - 1 else n
    (The abstract counter value is the concrete counter "rounded down"
     to the last completed pair of increments.)

    We show: every step of the concrete either maps to an abstract step
    or is a stutter (the abstract state doesn't change).
-/

open TLA

namespace CounterRefinement

/-! ### Abstract Spec: increment by 2 -/

def abstract : Spec Nat where
  init := fun n => n = 0
  next := fun n n' => n' = n + 2

/-! ### Concrete Spec: increment by 1 with phase -/

def concrete : Spec (Nat × Bool) where
  init := fun s => s = (0, false)
  next := fun s s' =>
    (s.2 = false ∧ s' = (s.1 + 1, true)) ∨
    (s.2 = true  ∧ s' = (s.1 + 1, false))

/-! ### Refinement Mapping -/

def ref_map : Nat × Bool → Nat :=
  fun s => if s.2 then s.1 - 1 else s.1

/-! ### Invariant: when phase is true, n > 0 and n is odd;
    when phase is false, n is even. -/

def conc_inv : Nat × Bool → Prop :=
  fun s => (s.2 = true → s.1 > 0) ∧
           (s.2 = false → s.1 % 2 = 0) ∧
           (s.2 = true → s.1 % 2 = 1)

/-! ### Proof: concrete refines abstract (with stuttering) -/

theorem counter_refinement :
    refines_via ref_map concrete.safety abstract.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant concrete abstract ref_map conc_inv
  · -- inv_init
    intro s hs ; subst hs ; simp [conc_inv]
  · -- inv_next
    intro s s' hinv hnext
    simp [concrete, conc_inv] at *
    rcases hnext with ⟨hf, hs'⟩ | ⟨ht, hs'⟩ <;> subst hs'
    · simp_all ; omega
    · simp_all ; omega
  · -- init preservation
    intro s hs ; simp [concrete, abstract, ref_map] at * ; subst hs ; rfl
  · -- step simulation
    intro s s' hinv hnext
    simp [concrete, abstract, ref_map, conc_inv] at *
    rcases hnext with ⟨hf, hs'⟩ | ⟨ht, hs'⟩ <;> subst hs'
    · -- phase false → true: stutter
      right ; simp_all
    · -- phase true → false: abstract step
      left ; simp_all ; omega

/-! ### Alternative: concrete refines a weaker abstract spec (no stuttering needed) -/

def abstract_with_stutter : Spec Nat where
  init := fun n => n = 0
  next := fun n n' => n' = n + 2 ∨ n' = n

theorem counter_refinement_nostutter :
    refines_via ref_map concrete.safety abstract_with_stutter.safety := by
  apply refinement_mapping_with_invariant concrete abstract_with_stutter ref_map conc_inv
  · intro s hs ; subst hs ; simp [conc_inv]
  · intro s s' hinv hnext
    simp [concrete, conc_inv] at *
    rcases hnext with ⟨hf, hs'⟩ | ⟨ht, hs'⟩ <;> subst hs' <;> simp_all <;> omega
  · intro s hs ; simp [concrete, abstract_with_stutter, ref_map] at * ; subst hs ; rfl
  · intro s s' hinv hnext
    simp [concrete, abstract_with_stutter, ref_map, conc_inv] at *
    rcases hnext with ⟨hf, hs'⟩ | ⟨ht, hs'⟩
    · subst hs' ; simp_all
    · subst hs' ; simp_all ; omega

end CounterRefinement
