import Leslie.SymShared

open TLA
open SymShared

/-! ## Environment Abstraction Framework

    This file defines an environment abstraction for symmetric shared-memory
    protocols. Given an `n+1`-process symmetric spec, the abstraction produces
    a 2-component abstract system: a *focus* process (index 0) and an
    *environment summary* that over-approximates the collective state of
    the remaining `n` processes.

    Definitions:
    - `mkLocals` / `otherLocals`: helpers for splitting locals at index 0
    - `AbsState`: abstract state with shared, focus, and env components
    - `EnvAbstraction`: the abstraction structure with soundness conditions
    - `EnvAbstraction.toAbsSpec`: the abstract 2-component `Spec`
    - `EnvAbstraction.abs_map`: the refinement mapping
    - `EnvAbstraction.refinement`: the refinement theorem
    - `EnvAbstraction.lift_to_focus` / `lift_to_all`: invariant lifting
-/

namespace SymShared

/-! ### Helper functions for locals -/

/-- Construct (n+1)-process locals from focus (index 0) and n others. -/
def mkLocals {L : Type} (focus : L) (others : Fin n → L) : Fin (n + 1) → L
  | ⟨0, _⟩ => focus
  | ⟨i + 1, h⟩ => others ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Extract non-focus locals from (n+1)-process locals. -/
def otherLocals {L : Type} (locals : Fin (n + 1) → L) : Fin n → L :=
  locals ∘ Fin.succ

/-! ### Abstract state -/

/-- The abstract 2-component state: focus process + environment summary. -/
structure AbsState (Shared EnvState Local : Type) where
  shared : Shared
  focus : Local
  env : EnvState

/-! ### Environment Abstraction -/

/-- An environment abstraction for a symmetric shared-memory specification.
    It provides an abstract environment state type and soundness conditions
    ensuring that the abstraction faithfully captures the concrete system. -/
structure EnvAbstraction (spec : SymSharedSpec) where
  EnvState : Type
  env_init : EnvState → Prop
  abs_env : (n : Nat) → (Fin n → spec.Local) → EnvState
  /-- Focus process acts, env reacts (on abstract state). -/
  focus_step : spec.ActType → AbsState spec.Shared EnvState spec.Local →
               AbsState spec.Shared EnvState spec.Local → Prop
  /-- Some environment process acts (on abstract state). -/
  env_step : spec.ActType → AbsState spec.Shared EnvState spec.Local →
             AbsState spec.Shared EnvState spec.Local → Prop
  /-- Soundness: concrete init maps to abstract init. -/
  init_sound : ∀ (n : Nat) (locals : Fin n → spec.Local),
    (∀ i, spec.init_local (locals i)) → env_init (abs_env n locals)
  /-- When process 0 acts concretely, focus_step captures it abstractly. -/
  focus_step_sound : ∀ (n : Nat) (a : spec.ActType)
    (s s' : SymState spec.Shared spec.Local (n + 1)),
    spec.step (n + 1) 0 a s s' →
    focus_step a
      ⟨s.shared, s.locals 0, abs_env n (otherLocals s.locals)⟩
      ⟨s'.shared, s'.locals 0, abs_env n (otherLocals s'.locals)⟩
  /-- When process i>0 acts concretely, env_step captures it abstractly. -/
  env_step_sound : ∀ (n : Nat) (i : Fin n) (a : spec.ActType)
    (s s' : SymState spec.Shared spec.Local (n + 1)),
    spec.step (n + 1) i.succ a s s' →
    env_step a
      ⟨s.shared, s.locals 0, abs_env n (otherLocals s.locals)⟩
      ⟨s'.shared, s'.locals 0, abs_env n (otherLocals s'.locals)⟩

/-! ### Abstract Spec construction -/

/-- The abstract 2-component specification derived from an environment abstraction. -/
def EnvAbstraction.toAbsSpec (spec : SymSharedSpec) (ea : EnvAbstraction spec) :
    Spec (AbsState spec.Shared ea.EnvState spec.Local) where
  init := fun s => spec.init_shared s.shared ∧ spec.init_local s.focus ∧ ea.env_init s.env
  next := fun s s' =>
    (∃ a, ea.focus_step a s s') ∨ (∃ a, ea.env_step a s s')
  fair := []

/-! ### Refinement mapping -/

/-- The refinement mapping from concrete (n+1)-process state to abstract state. -/
def EnvAbstraction.abs_map (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (n : Nat) (s : SymState spec.Shared spec.Local (n + 1)) :
    AbsState spec.Shared ea.EnvState spec.Local where
  shared := s.shared
  focus := s.locals 0
  env := ea.abs_env n (otherLocals s.locals)

/-! ### Refinement theorem -/

/-- The (n+1)-process concrete system refines the abstract 2-component system
    via the environment abstraction mapping. -/
theorem EnvAbstraction.refinement (spec : SymSharedSpec) (ea : EnvAbstraction spec) (n : Nat) :
    refines_via (ea.abs_map spec n)
      (spec.toSpec (n + 1)).safety
      (ea.toAbsSpec spec).safety_stutter := by
  apply refinement_mapping_stutter (spec.toSpec (n + 1)) (ea.toAbsSpec spec) (ea.abs_map spec n)
  · -- Init case
    intro s hinit
    simp [SymSharedSpec.toSpec, EnvAbstraction.toAbsSpec, EnvAbstraction.abs_map] at *
    exact ⟨hinit.1, hinit.2 0, ea.init_sound n (otherLocals s.locals)
      (fun i => hinit.2 i.succ)⟩
  · -- Next case
    intro s s' hnext
    simp [SymSharedSpec.toSpec, EnvAbstraction.toAbsSpec, EnvAbstraction.abs_map] at *
    obtain ⟨i, a, hstep⟩ := hnext
    -- Case split on whether i = 0 or i > 0
    by_cases h : i = 0
    · -- Focus process acts
      subst h
      exact Or.inl (Or.inl ⟨a, ea.focus_step_sound n a s s' hstep⟩)
    · -- Environment process acts
      have hi : ∃ j : Fin n, j.succ = i := by
        match i with
        | ⟨0, _⟩ => exact absurd rfl h
        | ⟨k + 1, hk⟩ =>
          exact ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, rfl⟩
      obtain ⟨j, hj⟩ := hi
      subst hj
      exact Or.inl (Or.inr ⟨a, ea.env_step_sound n j a s s' hstep⟩)

/-! ### Invariant lifting -/

/-- Lift an abstract invariant to the concrete system for process 0. -/
theorem EnvAbstraction.lift_to_focus (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (n : Nat)
    (inv : AbsState spec.Shared ea.EnvState spec.Local → Prop)
    (hinv : pred_implies (ea.toAbsSpec spec).safety_stutter [tlafml| □ ⌜ inv ⌝])
    (P : spec.Shared → spec.Local → Prop)
    (hP : ∀ s, inv s → P s.shared s.focus) :
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => P s.shared (s.locals (0 : Fin (n+1))) ⌝] := by
  -- Use refines_stutter_preserves_invariant to transfer the invariant
  have href := ea.refinement spec n
  have htransfer := refines_stutter_preserves_invariant
    (ea.abs_map spec n) (spec.toSpec (n + 1)) (ea.toAbsSpec spec) inv href hinv
  -- htransfer : pred_implies (spec.toSpec (n+1)).safety [tlafml| □ ⌜ inv ∘ ea.abs_map spec n ⌝]
  -- We need to show inv ∘ abs_map implies P on shared/locals 0
  apply pred_implies_trans htransfer
  apply always_monotone
  intro e he
  simp at *
  exact hP _ he

/-- Lift an abstract invariant to all processes (using symmetry). -/
theorem EnvAbstraction.lift_to_all (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (hsym : spec.IsSymmetric) (n : Nat) [NeZero (n + 1)]
    (inv : AbsState spec.Shared ea.EnvState spec.Local → Prop)
    (hinv : pred_implies (ea.toAbsSpec spec).safety_stutter [tlafml| □ ⌜ inv ⌝])
    (P : spec.Shared → spec.Local → Prop)
    (hP : ∀ s, inv s → P s.shared s.focus) :
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => ∀ i, P s.shared (s.locals i) ⌝] := by
  apply spec.forall_from_focus hsym (n + 1) P
  exact ea.lift_to_focus spec n inv hinv P hP

/-! ### Invariant-Relative Environment Abstraction

    When the soundness of the environment abstraction depends on a concrete
    invariant (e.g., SWMR for cache coherence), use `EnvAbstractionInv`.
    This mirrors `refinement_mapping_stutter_with_invariant` from Refinement.lean.
-/

/-- An environment abstraction with invariant-relative soundness.
    The soundness conditions are conditioned on a concrete state invariant `inv`,
    which must be proven inductive on the concrete system independently. -/
structure EnvAbstractionInv (spec : SymSharedSpec) extends EnvAbstraction spec where
  /-- A concrete state invariant (must hold on all reachable states). -/
  inv : SymState spec.Shared spec.Local n → Prop
  /-- The invariant holds initially. -/
  inv_init : ∀ (s : SymState spec.Shared spec.Local n),
    (spec.toSpec n).init s → inv s
  /-- The invariant is preserved by every transition. -/
  inv_next : ∀ (s s' : SymState spec.Shared spec.Local n),
    inv s → (spec.toSpec n).next s s' → inv s'

-- For EnvAbstractionInv, the soundness conditions in the `toEnvAbstraction`
-- field can reference `inv`. But since Lean structures don't easily allow
-- forward references, we instead define the invariant-relative abstraction
-- as a bundled proof obligation.

/-- Package for invariant-relative environment abstraction proofs.
    Given a SymSharedSpec, an EnvAbstraction (with abstract transitions),
    a concrete invariant, and proofs that:
    1. The invariant is inductive on the concrete system
    2. Under the invariant, soundness holds
    This yields the same lifting theorems as EnvAbstraction. -/
structure EnvAbsInvProof (spec : SymSharedSpec) where
  /-- The environment abstraction (abstract state, transitions). -/
  ea : EnvAbstraction spec
  /-- Concrete state invariant (parameterized by n). -/
  conc_inv : (n : Nat) → SymState spec.Shared spec.Local (n + 1) → Prop
  /-- The invariant holds initially. -/
  conc_inv_init : ∀ (n : Nat) (s : SymState spec.Shared spec.Local (n + 1)),
    (spec.toSpec (n + 1)).init s → conc_inv n s
  /-- The invariant is preserved by every transition. -/
  conc_inv_next : ∀ (n : Nat) (s s' : SymState spec.Shared spec.Local (n + 1)),
    conc_inv n s → (spec.toSpec (n + 1)).next s s' → conc_inv n s'
  /-- Soundness of focus_step, conditioned on the invariant. -/
  focus_step_sound_inv : ∀ (n : Nat) (a : spec.ActType)
    (s s' : SymState spec.Shared spec.Local (n + 1)),
    conc_inv n s →
    spec.step (n + 1) 0 a s s' →
    ea.focus_step a
      ⟨s.shared, s.locals 0, ea.abs_env n (otherLocals s.locals)⟩
      ⟨s'.shared, s'.locals 0, ea.abs_env n (otherLocals s'.locals)⟩
  /-- Soundness of env_step, conditioned on the invariant. -/
  env_step_sound_inv : ∀ (n : Nat) (i : Fin n) (a : spec.ActType)
    (s s' : SymState spec.Shared spec.Local (n + 1)),
    conc_inv n s →
    spec.step (n + 1) i.succ a s s' →
    ea.env_step a
      ⟨s.shared, s.locals 0, ea.abs_env n (otherLocals s.locals)⟩
      ⟨s'.shared, s'.locals 0, ea.abs_env n (otherLocals s'.locals)⟩

/-- Invariant-relative refinement: the concrete system refines the abstract one,
    using the concrete invariant to discharge soundness obligations. -/
theorem EnvAbsInvProof.refinement (proof : EnvAbsInvProof spec) (n : Nat) :
    refines_via (proof.ea.abs_map spec n)
      (spec.toSpec (n + 1)).safety
      (proof.ea.toAbsSpec spec).safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    (spec.toSpec (n + 1)) (proof.ea.toAbsSpec spec) (proof.ea.abs_map spec n)
    (proof.conc_inv n)
  · exact proof.conc_inv_init n
  · exact proof.conc_inv_next n
  · intro s hinit
    simp [SymSharedSpec.toSpec, EnvAbstraction.toAbsSpec, EnvAbstraction.abs_map] at *
    exact ⟨hinit.1, hinit.2 0, proof.ea.init_sound n (otherLocals s.locals)
      (fun i => hinit.2 i.succ)⟩
  · intro s s' hinv hnext
    simp [SymSharedSpec.toSpec, EnvAbstraction.toAbsSpec, EnvAbstraction.abs_map] at *
    obtain ⟨i, a, hstep⟩ := hnext
    by_cases h : i = 0
    · subst h
      exact Or.inl (Or.inl ⟨a, proof.focus_step_sound_inv n a s s' hinv hstep⟩)
    · have hi : ∃ j : Fin n, j.succ = i := by
        match i with
        | ⟨0, _⟩ => exact absurd rfl h
        | ⟨k + 1, hk⟩ => exact ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, rfl⟩
      obtain ⟨j, hj⟩ := hi
      subst hj
      exact Or.inl (Or.inr ⟨a, proof.env_step_sound_inv n j a s s' hinv hstep⟩)

/-- Lift abstract invariant to focus process using invariant-relative abstraction. -/
theorem EnvAbsInvProof.lift_to_focus (proof : EnvAbsInvProof spec) (n : Nat)
    (inv : AbsState spec.Shared proof.ea.EnvState spec.Local → Prop)
    (hinv : pred_implies (proof.ea.toAbsSpec spec).safety_stutter [tlafml| □ ⌜ inv ⌝])
    (P : spec.Shared → spec.Local → Prop)
    (hP : ∀ s, inv s → P s.shared s.focus) :
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => P s.shared (s.locals (0 : Fin (n+1))) ⌝] := by
  have href := proof.refinement n
  have htransfer := refines_stutter_preserves_invariant
    (proof.ea.abs_map spec n) (spec.toSpec (n + 1)) (proof.ea.toAbsSpec spec) inv href hinv
  apply pred_implies_trans htransfer
  apply always_monotone
  intro e he
  simp at *
  exact hP _ he

/-- Lift abstract invariant to all processes using invariant-relative abstraction. -/
theorem EnvAbsInvProof.lift_to_all (proof : EnvAbsInvProof spec) (hsym : spec.IsSymmetric)
    (n : Nat) [NeZero (n + 1)]
    (inv : AbsState spec.Shared proof.ea.EnvState spec.Local → Prop)
    (hinv : pred_implies (proof.ea.toAbsSpec spec).safety_stutter [tlafml| □ ⌜ inv ⌝])
    (P : spec.Shared → spec.Local → Prop)
    (hP : ∀ s, inv s → P s.shared s.focus) :
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => ∀ i, P s.shared (s.locals i) ⌝] := by
  apply spec.forall_from_focus hsym (n + 1) P
  exact proof.lift_to_focus n inv hinv P hP

end SymShared
