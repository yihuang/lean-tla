import Leslie.EnvAbstraction

open TLA
open SymShared

/-! ## Assume-Guarantee Reasoning for Symmetric Shared-Memory Protocols

    This file defines a circular assume-guarantee rule for symmetric
    shared-memory protocols with environment abstraction.

    Definitions:
    - `SymAG`: assume-guarantee structure with a per-process guarantee
    - `SymAG.focus_inv`: the guarantee holds for the focus process in the abstract system
    - `SymAG.compose`: the guarantee holds for all processes in the concrete system
-/

namespace SymShared

/-- An assume-guarantee structure for a symmetric shared-memory protocol
    with environment abstraction. The `guarantee` is a per-process property
    on shared and local state that is preserved by both focus and environment
    steps, and holds initially. -/
structure SymAG (spec : SymSharedSpec) (ea : EnvAbstraction spec) where
  /-- The per-process guarantee. -/
  guarantee : spec.Shared → spec.Local → Prop
  /-- When focus acts, guarantee preserved for focus. -/
  focus_preserves :
    ∀ (s s' : AbsState spec.Shared ea.EnvState spec.Local),
    guarantee s.shared s.focus →
    (∃ a, ea.focus_step a s s') →
    guarantee s'.shared s'.focus
  /-- When env acts, guarantee preserved for focus (non-interference). -/
  env_preserves :
    ∀ (s s' : AbsState spec.Shared ea.EnvState spec.Local),
    guarantee s.shared s.focus →
    (∃ a, ea.env_step a s s') →
    guarantee s'.shared s'.focus
  /-- Guarantee holds initially. -/
  init_guarantee :
    ∀ sh l, spec.init_shared sh → spec.init_local l → guarantee sh l

/-- The guarantee is an invariant of the abstract system for the focus process.
    This uses `init_invariant`-style reasoning adapted for `safety_stutter`. -/
theorem SymAG.focus_inv {spec : SymSharedSpec} {ea : EnvAbstraction spec}
    (ag : SymAG spec ea) :
    pred_implies (ea.toAbsSpec spec).safety_stutter
      [tlafml| □ ⌜ fun s => ag.guarantee s.shared s.focus ⌝] := by
  -- safety_stutter = ⌜init⌝ ∧ □⟨next ∨ id⟩
  -- We use init_invariant with the stuttering next relation.
  -- The next relation in safety_stutter is: fun s s' => (toAbsSpec.next s s') ∨ s = s'
  -- We need to show the guarantee is preserved by this relation.
  apply init_invariant
  · -- Init case: init s → guarantee s.shared s.focus
    intro s hinit
    simp [EnvAbstraction.toAbsSpec] at hinit
    exact ag.init_guarantee s.shared s.focus hinit.1 hinit.2.1
  · -- Step case: (next s s' ∨ s = s') → guarantee s.shared s.focus → guarantee s'.shared s'.focus
    intro s s' hstep hinv
    rcases hstep with hreal | hstutter
    · -- Real step: next s s'
      simp [EnvAbstraction.toAbsSpec] at hreal
      rcases hreal with ⟨a, hfocus⟩ | ⟨a, henv⟩
      · exact ag.focus_preserves s s' hinv ⟨a, hfocus⟩
      · exact ag.env_preserves s s' hinv ⟨a, henv⟩
    · -- Stutter step: s = s'
      rw [← hstutter]
      exact hinv

/-- Composing the abstract invariant with symmetry to get a concrete invariant
    for all processes. -/
theorem SymAG.compose {spec : SymSharedSpec} {ea : EnvAbstraction spec}
    (ag : SymAG spec ea) (hsym : spec.IsSymmetric) :
    ∀ (n : Nat) [NeZero (n + 1)],
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => ∀ i, ag.guarantee s.shared (s.locals i) ⌝] := by
  intro n _
  -- Use lift_to_all from EnvAbstraction.lean:
  -- lift_to_all needs:
  --   1. An abstract invariant: inv on AbsState
  --   2. A proof that inv holds always under safety_stutter
  --   3. A property P on (Shared, Local)
  --   4. A proof that inv s → P s.shared s.focus
  exact ea.lift_to_all spec hsym n
    (fun s => ag.guarantee s.shared s.focus)
    ag.focus_inv
    (fun sh l => ag.guarantee sh l)
    (fun s hinv => hinv)

end SymShared
