import TlaDsl.Rules

namespace Tla

/-! # Action-algebra counterexamples

Kernel-checked refutations of tempting-but-false laws. Currently one:

* `wf_or_counterexample` — `WF_v(A) ∧ WF_v(B) ⊢ WF_v(A ∨ B)` is *not*
  valid. On the identity behavior over `Nat`, `parityA` is enabled exactly
  on the even states and `parityB` exactly on the odd ones (with
  `v = id`), so neither component is ever eventually-always enabled — both
  `WF`s hold vacuously — while `A ∨ B` is enabled at every state and never
  fires. Strong fairness is different: `sf_or` in `TlaDsl/Rules.lean`
  proves the disjunction law for `SF`, because "infinitely often enabled"
  *does* distribute over `∨`, whereas "eventually always enabled" does
  not.
-/

/-- Enabled exactly on even states, never firing along the identity
behavior. -/
def parityA : Action Nat := fun s s' => s % 2 = 0 ∧ s' ≠ s + 1

/-- Enabled exactly on odd states, never firing along the identity
behavior. -/
def parityB : Action Nat := fun s s' => s % 2 = 1 ∧ s' ≠ s + 1

/-- `parityA` is enabled exactly at even states (the angle action with the
identity state function). -/
theorem enabled_parityA (s : Nat) :
    Enabled (AngleAction parityA (fun x : Nat => x)) s ↔ s % 2 = 0 := by
  constructor
  · rintro ⟨s', hA, _hchg⟩
    exact hA.1
  · intro hs
    refine ⟨s + 2, ⟨⟨hs, by omega⟩, by simp⟩⟩

/-- `parityB` is enabled exactly at odd states. -/
theorem enabled_parityB (s : Nat) :
    Enabled (AngleAction parityB (fun x : Nat => x)) s ↔ s % 2 = 1 := by
  constructor
  · rintro ⟨s', hB, _hchg⟩
    exact hB.1
  · intro hs
    refine ⟨s + 2, ⟨⟨hs, by omega⟩, by simp⟩⟩

/-- No suffix of the identity behavior consists only of even states. -/
lemma not_always_even (k : Nat) : ¬ ∀ m : Nat, (k + m) % 2 = 0 := by
  by_cases hk : k % 2 = 0
  · intro hAll
    have h1 : (k + 1) % 2 = 1 := by
      rw [Nat.add_mod]
      simp [hk]
    exact (by decide : 0 ≠ 1) (hAll 1 ▸ h1)
  · intro hAll
    have hk1 : k % 2 = 1 := (Nat.mod_two_eq_zero_or_one k).resolve_left hk
    exact (by decide : 1 ≠ 0) (hk1 ▸ (by simpa using hAll 0))

/-- No suffix of the identity behavior consists only of odd states. -/
lemma not_always_odd (k : Nat) : ¬ ∀ m : Nat, (k + m) % 2 = 1 := by
  by_cases hk : k % 2 = 1
  · intro hAll
    have h0 : (k + 1) % 2 = 0 := by
      rw [Nat.add_mod]
      simp [hk]
    exact (by decide : 1 ≠ 0) (hAll 1 ▸ h0)
  · intro hAll
    have hk0 : k % 2 = 0 := (Nat.mod_two_eq_zero_or_one k).resolve_right hk
    exact (by decide : 0 ≠ 1) (hk0 ▸ (by simpa using hAll 0))

/-- `WF_v(A) ∧ WF_v(B) ⊢ WF_v(A ∨ B)` is not valid: on the identity
behavior, `parityA` is enabled exactly on even states and `parityB`
exactly on odd ones, so neither `WF` ever has a non-vacuous obligation,
while `A ∨ B` is enabled at every state and never fires. -/
theorem wf_or_counterexample :
    ¬ Entails (tlaAnd (WF_v parityA (fun x : Nat => x))
                      (WF_v parityB (fun x : Nat => x)))
              (WF_v (actOr parityA parityB) (fun x : Nat => x)) := by
  intro h
  let e : Behavior Nat := ⟨fun n => n⟩
  -- both WF's hold on the identity behavior: the always-enabled premise
  -- never holds, because every suffix contains both parities
  have hprem : tlaAnd (WF_v parityA (fun x : Nat => x))
      (WF_v parityB (fun x : Nat => x)) e := by
    constructor
    · intro k hEn
      exfalso
      have hEnAll : ∀ m : Nat, (k + m) % 2 = 0 := by
        intro m
        have hm := hEn m
        have hen : Enabled (AngleAction parityA (fun x : Nat => x)) (e (k + m)) := by
          simpa [statePred, Cslib.ωSequence.drop, e, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hm
        simpa [e] using (enabled_parityA (k + m)).1 (by simpa [e] using hen)
      exact not_always_even k hEnAll
    · intro k hEn
      exfalso
      have hEnAll : ∀ m : Nat, (k + m) % 2 = 1 := by
        intro m
        have hm := hEn m
        have hen : Enabled (AngleAction parityB (fun x : Nat => x)) (e (k + m)) := by
          simpa [statePred, Cslib.ωSequence.drop, e, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hm
        simpa [e] using (enabled_parityB (k + m)).1 (by simpa [e] using hen)
      exact not_always_odd k hEnAll
  -- ... but WF(A ∨ B) fails on it: the premise holds at 0 (every state is
  -- even or odd) while the action never fires
  have hconc : ¬ WF_v (actOr parityA parityB) (fun x : Nat => x) e := by
    intro hWF
    have hPrem0 : always (statePred (Enabled (AngleAction (actOr parityA parityB)
        (fun x : Nat => x)))) (e.drop 0) := by
      intro m
      have hmod : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
      rcases hmod with hm0 | hm1
      · have hAen : Enabled (AngleAction parityA (fun x : Nat => x)) (e m) := by
          simpa [e] using (enabled_parityA m).2 hm0
        simpa [statePred, Cslib.ωSequence.drop, e, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
            (enabled_angle_or parityA parityB (fun x : Nat => x) (e m)).2 (Or.inl hAen)
      · have hBen : Enabled (AngleAction parityB (fun x : Nat => x)) (e m) := by
          simpa [e] using (enabled_parityB m).2 hm1
        simpa [statePred, Cslib.ωSequence.drop, e, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
            (enabled_angle_or parityA parityB (fun x : Nat => x) (e m)).2 (Or.inr hBen)
    rcases hWF 0 hPrem0 with ⟨j, hj⟩
    rcases hj with ⟨hAB, _hchg⟩
    rcases hAB with hA | hB
    · rcases hA with ⟨_hpar, hneq⟩
      simp [Cslib.ωSequence.drop, e, Nat.add_comm] at hneq
    · rcases hB with ⟨_hpar, hneq⟩
      simp [Cslib.ωSequence.drop, e, Nat.add_comm] at hneq
  exact hconc (h e hprem)

end Tla
