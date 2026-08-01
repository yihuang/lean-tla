import Leslie.Examples.Peterson
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Peterson's Algorithm: Starvation Freedom

    Under weak fairness of all 8 actions, if process 0 is waiting,
    it eventually enters the critical section.

    **Property**: `pc0 = .waiting ↝ pc0 = .cs`
-/

open TLA

namespace PetersonLiveness

open Peterson

/-! ### Fair specification -/

def petersonFair : ActionSpec PState PAction where
  init := peterson.init
  actions := peterson.actions
  fair := [.setFlag0, .setFlag1, .setTurn0, .setTurn1,
           .enter0, .enter1, .exit0, .exit1]

abbrev Γ := petersonFair.toSpec.formula

/-! ### Extract fairness components -/

private theorem extractNext (e : exec PState) (h : Γ e) :
    always (action_pred peterson.next) e := h.2.1

set_option linter.unusedSimpArgs false in
private theorem extractWF (e : exec PState) (h : Γ e)
    (a : PAction) : weak_fairness (peterson.actions a).toAction e := by
  have hwf := h.2.2
  simp only [petersonFair, ActionSpec.toSpec, Foldable.fold, tla_true] at hwf
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := hwf
  cases a <;> assumption

/-! ### Invariant -/

theorem always_inv : pred_implies Γ [tlafml| □ ⌜ inv ⌝] := by
  intro e hspec
  exact init_invariant inv_init
    (fun s s' hn hi => inv_next s s' hn hi) e ⟨hspec.1, extractNext e hspec⟩

private theorem inv_at (e : exec PState) (hinv : e |=tla= [tlafml| □ ⌜inv⌝]) (k : Nat) :
    inv (e k) := by
  have := hinv k ; simp only [state_pred, exec.drop, Nat.add_zero] at this ; exact this

private theorem mk_sp {f : PState → Prop} {e : exec PState} {k : Nat}
    (h : f (e k)) : state_pred f (e.drop k) := by
  simp [state_pred, exec.drop, Nat.add_zero]; exact h

private theorem un_sp {f : PState → Prop} {e : exec PState} {k : Nat}
    (h : state_pred f (e.drop k)) : f (e k) := by
  simp [state_pred, exec.drop, Nat.add_zero] at h; exact h

/-! ### WF1 step lemmas -/

set_option linter.unusedSimpArgs false in
theorem cs1_leads_to_flag1_false :
    pred_implies Γ
      (leads_to
        (state_pred (fun s => s.pc0 = .waiting ∧ s.pc1 = .cs))
        (state_pred (fun s => s.pc0 = .waiting ∧ s.flag1 = false))) := by
  intro e hspec
  have hinv := always_inv e hspec
  apply wf1_apply (a := (peterson.actions .exit1).toAction) ⟨?_, ?_, ?_,
    extractNext e hspec, extractWF e hspec .exit1⟩
  · intro k hp hnext
    simp only [state_pred, exec.drop, Nat.add_zero] at *
    have hi := inv_at e hinv k
    obtain ⟨i, hfire⟩ := hnext
    cases i <;> simp_all [peterson, GatedAction.fires, inv]
  · intro k hp hnext ha
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction, GatedAction.fires] at *
    obtain ⟨_, ht⟩ := ha
    simp_all [peterson]
  · intro k hp
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction] at *
    left
    exact ⟨{ (e k) with flag1 := false, pc1 := .idle },
      ⟨by simp [peterson, GatedAction.fires, hp.2], by simp [peterson]⟩⟩

set_option linter.unusedSimpArgs false in
theorem flagged1_leads_to_turn_false :
    pred_implies Γ
      (leads_to
        (state_pred (fun s => s.pc0 = .waiting ∧ s.pc1 = .flagged ∧ s.turn = true))
        (state_pred (fun s => s.pc0 = .waiting ∧ s.turn = false))) := by
  intro e hspec
  have hinv := always_inv e hspec
  apply wf1_apply (a := (peterson.actions .setTurn1).toAction) ⟨?_, ?_, ?_,
    extractNext e hspec, extractWF e hspec .setTurn1⟩
  · intro k hp hnext
    simp only [state_pred, exec.drop, Nat.add_zero] at *
    have hi := inv_at e hinv k
    obtain ⟨i, hfire⟩ := hnext
    cases i <;> simp_all [peterson, GatedAction.fires, inv]
  · intro k hp hnext ha
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction, GatedAction.fires] at *
    obtain ⟨_, ht⟩ := ha
    simp_all [peterson]
  · intro k hp
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction] at *
    left
    exact ⟨{ (e k) with turn := false, pc1 := .waiting },
      ⟨by simp [peterson, GatedAction.fires, hp.2.1], by simp [peterson]⟩⟩

set_option linter.unusedSimpArgs false in
theorem waiting1_true_leads_to_cs1 :
    pred_implies Γ
      (leads_to
        (state_pred (fun s => s.pc0 = .waiting ∧ s.pc1 = .waiting ∧ s.turn = true))
        (state_pred (fun s => s.pc0 = .waiting ∧ s.pc1 = .cs))) := by
  intro e hspec
  have hinv := always_inv e hspec
  apply wf1_apply (a := (peterson.actions .enter1).toAction) ⟨?_, ?_, ?_,
    extractNext e hspec, extractWF e hspec .enter1⟩
  · intro k hp hnext
    simp only [state_pred, exec.drop, Nat.add_zero] at *
    have hi := inv_at e hinv k
    obtain ⟨i, hfire⟩ := hnext
    cases i <;> simp_all [peterson, GatedAction.fires, inv]
  · intro k hp hnext ha
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction, GatedAction.fires] at *
    obtain ⟨_, ht⟩ := ha
    simp_all [peterson]
  · intro k hp
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction] at *
    left
    exact ⟨{ (e k) with pc1 := .cs },
      ⟨by simp [peterson, GatedAction.fires, hp.2.1, hp.2.2], by simp [peterson]⟩⟩

set_option linter.unusedSimpArgs false in
theorem turn_false_leads_to_cs0 :
    pred_implies Γ
      (leads_to
        (state_pred (fun s => s.pc0 = .waiting ∧ s.turn = false))
        (state_pred (fun s => s.pc0 = .cs))) := by
  intro e hspec
  have hinv := always_inv e hspec
  apply wf1_apply (a := (peterson.actions .enter0).toAction) ⟨?_, ?_, ?_,
    extractNext e hspec, extractWF e hspec .enter0⟩
  · intro k hp hnext
    simp only [state_pred, exec.drop, Nat.add_zero] at *
    have hi := inv_at e hinv k
    obtain ⟨i, hfire⟩ := hnext
    cases i <;> simp_all [peterson, GatedAction.fires, inv]
  · intro k hp hnext ha
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction, GatedAction.fires] at *
    obtain ⟨_, ht⟩ := ha
    simp_all [peterson]
  · intro k hp
    simp only [state_pred, exec.drop, Nat.add_zero, GatedAction.toAction] at *
    left
    exact ⟨{ (e k) with pc0 := .cs },
      ⟨by simp [peterson, GatedAction.fires, hp.1, hp.2], by simp [peterson]⟩⟩

/-! ### Helper: from flag1=false (pc1=idle) to cs0 -/

/-- At position k with pc0=waiting, flag1=false, pc1=idle: reach cs0.
    Non-recursive: one step to either cs0 or flagged1, then WF1 chain. -/
private theorem idle1_to_cs0 (e : exec PState) (hspec : Γ e) (k : Nat)
    (hpc0 : (e k).pc0 = .waiting) (hf1 : (e k).flag1 = false)
    (hpc1 : (e k).pc1 = .idle) :
    ∃ j, (e (k + j)).pc0 = .cs := by
  have hinv := always_inv e hspec
  have hnext_k := extractNext e hspec k
  simp only [action_pred, exec.drop, Nat.add_zero] at hnext_k
  obtain ⟨i, hfire⟩ := hnext_k
  have hi := inv_at e hinv k
  have hfire_cases : (i = .enter0 ∨ i = .setFlag1) := by
    cases i <;> simp_all [peterson, GatedAction.fires, inv]
  rcases hfire_cases with rfl | rfl
  · -- enter0 fired → pc0=cs at k+1
    simp only [peterson, GatedAction.fires] at hfire
    obtain ⟨_, ht⟩ := hfire
    exact ⟨1, by simp_all⟩
  · -- setFlag1 fired → pc1=flagged at k+1
    simp only [peterson, GatedAction.fires] at hfire
    obtain ⟨_, ht⟩ := hfire
    have hk1_pc0 : (e (k + 1)).pc0 = .waiting := by simp_all
    have hk1_turn : (e (k + 1)).turn = (e k).turn := by simp_all
    have hk1_pc1 : (e (k + 1)).pc1 = .flagged := by simp_all
    by_cases hturn : (e k).turn = false
    · -- turn=false → direct to cs0
      have h1 := turn_false_leads_to_cs0 e hspec (k + 1)
        (mk_sp ⟨hk1_pc0, by rw [hk1_turn]; exact hturn⟩)
      obtain ⟨j1, hj1⟩ := h1
      simp only [state_pred, exec.drop, Nat.add_zero] at hj1
      exact ⟨1 + j1, by simp only [Nat.add_assoc] at hj1 ⊢; exact hj1⟩
    · -- turn=true → flagged1 chain
      simp only [Bool.not_eq_false] at hturn
      have h1 := flagged1_leads_to_turn_false e hspec (k + 1)
        (mk_sp ⟨hk1_pc0, hk1_pc1, by rw [hk1_turn]; exact hturn⟩)
      obtain ⟨j1, hj1⟩ := h1
      simp only [exec.drop_drop] at hj1
      have h2 := turn_false_leads_to_cs0 e hspec (k + 1 + j1) hj1
      obtain ⟨j2, hj2⟩ := h2
      simp only [state_pred, exec.drop, Nat.add_zero] at hj2
      exact ⟨1 + j1 + j2, by simp only [Nat.add_assoc] at hj2 ⊢; exact hj2⟩

/-! ### Main theorem: starvation freedom -/

theorem starvation_freedom_0 :
    pred_implies Γ
      (leads_to (state_pred (fun s => s.pc0 = .waiting))
                (state_pred (fun s => s.pc0 = .cs))) := by
  intro e hspec k hp
  have hp' := un_sp hp
  have hinv := always_inv e hspec
  have hi := inv_at e hinv k
  by_cases hturn : (e k).turn = false
  · -- turn=false → use turn_false_leads_to_cs0
    have h := turn_false_leads_to_cs0 e hspec k (mk_sp ⟨hp', hturn⟩)
    obtain ⟨j, hj⟩ := h
    exact ⟨j, hj⟩
  · simp only [Bool.not_eq_false] at hturn
    -- turn=true: case split on pc1
    by_cases hf1 : (e k).flag1 = false
    · -- flag1=false → pc1=idle
      have hpc1_idle : (e k).pc1 = .idle := by
        have h := hi.2.1; by_contra hne; exact absurd (h.mpr hne) (by simp_all)
      have h := idle1_to_cs0 e hspec k hp' hf1 hpc1_idle
      obtain ⟨j, hj⟩ := h
      exact ⟨j, mk_sp hj⟩
    · -- flag1=true → pc1 ≠ idle
      simp only [Bool.not_eq_false] at hf1
      have hpc1_ne_idle : (e k).pc1 ≠ .idle :=
        fun heq => absurd heq (hi.2.1.mp hf1)
      by_cases hpc1_cs : (e k).pc1 = .cs
      · -- pc1=cs → exit1 → flag1=false → idle1 → cs0
        have h1 := cs1_leads_to_flag1_false e hspec k (mk_sp ⟨hp', hpc1_cs⟩)
        obtain ⟨j1, hj1⟩ := h1
        simp only [state_pred, exec.drop, Nat.add_zero] at hj1
        -- At k+j1: pc0=waiting, flag1=false → use idle1_to_cs0
        have hi' := inv_at e hinv (k + j1)
        have hpc1_idle : (e (k + j1)).pc1 = .idle := by
          have h := hi'.2.1; by_contra hne; exact absurd (h.mpr hne) (by simp_all)
        have h2 := idle1_to_cs0 e hspec (k + j1) hj1.1 hj1.2 hpc1_idle
        obtain ⟨j2, hj2⟩ := h2
        exact ⟨j1 + j2, by simp only [Nat.add_assoc] at hj2 ⊢; exact mk_sp hj2⟩
      · by_cases hpc1_flagged : (e k).pc1 = .flagged
        · -- pc1=flagged, turn=true → setTurn1 → turn=false → cs0
          have h1 := flagged1_leads_to_turn_false e hspec k
            (mk_sp ⟨hp', hpc1_flagged, hturn⟩)
          obtain ⟨j1, hj1⟩ := h1
          simp only [exec.drop_drop] at hj1
          have h2 := turn_false_leads_to_cs0 e hspec (k + j1) hj1
          obtain ⟨j2, hj2⟩ := h2
          simp only [exec.drop_drop] at hj2
          exact ⟨j1 + j2, by
            simp only [exec.drop_drop, Nat.add_assoc] at hj2 ⊢; exact hj2⟩
        · -- pc1=waiting, turn=true → enter1 → pc1=cs → cs1 → flag1=false → idle1 → cs0
          have hpc1_waiting : (e k).pc1 = .waiting := by
            cases h : (e k).pc1 <;> simp_all
          -- Step 1: waiting1 → pc1=cs
          have h1 := waiting1_true_leads_to_cs1 e hspec k
            (mk_sp ⟨hp', hpc1_waiting, hturn⟩)
          obtain ⟨j1, hj1⟩ := h1
          simp only [state_pred, exec.drop, Nat.add_zero] at hj1
          -- Step 2: cs1 → flag1=false
          have h2 := cs1_leads_to_flag1_false e hspec (k + j1)
            (mk_sp hj1)
          obtain ⟨j2, hj2⟩ := h2
          simp only [state_pred, exec.drop, Nat.add_zero] at hj2
          -- Step 3: flag1=false → idle1 → cs0
          have hi' := inv_at e hinv (k + j1 + j2)
          have hpc1_idle : (e (k + j1 + j2)).pc1 = .idle := by
            have h := hi'.2.1; by_contra hne; exact absurd (h.mpr hne) (by simp_all)
          have h3 := idle1_to_cs0 e hspec (k + j1 + j2) hj2.1 hj2.2 hpc1_idle
          obtain ⟨j3, hj3⟩ := h3
          exact ⟨j1 + j2 + j3, by
            simp only [Nat.add_assoc] at hj3 ⊢; exact mk_sp hj3⟩

end PetersonLiveness
