import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Meta
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Two classic protocol examples

1. Two-process turn-based mutex: mutual exclusion (safety) via the standard
   inductive invariant and `init_invariant_stut`.
2. Two-phase progress: `pc = 0 ↝ pc = 2` by chaining two `WF1` applications
   with leads-to transitivity (liveness composition).
-/

namespace TlaDsl.Examples.TwoProcessMutex

structure St where
  pc0 : Nat
  pc1 : Nat
  turn : Nat
deriving Repr

tla_var St pc0 pc1 turn

@[simp] def Req0 : Tla.Action St := [a| pc0 = 0 ∧ pc0' = 1 ∧ pc1' = pc1 ∧ turn' = turn]
@[simp] def Enter0 : Tla.Action St := [a| pc0 = 1 ∧ turn = 0 ∧ pc0' = 2 ∧ pc1' = pc1 ∧ turn' = turn]
@[simp] def Exit0 : Tla.Action St := [a| pc0 = 2 ∧ pc0' = 0 ∧ pc1' = pc1 ∧ turn' = 1]
@[simp] def Req1 : Tla.Action St := [a| pc1 = 0 ∧ pc1' = 1 ∧ pc0' = pc0 ∧ turn' = turn]
@[simp] def Enter1 : Tla.Action St := [a| pc1 = 1 ∧ turn = 1 ∧ pc1' = 2 ∧ pc0' = pc0 ∧ turn' = turn]
@[simp] def Exit1 : Tla.Action St := [a| pc1 = 2 ∧ pc1' = 0 ∧ pc0' = pc0 ∧ turn' = 0]

@[simp] def Next : Tla.Action St := fun s s' =>
  Req0 s s' ∨ Enter0 s s' ∨ Exit0 s s' ∨ Req1 s s' ∨ Enter1 s s' ∨ Exit1 s s'

@[simp] def Init : Tla.StatePred St := [p| pc0 = 0 ∧ pc1 = 0 ∧ turn = 0]

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_vars]

/-- The inductive invariant: whoever is in the critical section holds `turn`,
and all control variables stay in range. -/
def Inv : St → Prop := fun s =>
  ((s.pc0 = 2 → s.turn = 0) ∧ (s.pc1 = 2 → s.turn = 1)) ∧
    (s.pc0 ≤ 2 ∧ s.pc1 ≤ 2 ∧ s.turn ≤ 1)

theorem init_inv : ∀ s, Init s → Inv s := by
  intro s hs
  tla_unfold
  simp [Inv]
  omega

theorem step_inv : ∀ s s', Tla.StutAction Next vars s s' → Inv s → Inv s' := by
  intro s s' hstep hinv
  tla_unfold
  simp [Inv] at hinv ⊢
  rcases hstep with hnext | hstut
  · rcases hnext with h1 | h2 | h3 | h4 | h5 | h6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · cases hstut
    exact hinv

theorem inv_invariant : Tla.Entails Spec (Tla.always (Tla.statePred Inv)) := by
  unfold Spec
  tla_inv
  · exact init_inv
  · exact step_inv

theorem mutual_exclusion :
    Spec ⊢ □ ⌜ (fun s : St => ¬ (s.pc0 = 2 ∧ s.pc1 = 2)) ⌝ := by
  have hmut : Tla.Entails (Tla.always (Tla.statePred Inv))
      (Tla.always (Tla.statePred (fun s : St => ¬ (s.pc0 = 2 ∧ s.pc1 = 2)))) := by
    intro e h n
    have h' : Inv (e n) := by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h n
    intro hboth
    rcases h' with ⟨h01, hle⟩
    rcases h01 with ⟨h0, h1⟩
    rcases hboth with ⟨hpc0, hpc1⟩
    have ht0 : (e n).turn = 0 := h0 (by simpa [Cslib.ωSequence.drop] using hpc0)
    have ht1 : (e n).turn = 1 := h1 (by simpa [Cslib.ωSequence.drop] using hpc1)
    omega
  intro e h
  exact hmut e (inv_invariant e h)

/-! ## Liveness: eventual critical-section entry

Two WF1 applications: if it is process 0's turn she enters (fairness on
`Enter0`), and if process 1 is critical she exits and gives up the turn
(fairness on `Exit1`). Combined with leads-to transitivity and disjunction.
-/

@[simp] def P0 : St → Prop := fun s => s.pc0 = 1 ∧ s.turn = 0
@[simp] def Q0 : St → Prop := fun s => s.pc0 = 2
@[simp] def PB : St → Prop := fun s => s.pc0 = 1 ∧ s.turn = 1 ∧ s.pc1 = 2
@[simp] def PC : St → Prop := fun s => s.pc0 = 1 ∧ s.turn = 1 ∧ s.pc1 = 1
@[simp] def PD : St → Prop := fun s => s.pc0 = 1 ∧ s.turn = 1 ∧ s.pc1 = 0

theorem hstep0 : ∀ s s', P0 s → Tla.StutAction Next vars s s' → P0 s' ∨ Q0 s' := by
  intro s s' hp h
  rcases hp with ⟨hpc0, hturn⟩
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2 | h3 | h4 | h5 | h6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · cases hstut
    omega

theorem haq0 : ∀ s s', P0 s → Tla.AngleAction Enter0 vars s s' → Q0 s' := by
  intro s s' hp h
  tla_unfold
  rcases h with ⟨hA, hchg⟩
  rcases hA with ⟨hpc0, hturn, hpc0', hpc1', hturn'⟩
  exact hpc0'

theorem henable0 : ∀ s, P0 s → Tla.Enabled (Tla.AngleAction Enter0 vars) s ∨ Q0 s := by
  intro s hp
  rcases hp with ⟨hpc0, hturn⟩
  left
  refine ⟨{ pc0 := 2, pc1 := s.pc1, turn := s.turn }, ?_⟩
  tla_unfold
  constructor
  · omega
  · intro hEq
    have hc : (2 : Nat) = s.pc0 := by simpa using congrArg St.pc0 hEq
    omega

/-- If it is process 0's turn, weak fairness on `Enter0` gets her in. -/
theorem turn0_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Enter0 vars))
      (Tla.leadsTo (Tla.statePred P0) (Tla.statePred Q0)) := by
  tla_wf1
  exact henable0

theorem hstepB : ∀ s s', PB s → Tla.StutAction Next vars s s' →
    PB s' ∨ (s'.pc0 = 1 ∧ s'.turn = 0) := by
  intro s s' hp h
  rcases hp with ⟨hpc0, hturn, hpc1⟩
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2 | h3 | h4 | h5 | h6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · cases hstut
    omega

theorem haqB : ∀ s s', PB s → Tla.AngleAction Exit1 vars s s' → s'.pc0 = 1 ∧ s'.turn = 0 := by
  intro s s' hp h
  tla_unfold
  rcases h with ⟨hA, hchg⟩
  rcases hA with ⟨hpc1, hpc1', hpc0', hturn'⟩
  exact ⟨hpc0'.trans hp.1, hturn'⟩

theorem henableB : ∀ s, PB s → Tla.Enabled (Tla.AngleAction Exit1 vars) s ∨ (s.pc0 = 1 ∧ s.turn = 0) := by
  intro s hp
  rcases hp with ⟨hpc0, hturn, hpc1⟩
  left
  refine ⟨{ pc0 := s.pc0, pc1 := 0, turn := 0 }, ?_⟩
  tla_unfold
  constructor
  · omega
  · intro hEq
    have hc : (0 : Nat) = s.pc1 := by simpa using congrArg St.pc1 hEq
    omega

/-- If process 1 is critical, weak fairness on `Exit1` gives the turn to 0. -/
theorem exit1_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Exit1 vars))
      (Tla.leadsTo (Tla.statePred PB) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0))) := by
  tla_wf1
  exact henableB

theorem hstepC : ∀ s s', PC s → Tla.StutAction Next vars s s' → PC s' ∨ PB s' := by
  intro s s' hp h
  rcases hp with ⟨hpc0, hturn, hpc1⟩
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2 | h3 | h4 | h5 | h6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · cases hstut
    omega

theorem haqC : ∀ s s', PC s → Tla.AngleAction Enter1 vars s s' → PB s' := by
  intro s s' hp h
  tla_unfold
  rcases h with ⟨hA, hchg⟩
  rcases hA with ⟨hpc1, hturn, hpc1', hpc0', hturn'⟩
  exact ⟨hpc0'.trans hp.1, hturn'.trans hp.2.1, hpc1'⟩

theorem henableC : ∀ s, PC s → Tla.Enabled (Tla.AngleAction Enter1 vars) s ∨ PB s := by
  intro s hp
  rcases hp with ⟨hpc0, hturn, hpc1⟩
  left
  refine ⟨{ pc0 := s.pc0, pc1 := 2, turn := s.turn }, ?_⟩
  tla_unfold
  constructor
  · omega
  · intro hEq
    have hc : (2 : Nat) = s.pc1 := by simpa using congrArg St.pc1 hEq
    omega

/-- If process 1 is waiting and it is her turn, weak fairness on `Enter1`
puts her in the critical section. -/
theorem enter1_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Enter1 vars))
      (Tla.leadsTo (Tla.statePred PC) (Tla.statePred PB)) := by
  tla_wf1
  exact henableC

theorem hstepD : ∀ s s', PD s → Tla.StutAction Next vars s s' → PD s' ∨ PC s' := by
  intro s s' hp h
  rcases hp with ⟨hpc0, hturn, hpc1⟩
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2 | h3 | h4 | h5 | h6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · cases hstut
    omega

theorem haqD : ∀ s s', PD s → Tla.AngleAction Req1 vars s s' → PC s' := by
  intro s s' hp h
  tla_unfold
  rcases h with ⟨hA, hchg⟩
  rcases hA with ⟨hpc1, hpc1', hpc0', hturn'⟩
  exact ⟨hpc0'.trans hp.1, hturn'.trans hp.2.1, hpc1'⟩

theorem henableD : ∀ s, PD s → Tla.Enabled (Tla.AngleAction Req1 vars) s ∨ PC s := by
  intro s hp
  rcases hp with ⟨hpc0, hturn, hpc1⟩
  left
  refine ⟨{ pc0 := s.pc0, pc1 := 1, turn := s.turn }, ?_⟩
  tla_unfold
  constructor
  · omega
  · intro hEq
    have hc : (1 : Nat) = s.pc1 := by simpa using congrArg St.pc1 hEq
    omega

/-- If process 1 is idle, weak fairness on `Req1` starts her request. -/
theorem req1_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Req1 vars))
      (Tla.leadsTo (Tla.statePred PD) (Tla.statePred PC)) := by
  tla_wf1
  exact henableD

/-- The fairness hypothesis: `□[Next]_vars` plus weak fairness on the four
actions that make progress for process 0. -/
def FairHyp : Tla.Pred St :=
  Tla.tlaAnd (Tla.tlaAnd (Tla.tlaAnd (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Enter0 vars))
      (Tla.WF_v Req1 vars)) (Tla.WF_v Enter1 vars)) (Tla.WF_v Exit1 vars)

/-- The full liveness chain: if process 0 is trying, she eventually enters the
critical section, under fairness on `Enter0`, `Req1`, `Enter1`, `Exit1` and
the inductive invariant. Process 1 must request, enter, and exit to hand the
turn back to process 0. -/
theorem full_liveness :
    Tla.Entails (Tla.tlaAnd FairHyp (Tla.always (Tla.statePred Inv)))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc0 = 1))
        (Tla.statePred Q0)) := by
  intro e hΓ n hp
  rcases hΓ with ⟨hFair, hInv⟩
  rcases hFair with ⟨hFair4, hWF3⟩
  rcases hFair4 with ⟨hFair3, hWF2⟩
  rcases hFair3 with ⟨hFair2, hWF1⟩
  rcases hFair2 with ⟨hspec, hWF0⟩
  have hInvAlways : ∀ m, Inv (e m) := by
    intro m
    simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInv m
  have l0 : Tla.leadsTo (Tla.statePred P0) (Tla.statePred Q0) e :=
    turn0_liveness e ⟨hspec, hWF0⟩
  have lB : Tla.leadsTo (Tla.statePred PB) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0)) e :=
    exit1_liveness e ⟨hspec, hWF3⟩
  have lC : Tla.leadsTo (Tla.statePred PC) (Tla.statePred PB) e :=
    enter1_liveness e ⟨hspec, hWF2⟩
  have lD : Tla.leadsTo (Tla.statePred PD) (Tla.statePred PC) e :=
    req1_liveness e ⟨hspec, hWF1⟩
  have lCq : Tla.leadsTo (Tla.statePred PC) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0)) e :=
    by
      tla_leads_to
  have lDq : Tla.leadsTo (Tla.statePred PD) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0)) e :=
    by
      tla_leads_to
  have hcaseTurn1 : ∀ e0 : Tla.Behavior St, ∀ n, Inv (e0 n) →
      (Tla.statePred (fun s : St => s.pc0 = 1 ∧ s.turn = 1)) (e0.drop n) →
      (Tla.tlaOr (Tla.tlaOr (Tla.statePred PB) (Tla.statePred PC)) (Tla.statePred PD)) (e0.drop n) := by
    intro e0 n hInv hp
    rcases hInv with ⟨h01, hle⟩
    rcases hle with ⟨hpc0le, hpc1le, hturnle⟩
    have hp' : ((e0.drop n) 0).pc0 = 1 ∧ ((e0.drop n) 0).turn = 1 := by
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    by_cases h0 : (e0 n).pc1 = 0
    · right
      exact ⟨hp'.1, hp'.2, by simpa [Cslib.ωSequence.drop] using h0⟩
    · by_cases h1 : (e0 n).pc1 = 1
      · left
        right
        exact ⟨hp'.1, hp'.2, by simpa [Cslib.ωSequence.drop] using h1⟩
      · by_cases h2 : (e0 n).pc1 = 2
        · left
          left
          exact ⟨hp'.1, hp'.2, by simpa [Cslib.ωSequence.drop] using h2⟩
        · exfalso
          omega
  have turn1Chain : ∀ n, Inv (e n) →
      (Tla.statePred (fun s : St => s.pc0 = 1 ∧ s.turn = 1)) (e.drop n) →
      Tla.eventually (Tla.statePred (fun s : St => s.pc0 = 1 ∧ s.turn = 0)) (e.drop n) :=
    Tla.leads_to_cases e Inv (Tla.statePred (fun s : St => s.pc0 = 1 ∧ s.turn = 1))
      (Tla.statePred (fun s : St => s.pc0 = 1 ∧ s.turn = 0))
      (Tla.statePred PB) (Tla.statePred PC) (Tla.statePred PD)
      (hcaseTurn1 e) lB lCq lDq
  have hpe : (e n).pc0 = 1 := by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
  rcases hInvAlways n with ⟨h01, hle⟩
  rcases hle with ⟨hpc0le, hpc1le, hturnle⟩
  by_cases ht0 : (e n).turn = 0
  · exact l0 n (by simpa [P0, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ⟨hpe, ht0⟩)
  · by_cases ht1 : (e n).turn = 1
    · have hT1 : (Tla.statePred (fun s : St => s.pc0 = 1 ∧ s.turn = 1)) (e.drop n) := by
        simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ⟨hpe, ht1⟩
      rcases turn1Chain n (hInvAlways n) hT1 with ⟨m, hq'⟩
      have hP0' : Tla.statePred P0 (e.drop (n + m)) := by
        simpa [P0, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq'
      rcases l0 (n + m) hP0' with ⟨m2, hQ0⟩
      refine ⟨m + m2, ?_⟩
      simpa [Q0, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hQ0
    · exfalso
      omega

/-- If process 0 is trying and either it is her turn, or process 1 is critical
(and will exit), she eventually enters the critical section. -/
theorem two_process_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Enter0 vars))
        (Tla.WF_v Exit1 vars))
      (Tla.leadsTo
        (Tla.statePred (fun s : St =>
          (s.pc0 = 1 ∧ s.turn = 0) ∨ (s.pc0 = 1 ∧ s.turn = 1 ∧ s.pc1 = 2)))
        (Tla.statePred (fun s : St => s.pc0 = 2))) := by
  intro e h
  have hspec1 : Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Enter0 vars) e := ⟨h.1.1, h.1.2⟩
  have hspec2 : Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Exit1 vars) e := ⟨h.1.1, h.2⟩
  have lA : Tla.leadsTo (Tla.statePred P0) (Tla.statePred Q0) e := turn0_liveness e hspec1
  have lB : Tla.leadsTo (Tla.statePred PB) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0)) e :=
    exit1_liveness e hspec2
  have lB2 : Tla.leadsTo (Tla.statePred PB) (Tla.statePred Q0) e :=
    by
      tla_leads_to
  tla_leads_to

end TlaDsl.Examples.TwoProcessMutex

namespace TlaDsl.Examples.TwoPhase

structure St where
  pc : Nat
  x : Nat
deriving Repr

tla_var St pc x

@[simp] def A1 : Tla.Action St := [a| pc = 0 ∧ pc' = 1 ∧ x' = x]
@[simp] def A2 : Tla.Action St := [a| pc = 1 ∧ pc' = 2 ∧ x' = x]
@[simp] def Next : Tla.Action St :=
  [a| (pc = 0 ∧ pc' = 1 ∧ x' = x) ∨ (pc = 1 ∧ pc' = 2 ∧ x' = x)]

theorem hstep1 : ∀ s s', s.pc = 0 → Tla.StutAction Next pc s s' → s'.pc = 0 ∨ s'.pc = 1 := by
  intro s s' hs h
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2
    · right
      exact h1.2.1
    · omega
  · left
    omega

theorem haq1 : ∀ s s', s.pc = 0 → Tla.AngleAction A1 pc s s' → s'.pc = 1 := by
  intro s s' hs h
  tla_unfold
  exact h.1.2.1

theorem henable1 : ∀ s, s.pc = 0 → Tla.Enabled (Tla.AngleAction A1 pc) s ∨ s.pc = 1 := by
  intro s hs
  left
  refine ⟨{ pc := 1, x := s.x }, ?_⟩
  tla_unfold
  omega

theorem hstep2 : ∀ s s', s.pc = 1 → Tla.StutAction Next pc s s' → s'.pc = 1 ∨ s'.pc = 2 := by
  intro s s' hs h
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2
    · omega
    · right
      exact h2.2.1
  · left
    omega

theorem haq2 : ∀ s s', s.pc = 1 → Tla.AngleAction A2 pc s s' → s'.pc = 2 := by
  intro s s' hs h
  tla_unfold
  exact h.1.2.1

theorem henable2 : ∀ s, s.pc = 1 → Tla.Enabled (Tla.AngleAction A2 pc) s ∨ s.pc = 2 := by
  intro s hs
  left
  refine ⟨{ pc := 2, x := s.x }, ?_⟩
  tla_unfold
  omega

/-- Two-phase progress: from phase 0 the protocol reaches phase 2, by chaining
`pc = 0 ↝ pc = 1` and `pc = 1 ↝ pc = 2` (each via WF1) with leads-to
transitivity. -/
theorem two_phase_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A1 pc))
        (Tla.WF_v A2 pc))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 0))
        (Tla.statePred (fun s : St => s.pc = 2))) := by
  have h01 : Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A1 pc))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 0))
        (Tla.statePred (fun s : St => s.pc = 1))) := by
    tla_wf1
    exact henable1
  have h12 : Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A2 pc))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 1))
        (Tla.statePred (fun s : St => s.pc = 2))) := by
    tla_wf1
    exact henable2
  intro e h
  have hspec1 : Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A1 pc) e := ⟨h.1.1, h.1.2⟩
  have hspec2 : Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A2 pc) e := ⟨h.1.1, h.2⟩
  have l1 : Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 0))
      (Tla.statePred (fun s : St => s.pc = 1)) e := h01 e hspec1
  have l2 : Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 1))
      (Tla.statePred (fun s : St => s.pc = 2)) e := h12 e hspec2
  tla_leads_to

end TlaDsl.Examples.TwoPhase
