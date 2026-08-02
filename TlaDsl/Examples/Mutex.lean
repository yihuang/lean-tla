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

/-- The inductive invariant: whoever is in the critical section holds `turn`. -/
def Inv : St → Prop := fun s => (s.pc0 = 2 → s.turn = 0) ∧ (s.pc1 = 2 → s.turn = 1)

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
    have h' : Inv (e n) := by simpa [Tla.statePred, Tla.Behavior.drop] using h n
    intro hboth
    rcases h' with ⟨h0, h1⟩
    rcases hboth with ⟨hpc0, hpc1⟩
    have ht0 : (e n).turn = 0 := h0 hpc0
    have ht1 : (e n).turn = 1 := h1 hpc1
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
      (Tla.leadsTo (Tla.statePred P0) (Tla.statePred Q0)) :=
  Tla.wf1 P0 Q0 Next Enter0 vars hstep0 haq0 henable0

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
      (Tla.leadsTo (Tla.statePred PB) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0))) :=
  Tla.wf1 PB (fun s => s.pc0 = 1 ∧ s.turn = 0) Next Exit1 vars hstepB haqB henableB

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
    Tla.leadsTo_trans_entails (Tla.statePred PB) (Tla.statePred (fun s => s.pc0 = 1 ∧ s.turn = 0))
      (Tla.statePred Q0) e ⟨lB, lA⟩
  exact Tla.leadsTo_or (Tla.statePred P0) (Tla.statePred PB) (Tla.statePred Q0) e ⟨lA, lB2⟩

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
        (Tla.statePred (fun s : St => s.pc = 1))) :=
    Tla.wf1 (fun s : St => s.pc = 0) (fun s : St => s.pc = 1) Next A1 pc hstep1 haq1 henable1
  have h12 : Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A2 pc))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 1))
        (Tla.statePred (fun s : St => s.pc = 2))) :=
    Tla.wf1 (fun s : St => s.pc = 1) (fun s : St => s.pc = 2) Next A2 pc hstep2 haq2 henable2
  intro e h
  have hspec1 : Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A1 pc) e := ⟨h.1.1, h.1.2⟩
  have hspec2 : Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v A2 pc) e := ⟨h.1.1, h.2⟩
  exact Tla.leadsTo_trans_entails (Tla.statePred (fun s : St => s.pc = 0))
    (Tla.statePred (fun s : St => s.pc = 1)) (Tla.statePred (fun s : St => s.pc = 2))
    e ⟨h01 e hspec1, h12 e hspec2⟩

end TlaDsl.Examples.TwoPhase
