import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Meta
import TlaDsl.Tactic

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

@[simp] def pc0 : St → Nat := St.pc0
@[simp] def pc1 : St → Nat := St.pc1
@[simp] def turn : St → Nat := St.turn

@[simp] def Req0 : Tla.Action St := [a| pc0 = 0 ∧ pc0' = 1 ∧ pc1' = pc1 ∧ turn' = turn]
@[simp] def Enter0 : Tla.Action St := [a| pc0 = 1 ∧ turn = 0 ∧ pc0' = 2 ∧ pc1' = pc1 ∧ turn' = turn]
@[simp] def Exit0 : Tla.Action St := [a| pc0 = 2 ∧ pc0' = 0 ∧ pc1' = pc1 ∧ turn' = 1]
@[simp] def Req1 : Tla.Action St := [a| pc1 = 0 ∧ pc1' = 1 ∧ pc0' = pc0 ∧ turn' = turn]
@[simp] def Enter1 : Tla.Action St := [a| pc1 = 1 ∧ turn = 1 ∧ pc1' = 2 ∧ pc0' = pc0 ∧ turn' = turn]
@[simp] def Exit1 : Tla.Action St := [a| pc1 = 2 ∧ pc1' = 0 ∧ pc0' = pc0 ∧ turn' = 1]

@[simp] def Next : Tla.Action St := fun s s' =>
  Req0 s s' ∨ Enter0 s s' ∨ Exit0 s s' ∨ Req1 s s' ∨ Enter1 s s' ∨ Exit1 s s'

@[simp] def Init : Tla.StatePred St := [p| pc0 = 0 ∧ pc1 = 0 ∧ turn = 0]
@[simp] def Vars : St → Nat × Nat × Nat := fun s => (s.pc0, s.pc1, s.turn)

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_Vars]

/-- The inductive invariant: whoever is in the critical section holds `turn`. -/
def Inv : St → Prop := fun s => (s.pc0 = 2 → s.turn = 0) ∧ (s.pc1 = 2 → s.turn = 1)

theorem init_inv : ∀ s, Init s → Inv s := by
  intro s hs
  tla_unfold
  simp [Inv]
  omega

theorem step_inv : ∀ s s', Tla.StutAction Next Vars s s' → Inv s → Inv s' := by
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
  · omega

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

end TlaDsl.Examples.TwoProcessMutex

namespace TlaDsl.Examples.TwoPhase

structure St where
  pc : Nat
  x : Nat
deriving Repr

@[simp] def pc : St → Nat := St.pc
@[simp] def x : St → Nat := St.x

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
