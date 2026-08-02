import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic

open scoped Tla

/-! # Liveness example: critical-section entry via WF1

A minimal protocol (`pc = 0` waiting, `pc = 1` critical). Weak fairness on
the `Enter` action forces progress: from `pc = 0` the process eventually
reaches `pc = 1`. The proof is a one-line application of the semantically
proved `wf1` rule.
-/

namespace TlaDsl.Examples.TicketLock

structure St where
  pc : Nat
  x : Nat
deriving Repr

@[simp] def pc : St → Nat := St.pc
@[simp] def x : St → Nat := St.x

@[simp] def Enter : Tla.Action St := [a| pc = 0 ∧ pc' = 1 ∧ x' = x]
@[simp] def Exit : Tla.Action St := [a| pc = 1 ∧ pc' = 0 ∧ x' = x]
@[simp] def Next : Tla.Action St :=
  [a| (pc = 0 ∧ pc' = 1 ∧ x' = x) ∨ (pc = 1 ∧ pc' = 0 ∧ x' = x)]

theorem hstep : ∀ s s', s.pc = 0 →
    Tla.StutAction Next pc s s' → s'.pc = 0 ∨ s'.pc = 1 := by
  intro s s' hs h
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2
    · right
      exact h1.2.1
    · omega
  · left
    omega

theorem haq : ∀ s s', s.pc = 0 → Tla.AngleAction Enter pc s s' → s'.pc = 1 := by
  intro s s' hs h
  tla_unfold
  exact h.1.2.1

theorem henable : ∀ s, s.pc = 0 → Tla.Enabled (Tla.AngleAction Enter pc) s ∨ s.pc = 1 := by
  intro s hs
  left
  refine ⟨{ pc := 1, x := s.x }, ?_⟩
  tla_unfold
  omega

/-- WF1 gives liveness: under `□[Next]_pc ∧ WF_pc(Enter)`, the process
eventually enters its critical section. -/
theorem ticket_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next pc) (Tla.WF_v Enter pc))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 0))
        (Tla.statePred (fun s : St => s.pc = 1))) :=
  Tla.wf1 (fun s : St => s.pc = 0) (fun s : St => s.pc = 1) Next Enter pc
    hstep haq henable

end TlaDsl.Examples.TicketLock
