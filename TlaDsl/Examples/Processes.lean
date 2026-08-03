import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Pretty
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Multithread-style state: `Nat → ProcState`

The typical TLA+ idiom of storing per-process state in a function is
supported directly. With `proc : St → Nat → ProcState`, a state predicate
reads `proc[i]`, an action reads the post state with `proc'[i]`, and the
`[proc EXCEPT ![i] = st]` update pattern is `proc' = Function.update proc i
st` (Lean's function update).

The example is a ticket protocol: process `i` may advance only when it
holds the ticket; the invariant is that every process is idle or running.
-/

namespace TlaDsl.Examples.Processes

structure ProcState where
  pc : Nat   -- 0 = idle, 1 = running
  done : Bool

structure St where
  proc : Nat → ProcState
  ticket : Nat

tla_var St proc ticket

@[simp] def Init : Tla.StatePred St := [p| ∀ i, proc[i].pc = 0 ∧ ticket = 0]

/-- Process `i` claims its turn: it must hold the ticket and be idle; after
the step it is running and the ticket moves to the next process. -/
@[simp] def Next (i : Nat) : Tla.Action St :=
  [a| ticket = i ∧ proc[i].pc = 0 ∧
      proc' = Function.update proc i { pc := 1, done := true } ∧
      ticket' = ticket + 1]

/-- Every process is idle or running. -/
@[simp] def Inv : Tla.StatePred St := [p| ∀ i, proc[i].pc = 0 ∨ proc[i].pc = 1]

def Spec (i : Nat) : Tla.Pred St := [t| Init ∧ □[Next i]_vars]

/-! ## The invariant is preserved by the step -/

theorem step_ok (i : Nat) : ∀ s s' : St, Next i s s' → Inv s → Inv s' := by
  intro s s' hnext hInv
  tla_unfold
  rcases hnext with ⟨_hticket, _hpc, hproc, _hticket'⟩
  intro j
  by_cases hji : j = i
  · subst j
    rw [hproc]
    simp [Function.update]
  · rw [hproc]
    simp [Function.update, hji]
    exact hInv j

/-! ## The step really updates process `i`'s slot -/

theorem next_updates_proc (i : Nat) : ∀ s s' : St, Next i s s' →
    proc s' i = { pc := 1, done := true } := by
  intro s s' hnext
  tla_unfold
  rcases hnext with ⟨_hticket, _hpc, hproc, _hticket'⟩
  rw [hproc]
  simp [Function.update]

/-! ## The spec entails the invariant (goal renders in TLA notation) -/

theorem inv_entailed (i : Nat) : Spec i ⊢ □ ⌜ Inv ⌝ := by
  unfold Spec
  tla_inv
  · intro s hs
    tla_unfold
    intro j
    exact Or.inl (hs j).1
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact step_ok i s s' hnext hInv
    · tla_unfold
      cases hstut
      exact hInv

end TlaDsl.Examples.Processes
