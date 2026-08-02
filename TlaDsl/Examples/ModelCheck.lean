import TlaDsl.ModelCheck

/-! # Finite-state model checking: a two-process mutex

The whole spec is finite (`pc0 : Fin 3`, `pc1 : Fin 3`, `turn : Fin 2`), so
the invariant can be discharged by exhaustive reachable-state checking with
`native_decide` — no hand proof needed. `mcInvariant_sound` turns the check
into a theorem over all behaviors, and `mcEntails` gives the same result in
DSL form (`Init ∧ □[Next]_turn ⊢ □Inv`).
-/

namespace Tla
namespace ModelCheckExample

/-- Program counters: 0 idle, 1 waiting, 2 critical. -/
abbrev Idle : Fin 3 := 0
abbrev Wait : Fin 3 := 1
abbrev Crit : Fin 3 := 2

/-- The finite state: two processes plus a turn bit. -/
structure St where
  pc0 : Fin 3
  pc1 : Fin 3
  turn : Fin 2
deriving DecidableEq, Repr

instance : Fintype St := Fintype.ofEquiv (Fin 3 × Fin 3 × Fin 2) {
  toFun := fun p => { pc0 := p.1, pc1 := p.2.1, turn := p.2.2 }
  invFun := fun s => (s.pc0, s.pc1, s.turn)
  left_inv := by intro p; rcases p with ⟨a, b, c⟩; rfl
  right_inv := by intro s; cases s; rfl
}

/-- Both processes start idle, turn on process 0. -/
def init (s : St) : Prop := s.pc0 = Idle ∧ s.pc1 = Idle ∧ s.turn = 0

/-- The transitions: request, enter (with the turn), exit (handing over the
turn). -/
def next (s s' : St) : Prop :=
  (s.pc0 = Idle ∧ s'.pc0 = Wait ∧ s'.pc1 = s.pc1 ∧ s'.turn = s.turn) ∨
  (s.pc0 = Wait ∧ s.turn = 0 ∧ s'.pc0 = Crit ∧ s'.pc1 = s.pc1 ∧ s'.turn = s.turn) ∨
  (s.pc0 = Crit ∧ s'.pc0 = Idle ∧ s'.turn = 1 ∧ s'.pc1 = s.pc1) ∨
  (s.pc1 = Idle ∧ s'.pc1 = Wait ∧ s'.pc0 = s.pc0 ∧ s'.turn = s.turn) ∨
  (s.pc1 = Wait ∧ s.turn = 1 ∧ s'.pc1 = Crit ∧ s'.pc0 = s.pc0 ∧ s'.turn = s.turn) ∨
  (s.pc1 = Crit ∧ s'.pc1 = Idle ∧ s'.turn = 0 ∧ s'.pc0 = s.pc0)

/-- Mutual exclusion. -/
def inv (s : St) : Prop := ¬ (s.pc0 = Crit ∧ s.pc1 = Crit)

instance : DecidablePred init := fun s => by unfold init; infer_instance
instance : DecidableRel next := fun s s' => by unfold next; infer_instance
instance : DecidablePred inv := fun s => by unfold inv; infer_instance

/-- The model check passes, so the invariant holds on every behavior. -/
example : mcInvariant init next inv = true := by
  native_decide

example : ∀ e : Behavior St, init (e 0) → (∀ n, next (e n) (e (n + 1))) → ∀ n, inv (e n) :=
  mcInvariant_sound init next inv (by native_decide)

/-- The same invariant as a DSL theorem, with true stuttering steps
(`v = id`, so `Unchanged v` means the whole state stays):
`Init ∧ □[Next]_id ⊢ □Inv`. -/
example : Entails (tlaAnd (statePred init) (stutAlways next (fun s : St => s)))
    (always (statePred inv)) := by
  apply mcEntails init next (fun s : St => s) inv
  native_decide

/-! ## Counterexamples: a buggy variant -/

/-- The state enumeration used by the counterexample search. -/
def allStates : List St :=
  List.flatMap (fun a : Fin 3 =>
    List.flatMap (fun b : Fin 3 =>
      List.map (fun c : Fin 2 => { pc0 := a, pc1 := b, turn := c }) (List.finRange 2))
      (List.finRange 3))
    (List.finRange 3)

/-- A buggy variant: process 1 may enter the critical section without the
turn, breaking mutual exclusion. -/
def nextBuggy (s s' : St) : Prop :=
  (s.pc0 = Idle ∧ s'.pc0 = Wait ∧ s'.pc1 = s.pc1 ∧ s'.turn = s.turn) ∨
  (s.pc0 = Wait ∧ s.turn = 0 ∧ s'.pc0 = Crit ∧ s'.pc1 = s.pc1 ∧ s'.turn = s.turn) ∨
  (s.pc0 = Crit ∧ s'.pc0 = Idle ∧ s'.turn = 1 ∧ s'.pc1 = s.pc1) ∨
  (s.pc1 = Idle ∧ s'.pc1 = Wait ∧ s'.pc0 = s.pc0 ∧ s'.turn = s.turn) ∨
  (s.pc1 = Wait ∧ s'.pc1 = Crit ∧ s'.pc0 = s.pc0 ∧ s'.turn = s.turn) ∨
  (s.pc1 = Crit ∧ s'.pc1 = Idle ∧ s'.turn = 0 ∧ s'.pc0 = s.pc0)

instance : DecidableRel nextBuggy := fun s s' => by unfold nextBuggy; infer_instance

/-- The buggy check fails... -/
example : mcInvariant init nextBuggy inv = false := by
  native_decide

-- ...and the counterexample search finds a trace: both processes end up in
-- the critical section.
#eval! mcTrace allStates init nextBuggy inv

/-! ## Liveness: `P ↝ Q` -/

/-- Process 0 enters the critical section as soon as it holds the turn. -/
example : mcLeadsTo init next (fun s => s.pc0 = Wait ∧ s.turn = 0)
    (fun s => s.pc0 = Crit) = true := by
  native_decide

example : ∀ e : Behavior St, init (e 0) → (∀ n, next (e n) (e (n + 1))) →
    leadsTo (statePred (fun s => s.pc0 = Wait ∧ s.turn = 0))
      (statePred (fun s => s.pc0 = Crit)) e :=
  mcLeadsTo_sound init next (fun s => s.pc0 = Wait ∧ s.turn = 0)
    (fun s => s.pc0 = Crit) (by native_decide)

-- The DSL form (`mcEntailsLeadsTo`) needs a fairness assumption: under
-- `□[Next]_v` an infinite stutter is a legal behavior, so `P ↝ Q` without
-- fairness is false whenever P can stutter forever. The plain-`next` check
-- above is the fairness-free case.

-- The buggy spec breaks process-0's eventual entry (process 1 can hog the
-- critical section forever).
#eval mcLeadsTo init nextBuggy (fun _ : St => True) (fun s => s.pc0 = Crit)

end ModelCheckExample
end Tla
