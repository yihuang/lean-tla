import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Ticket-lock liveness with an unbounded rank

The ticket lock's liveness argument is the textbook *rank-function* proof:
a waiting process with ticket `t` stands behind `t - served` other tickets,
the server serves them one at a time, and the *rank* `t - served` strictly
decreases until the process's turn. This file formalises the waiting-phase
core of that argument:

* the process waits (`pc = 1`) with ticket `t` while `served` advances
  (`Serve` — the server handing tickets to the processes ahead);
* when `served = t` the process enters the critical section (`Enter`,
  `pc = 2`);
* the rank is `rank s := s.t - s.served` — *unbounded* (the queue can be
  arbitrarily long), so the proof is well-founded induction on `Nat`:
  `ticket_base` handles rank 0 (weak fairness on `Enter`), `ticket_step`
  handles rank `n+1` (weak fairness on `Serve` decreases the rank), and
  `bounded_liveness` chains them; `ticket_liveness` then instantiates the
  bound at the current position, and `spec_liveness` packages it with the
  initial state.

The `Req`/`Exit` actions of a full ticket lock are elided: they do not
affect the waiting-phase progress, and the invariant `pc = 1 → served ≤ t`
(tickets are handed out in order, so a waiting process's ticket is never
behind the served one) is the only fact the proof needs about them.

The `P n` predicate — "waiting, with rank at most `n`" — is exactly the
rank-function pattern: each WF1 step either keeps `P n` or drops to
`P (n-1)`, and `q` (`pc = 2`) is the goal.
-/

namespace TlaDsl.Examples.TicketLock

structure St where
  pc : Nat
  t : Nat
  served : Nat
deriving Repr

tla_var St pc t served

/-- The server hands out the ticket currently being served (some process
ahead of ours leaves the critical section). Disabled when it is our turn. -/
@[simp] def Serve : Tla.Action St :=
  [a| ¬ (pc = 1 ∧ served = t) ∧ served' = served + 1 ∧ pc' = pc ∧ t' = t]

/-- Enter the critical section when our ticket is being served. -/
@[simp] def Enter : Tla.Action St :=
  [a| pc = 1 ∧ served = t ∧ pc' = 2 ∧ served' = served ∧ t' = t]

@[simp] def Next : Tla.Action St := fun s s' => Serve s s' ∨ Enter s s'

/-- The process starts waiting, with a valid (in-order) ticket. -/
@[simp] def Init : Tla.StatePred St :=
  [p| pc = 1 ∧ served ≤ t]

/-- While waiting, our ticket is never behind the served one. -/
@[simp] def Inv : St → Prop := fun s => s.pc = 1 → s.served ≤ s.t

/-- The progress rank: tickets still ahead of ours. -/
@[simp] def rank (s : St) : Nat := s.t - s.served

/-- Waiting, with rank at most `n`. -/
@[simp] def P (n : Nat) : St → Prop := fun s =>
  s.pc = 1 ∧ s.served ≤ s.t ∧ rank s ≤ n

/-- In the critical section. -/
@[simp] def q : St → Prop := fun s => s.pc = 2

/-! ## The invariant is inductive -/

theorem init_inv : ∀ s, Init s → Inv s := by
  intro s hs
  tla_unfold
  intro hpc
  exact hs.2

theorem step_inv : ∀ s s', Tla.StutAction Next vars s s' → Inv s → Inv s' := by
  intro s s' hstep hinv
  tla_unfold
  rcases hstep with hnext | hstut
  · rcases hnext with h1 | h2
    · -- Serve
      rcases h1 with ⟨hG, hS', hP', hT'⟩
      intro hpc'
      have hpc : s.pc = 1 := by simpa [hP'] using hpc'
      have hle : s.served ≤ s.t := hinv hpc
      have hlt : s.served < s.t := by
        by_contra hnot
        have heq : s.served = s.t := by omega
        exact hG hpc heq
      omega
    · -- Enter: pc becomes 2, invariant vacuous
      rcases h2 with ⟨hpc, hserved, hpc', hserved', ht'⟩
      intro hpc2
      omega
  · cases hstut
    exact hinv

theorem inv_invariant :
    Tla.Entails (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways Next vars))
      (Tla.always (Tla.statePred Inv)) := by
  tla_inv
  · exact init_inv
  · exact step_inv

/-! ## WF1 at rank 0: it is our turn -/

theorem hstep_base : ∀ s s', P 0 s → Tla.StutAction Next vars s s' → P 0 s' ∨ q s' := by
  intro s s' hp h
  rcases hp with ⟨hpc, hle, hr⟩
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2
    · -- Serve is disabled when it is our turn (served = t)
      rcases h1 with ⟨hG, hS', hP', hT'⟩
      exfalso
      have heq : s.served = s.t := by omega
      exact hG hpc heq
    · -- Enter reaches the critical section
      rcases h2 with ⟨hpc, hserved, hpc', hserved', ht'⟩
      right
      exact hpc'
  · -- stutter
    cases hstut
    left
    exact ⟨hpc, hle, hr⟩

theorem haq_base : ∀ s s', P 0 s → Tla.AngleAction Enter vars s s' → q s' := by
  intro s s' hp h
  tla_unfold
  rcases h with ⟨hA, hchg⟩
  rcases hA with ⟨hpc, hserved, hpc', hserved', ht'⟩
  exact hpc'

theorem henable_base : ∀ s, P 0 s → Tla.Enabled (Tla.AngleAction Enter vars) s ∨ q s := by
  intro s hp
  rcases hp with ⟨hpc, hle, hr⟩
  left
  refine ⟨{ pc := 2, t := s.t, served := s.served }, ?_⟩
  tla_unfold
  constructor
  · omega
  · intro hEq
    have hc : (2 : Nat) = s.pc := by simpa using congrArg St.pc hEq
    omega

/-- **Rank 0**: our ticket is being served, weak fairness on `Enter` puts us
in the critical section. -/
theorem ticket_base :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Enter vars))
      (Tla.leadsTo (Tla.statePred (P 0)) (Tla.statePred q)) := by
  exact Tla.wf1 (P 0) q Next Enter vars hstep_base haq_base henable_base

/-! ## WF1 at rank `n+1`: the server advances the queue -/

theorem hstep_step (n : Nat) : ∀ s s', P (n + 1) s → Tla.StutAction Next vars s s' →
    P (n + 1) s' ∨ (P n s' ∨ q s') := by
  intro s s' hp h
  rcases hp with ⟨hpc, hle, hr⟩
  tla_unfold
  rcases h with hnext | hstut
  · rcases hnext with h1 | h2
    · -- Serve: either our turn already (rank 0, already `P n`) or the rank
      -- strictly decreases to `≤ n`
      rcases h1 with ⟨hG, hS', hP', hT'⟩
      by_cases hEq : s.served = s.t
      · exfalso
        exact hG hpc hEq
      · right
        left
        constructor
        · exact hP'.trans hpc
        · constructor
          · have hlt : s.served < s.t := Nat.lt_of_le_of_ne hle hEq
            simpa [hS', hT'] using (Nat.succ_le_of_lt hlt)
          · have hdec : s.t - (s.served + 1) ≤ n := by omega
            simpa [hS', hT'] using hdec
    · -- Enter
      rcases h2 with ⟨hpc, hserved, hpc', hserved', ht'⟩
      right
      right
      exact hpc'
  · -- stutter
    cases hstut
    left
    exact ⟨hpc, hle, hr⟩

theorem haq_step (n : Nat) : ∀ s s', P (n + 1) s → Tla.AngleAction Serve vars s s' →
    P n s' ∨ q s' := by
  intro s s' hp h
  rcases hp with ⟨hpc, hle, hr⟩
  tla_unfold
  rcases h with ⟨hA, hchg⟩
  rcases hA with ⟨hG, hS', hP', hT'⟩
  left
  constructor
  · exact hP'.trans hpc
  · constructor
    · have hlt : s.served < s.t := by
        by_contra hnot
        have heq : s.served = s.t := by omega
        exact hG hpc heq
      simpa [hS', hT'] using (Nat.succ_le_of_lt hlt)
    · have hdec : s.t - (s.served + 1) ≤ n := by omega
      simpa [hS', hT'] using hdec

theorem henable_step (n : Nat) : ∀ s, P (n + 1) s →
    Tla.Enabled (Tla.AngleAction Serve vars) s ∨ (P n s ∨ q s) := by
  intro s hp
  rcases hp with ⟨hpc, hle, hr⟩
  by_cases hEq : s.served = s.t
  · -- our turn already: `P n` holds
    right
    left
    constructor
    · exact hpc
    · constructor
      · exact hle
      · simpa [rank] using (by omega : s.t - s.served ≤ n)
  · -- someone is ahead: the server is enabled and advances the queue
    left
    refine ⟨{ pc := s.pc, t := s.t, served := s.served + 1 }, ?_⟩
    tla_unfold
    constructor
    · tla_grind
    · intro hEq'
      have hc : s.served + 1 = s.served := by simpa using congrArg St.served hEq'
      omega

/-- **Rank `n+1`**: weak fairness on `Serve` advances the queue, so the rank
drops to `≤ n` (or we were already that close). -/
theorem ticket_step (n : Nat) :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.WF_v Serve vars))
      (Tla.leadsTo (Tla.statePred (P (n + 1)))
        (Tla.statePred (fun s => P n s ∨ q s))) := by
  exact Tla.wf1 (P (n + 1)) (fun s => P n s ∨ q s) Next Serve vars
    (hstep_step n) (haq_step n) (henable_step n)

/-! ## Well-founded induction on the rank -/

/-- Fairness on `Enter` and `Serve`. -/
def FairHyp : Tla.Pred St :=
  Tla.tlaAnd (Tla.stutAlways Next vars) (Tla.tlaAnd (Tla.WF_v Serve vars) (Tla.WF_v Enter vars))

/-- The rank-function theorem: with rank at most `k`, the process eventually
enters the critical section. One WF1 step reduces the rank; strong induction
on `k` (well-foundedness of `Nat`) chains the steps. -/
theorem bounded_liveness (k : Nat) :
    Tla.Entails FairHyp (Tla.leadsTo (Tla.statePred (P k)) (Tla.statePred q)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro e hF
      cases k with
      | zero =>
          exact ticket_base e ⟨hF.1, hF.2.2⟩
      | succ k' =>
          have hstep1 : Tla.leadsTo (Tla.statePred (P (k' + 1)))
              (Tla.statePred (fun s => P k' s ∨ q s)) e :=
            ticket_step k' e ⟨hF.1, hF.2.1⟩
          have hih : Tla.leadsTo (Tla.statePred (P k')) (Tla.statePred q) e :=
            ih k' (Nat.lt_succ_self k') e hF
          have hq : Tla.leadsTo (Tla.statePred q) (Tla.statePred q) e := by
            intro n hq'
            refine ⟨0, ?_⟩
            simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hq'
          have hor : Tla.leadsTo (Tla.statePred (fun s => P k' s ∨ q s))
              (Tla.statePred q) e := by
            tla_leads_to
          have hchain : Tla.leadsTo (Tla.statePred (P (k' + 1))) (Tla.statePred q) e := by
            tla_leads_to
          exact hchain

/-- **Ticket-lock liveness**: a waiting process eventually enters the
critical section. The rank at the current position is finite (`t - served`),
so the bounded theorem applies. -/
theorem ticket_liveness :
    Tla.Entails (Tla.tlaAnd FairHyp (Tla.always (Tla.statePred Inv)))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 1)) (Tla.statePred q)) := by
  intro e h n hp
  rcases h with ⟨hF, hInv⟩
  have hInvAt : Inv (e n) := by
    simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInv n
  have hpc : (e n).pc = 1 := by
    simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
  have hle : (e n).served ≤ (e n).t := hInvAt hpc
  let k := (e n).t - (e n).served
  have hb : Tla.leadsTo (Tla.statePred (P k)) (Tla.statePred q) e := bounded_liveness k e hF
  have hp' : (Tla.statePred (P k)) (e.drop n) := by
    simpa [P, rank, Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using ⟨hpc, hle, by omega⟩
  rcases hb n hp' with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

/-- The spec-level statement: with the initial state (waiting, valid ticket),
the process eventually enters the critical section. -/
theorem spec_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.tlaAnd (Tla.statePred Init) FairHyp)
        (Tla.always (Tla.statePred Inv)))
      (Tla.eventually (Tla.statePred q)) := by
  intro e h
  have hInit : (e 0).pc = 1 := by
    have h0 : Init (e 0) := by simpa [Tla.statePred, Cslib.ωSequence.drop] using h.1.1
    exact h0.1
  have htl : Tla.leadsTo (Tla.statePred (fun s : St => s.pc = 1)) (Tla.statePred q) e :=
    ticket_liveness e ⟨h.1.2, h.2⟩
  rcases htl 0 (by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hInit) with ⟨j, hj⟩
  exact ⟨j, by
    simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj⟩

end TlaDsl.Examples.TicketLock
