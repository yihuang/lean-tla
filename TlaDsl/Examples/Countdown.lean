import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Liveness via a rank function: the countdown

The textbook *rank-function* liveness technique: to prove that a predicate
`P` eventually reaches `q`, exhibit a well-founded measure `f : σ → Nat`
that strictly decreases on every non-`q` step, then argue by well-founded
induction on `f`. This file runs the pattern on the simplest possible
protocol — a counter that decrements until it hits zero:

* `Next` decrements `i` while `0 < i` (stuttering otherwise);
* weak fairness on `Next` forces progress;
* the rank is the counter itself: `countdown_step` shows `i = n` leads to
  `i ≤ n - 1` (one WF1 application — the rank decreases by one), and
  `bounded_countdown` chains these by strong induction on `n`
  (well-foundedness of `Nat`) to get `i ≤ k ↝ i = 0`; `countdown_liveness`
  specializes to `i = k ↝ i = 0`, and `spec_liveness` packages it with the
  initial state.

The same pattern scales to protocols where progress is not one action per
state: the rank collapses a whole phase into a single WF1 step.
-/

namespace TlaDsl.Examples.Countdown

structure St where
  i : Nat
deriving Repr

tla_var St i

/-- Decrement the counter while it is positive. -/
@[simp] def Next : Tla.Action St :=
  [a| 0 < i ∧ i' = i - 1]

/-- The protocol starts the countdown at `k`. -/
@[simp] def Init (k : Nat) : Tla.StatePred St :=
  [p| i = k]

def Spec (k : Nat) : Tla.Pred St :=
  [t| Init k ∧ □[Next]_i]

/-! ## One WF1 step: the rank decreases -/

/-- WF1 with the rank: from `i = n` (`n > 0`), every `[Next]_i` step either
stays at `i = n` or reaches `i ≤ n - 1`, every `⟨Next⟩_i` step reaches
`i ≤ n - 1`, and `⟨Next⟩_i` is enabled. So `i = n` leads to `i ≤ n - 1`. -/
theorem countdown_step (n : Nat) (hn : 0 < n) :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next i) (Tla.WF_v Next i))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.i = n))
        (Tla.statePred (fun s : St => s.i ≤ n - 1))) := by
  tla_wf1
  · -- enabledness: decrement once
    intro s hs
    left
    refine ⟨{ i := n - 1 }, ?_⟩
    tla_unfold
    omega

/-! ## Strong induction on the rank: the countdown terminates -/

/-- The rank-function liveness theorem: under `□[Next]_i ∧ WF_i(Next)`,
`i ≤ k` leads to `i = 0`. One WF1 step reduces the rank, and strong
induction on `k` (well-foundedness of `Nat`) chains the steps: from
`i ≤ k' + 1`, either `i = k' + 1` (WF1 drops the rank to `≤ k'`, then the
hypothesis applies) or `i ≤ k'` already. -/
theorem bounded_countdown (k : Nat) :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next i) (Tla.WF_v Next i))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.i ≤ k))
        (Tla.statePred (fun s : St => s.i = 0))) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro e hSpec
      cases k with
      | zero =>
          -- `i ≤ 0` already satisfies the goal
          intro n hp
          refine ⟨0, ?_⟩
          have hz : (e n).i = 0 := by
            have hle : (e n).i ≤ 0 := by
              simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
            omega
          simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hz
      | succ k' =>
          -- one WF1 step drops the rank from `k' + 1` to `≤ k'`
          have hstep1 : Tla.leadsTo (Tla.statePred (fun s : St => s.i = k' + 1))
              (Tla.statePred (fun s : St => s.i ≤ k')) e := by
            simpa [Nat.add_sub_cancel] using countdown_step (k' + 1) (by omega) e hSpec
          -- induction hypothesis for the smaller bound
          have hih : Tla.leadsTo (Tla.statePred (fun s : St => s.i ≤ k'))
              (Tla.statePred (fun s : St => s.i = 0)) e := by
            exact ih k' (Nat.lt_succ_self k') e hSpec
          -- `i = k' + 1 ↝ i = 0` by chaining the WF1 step with the IH
          have hEq : Tla.leadsTo (Tla.statePred (fun s : St => s.i = k' + 1))
              (Tla.statePred (fun s : St => s.i = 0)) e := by
            tla_leads_to
          -- disjunction on the left: `i = k' + 1` or `i ≤ k'`
          have hSplit : Tla.leadsTo
              (Tla.statePred (fun s : St => s.i = k' + 1 ∨ s.i ≤ k'))
              (Tla.statePred (fun s : St => s.i = 0)) e := by
            tla_leads_to
          -- the goal: `i ≤ k' + 1`, which is exactly the disjunction
          intro n hp
          have hp' : (e n).i = k' + 1 ∨ (e n).i ≤ k' := by
            have hle : (e n).i ≤ k' + 1 := by
              simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
            rcases Nat.eq_or_lt_of_le hle with h | h
            · left
              exact h
            · right
              omega
          have hSp : (Tla.statePred (fun s : St => s.i = k' + 1 ∨ s.i ≤ k')) (e.drop n) := by
            simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp'
          rcases hSplit n hSp with ⟨j, hj⟩
          refine ⟨j, ?_⟩
          simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

/-- The countdown from a concrete value: `i = k` leads to `i = 0`. -/
theorem countdown_liveness (k : Nat) :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next i) (Tla.WF_v Next i))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.i = k))
        (Tla.statePred (fun s : St => s.i = 0))) := by
  intro e hSpec n hp
  have hle : Tla.leadsTo (Tla.statePred (fun s : St => s.i ≤ k))
      (Tla.statePred (fun s : St => s.i = 0)) e := bounded_countdown k e hSpec
  have hle' : (e n).i ≤ k := by
    have hk : (e n).i = k := by
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
    omega
  have hp' : (Tla.statePred (fun s : St => s.i ≤ k)) (e.drop n) := by
    simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hle'
  rcases hle n hp' with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

/-- The spec-level statement: with the initial state `i = k` and weak
fairness on `Next`, the countdown eventually reaches `i = 0`. -/
theorem spec_liveness (k : Nat) :
    Tla.Entails (Tla.tlaAnd (Tla.statePred (Init k))
      (Tla.tlaAnd (Tla.stutAlways Next i) (Tla.WF_v Next i)))
      (Tla.eventually (Tla.statePred (fun s : St => s.i = 0))) := by
  intro e h
  have hk : (e 0).i = k := by
    simpa [Tla.statePred, Init, Cslib.ωSequence.drop] using h.1
  have hle : Tla.leadsTo (Tla.statePred (fun s : St => s.i ≤ k))
      (Tla.statePred (fun s : St => s.i = 0)) e := bounded_countdown k e h.2
  rcases hle 0 (by
    simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using (by omega : (e 0).i ≤ k)) with ⟨j, hj⟩
  exact ⟨j, by
    simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj⟩

end TlaDsl.Examples.Countdown
