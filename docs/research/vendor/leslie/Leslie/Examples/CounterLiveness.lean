import Leslie.Examples.CounterRefinement
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Counter Liveness: First Liveness Proof in Leslie

    The concrete counter from `CounterRefinement` increments by 1 each step.
    Under weak fairness of the (single) next-step action, the counter
    eventually exceeds any bound N.

    **Property**: `∀ N, counter < N ↝ counter ≥ N`

    Demonstrates: WF1 application, leads_to composition by induction,
    extracting weak fairness from `Spec.formula`.
-/

open TLA

namespace CounterLiveness

/-! ### Fair spec -/

def concreteFair : Spec (Nat × Bool) where
  init := CounterRefinement.concrete.init
  next := CounterRefinement.concrete.next
  fair := [CounterRefinement.concrete.next]

abbrev cNext := CounterRefinement.concrete.next

/-! ### Basic action lemmas -/

theorem next_always_enabled (s : Nat × Bool) : enabled cNext s := by
  cases hs : s.2
  · exact ⟨(s.1 + 1, true), Or.inl ⟨hs, rfl⟩⟩
  · exact ⟨(s.1 + 1, false), Or.inr ⟨hs, rfl⟩⟩

theorem next_increases {s s' : Nat × Bool} (h : cNext s s') : s'.1 = s.1 + 1 := by
  simp [cNext, CounterRefinement.concrete] at h
  rcases h with ⟨_, hs'⟩ | ⟨_, hs'⟩ <;> simp_all

/-! ### WF1: counter at value k leads to counter ≥ k + 1

    We apply the `wf1` rule at the execution level.
    The key pattern: extract □⟨next⟩ and WF(a) from `Spec.formula`,
    verify the three state-level premises, then apply `wf1`. -/

theorem step_progress (k : Nat) :
    pred_implies concreteFair.formula
      (leads_to (state_pred (fun s : Nat × Bool => s.1 = k))
                (state_pred (fun s : Nat × Bool => s.1 ≥ k + 1))) := by
  intro e ⟨_, hnext, hwf⟩
  -- Extract WF(cNext) from the single-element fairness list
  have hwf : weak_fairness cNext e := by
    simp only [concreteFair, tla_bigwedge, Foldable.fold, tla_true] at hwf
    exact hwf.1
  -- Apply WF1 rule
  apply wf1
    (state_pred (fun s : Nat × Bool => s.1 = k))
    (state_pred (fun s : Nat × Bool => s.1 ≥ k + 1))
    cNext cNext e
  refine ⟨?safety, ?progress, ?enablement, hnext, hwf⟩
  case safety =>
    intro m ⟨hp, hstep⟩
    right
    simp only [action_pred, state_pred, exec.drop, later, Nat.add_zero] at hp hstep ⊢
    have hinc := next_increases hstep ; omega
  case progress =>
    intro m ⟨hp, _, hstep⟩
    simp only [action_pred, state_pred, exec.drop, later, Nat.add_zero] at hp hstep ⊢
    have hinc := next_increases hstep ; omega
  case enablement =>
    -- p ⇒ Enabled(a) ∨ q
    intro m _
    simp only [state_pred, tla_enabled, exec.drop, tla_or] at *
    left ; exact next_always_enabled _

/-! ### Composition helper -/

private theorem chain2 {Γ : pred (Nat × Bool)} {p q r : pred (Nat × Bool)}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r)) :
    pred_implies Γ (leads_to p r) :=
  fun e hΓ => leads_to_trans p q r e (h1 e hΓ) (h2 e hΓ)

/-! ### Counter ≥ n leads to counter ≥ n + 1

    If the counter is already > n, we're done immediately.
    If the counter equals n, apply step_progress. -/

private theorem ge_step (n : Nat) :
    pred_implies concreteFair.formula
      (leads_to (state_pred (fun s : Nat × Bool => s.1 ≥ n))
                (state_pred (fun s : Nat × Bool => s.1 ≥ n + 1))) := by
  intro e hΓ k hp
  -- hp : (≥ n) at e.drop k
  -- case split on whether it's exactly n or already ≥ n+1
  have hp_val : (e.drop k 0).1 ≥ n := hp
  by_cases heq : (e.drop k 0).1 = n
  · -- counter = n: use step_progress to get ≥ n+1
    exact step_progress n e hΓ k (show state_pred (fun s => s.1 = n) (e.drop k) from heq)
  · -- counter > n: already done
    exact ⟨0, show (e.drop (k + 0) 0).1 ≥ n + 1 by simp; omega⟩

/-! ### From ≥ 0 to ≥ N via induction -/

theorem counter_reaches (N : Nat) :
    pred_implies concreteFair.formula
      (leads_to (state_pred (fun s : Nat × Bool => s.1 ≥ 0))
                (state_pred (fun s : Nat × Bool => s.1 ≥ N))) := by
  induction N with
  | zero =>
    -- ≥ 0 ↝ ≥ 0 is trivial (immediate)
    intro e _ k hp ; exact ⟨0, hp⟩
  | succ n ih =>
    exact chain2 ih (ge_step n)

/-! ### Main theorem: counter below N eventually reaches ≥ N -/

theorem counter_eventually_reaches (N : Nat) :
    pred_implies concreteFair.formula
      (leads_to (state_pred (fun s : Nat × Bool => s.1 < N))
                (state_pred (fun s : Nat × Bool => s.1 ≥ N))) := by
  intro e hΓ k hp
  -- Weaken: s.1 < N implies s.1 ≥ 0
  have hge0 : (state_pred (fun s : Nat × Bool => s.1 ≥ 0)) (e.drop k) := by
    simp [state_pred, exec.drop]
  exact counter_reaches N e hΓ k hge0

end CounterLiveness
