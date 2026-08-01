import Leslie.Examples.AllGather
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## AllGather Liveness: Round Eventually Completes

    Under weak fairness of the round-step action, the AllGather protocol
    eventually completes one round. Combined with the safety proof
    `ag_completeness`, this gives: every process eventually knows about
    every other process.

    **Property**: `round < 1 ↝ round ≥ 1`

    This is a single WF1 application. The round step is always enabled
    (under reliable communication, we can always construct a valid
    successor state), so weak fairness guarantees eventual progress.
-/

open TLA

namespace AllGatherLiveness

variable (n : Nat)

/-! ### Fair spec -/

/-- The next-state relation of the AllGather round-based spec. -/
abbrev agNext := (AllGather.ag_spec n).toSpec.next

/-- Fair version of the AllGather spec: weak fairness on the round step. -/
def agFair : Spec (RoundState (Fin n) (Fin n → Bool)) where
  init := (AllGather.ag_spec n).toSpec.init
  next := agNext n
  fair := [agNext n]

/-! ### Enablement: the round step is always enabled -/

/-- Under reliable communication, the round step is always enabled:
    we can construct a successor state by delivering all messages. -/
theorem agNext_always_enabled (s : RoundState (Fin n) (Fin n → Bool)) :
    enabled (agNext n) s := by
  refine ⟨⟨s.round + 1, fun p => (AllGather.ag_alg n).update p (s.locals p)
    (delivered (AllGather.ag_alg n) s (fun _ _ => true) p)⟩, ?_⟩
  refine ⟨fun _ _ => true, ?_, ?_⟩
  · intro p q ; rfl
  · exact ⟨rfl, fun _ => rfl⟩

/-! ### Round step increments round counter -/

theorem agNext_inc_round {s s' : RoundState (Fin n) (Fin n → Bool)}
    (h : agNext n s s') : s'.round = s.round + 1 := by
  obtain ⟨_, _, hround, _⟩ := h
  exact hround

/-! ### WF1: round < 1 leads to round ≥ 1 -/

theorem round_progress :
    pred_implies (agFair n).formula
      (leads_to (state_pred (fun s : RoundState (Fin n) (Fin n → Bool) => s.round < 1))
                (state_pred (fun s : RoundState (Fin n) (Fin n → Bool) => s.round ≥ 1))) := by
  intro e ⟨_, hnext, hwf⟩
  -- Extract WF(agNext) from the single-element fairness list
  have hwf : weak_fairness (agNext n) e := by
    simp only [agFair, tla_bigwedge, Foldable.fold, tla_true] at hwf
    exact hwf.1
  -- Apply WF1
  apply wf1
    (state_pred (fun s : RoundState (Fin n) (Fin n → Bool) => s.round < 1))
    (state_pred (fun s : RoundState (Fin n) (Fin n → Bool) => s.round ≥ 1))
    (agNext n) (agNext n) e
  refine ⟨?safety, ?progress, ?enablement, hnext, hwf⟩
  case safety =>
    -- p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q
    intro m ⟨hp, hstep⟩
    have hinc := agNext_inc_round n hstep
    simp only [state_pred, later, tla_or, exec.drop, Nat.add_zero] at hp hinc ⊢
    right ; omega
  case progress =>
    -- p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q
    intro m ⟨hp, _, hstep⟩
    have hinc := agNext_inc_round n hstep
    simp only [state_pred, later, exec.drop, Nat.add_zero] at hp hinc ⊢
    omega
  case enablement =>
    intro m _
    simp only [state_pred, tla_enabled, exec.drop, tla_or] at *
    left ; exact agNext_always_enabled n _

/-! ### Main theorem: AllGather eventually completes -/

/-- Under weak fairness, the AllGather protocol eventually completes one round,
    after which every process knows about every other process. -/
theorem ag_eventually_complete :
    pred_implies (agFair n).formula
      (leads_to (state_pred (fun s : RoundState (Fin n) (Fin n → Bool) => s.round < 1))
                (state_pred (fun s : RoundState (Fin n) (Fin n → Bool) =>
                  ∀ p q, s.locals p q = true))) := by
  intro e hspec k hp
  -- Step 1: liveness — eventually round ≥ 1
  obtain ⟨j, hge⟩ := round_progress n e hspec k hp
  -- Step 2: safety — round ≥ 1 → all processes know all values
  have hsafety : (AllGather.ag_spec n).toSpec.safety e := by
    obtain ⟨hinit, hnext, _⟩ := hspec
    exact ⟨hinit, hnext⟩
  have hinv := AllGather.ag_completeness n e hsafety
  refine ⟨j, ?_⟩
  have hinv_at := hinv (k + j)
  simp only [state_pred, exec.drop, Nat.add_zero] at hinv_at hge ⊢
  exact hinv_at.2 hge

end AllGatherLiveness
