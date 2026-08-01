import Leslie.Examples.BallotLeader
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## BallotLeader Liveness: Rounds Eventually Complete

    Under weak fairness of the next-step action, the ballot-leader
    protocol eventually completes both rounds (reaches round >= 2).

    **Property**: `round = 0 ↝ round >= 2`

    We prove this via two WF1 applications composed with leads_to_trans:
    1. round = 0 ↝ round >= 1  (stepNew is always enabled at round 0)
    2. round = 1 ↝ round >= 2  (stepAck is always enabled at round 1)
-/

open TLA BallotLeader

namespace BallotLeaderLiveness

variable {n : Nat}

/-! ### Fair spec -/

/-- The ballot leader spec augmented with weak fairness on the next action. -/
def ballotLeaderFair (n : Nat) : Spec (GState n) where
  init := (ballotLeaderSpec n).init
  next := (ballotLeaderSpec n).next
  fair := [(ballotLeaderSpec n).next]

abbrev blNext (n : Nat) := (ballotLeaderSpec n).next

/-! ### Enablement lemmas -/

/-- At round 0, the next action is enabled: stepNew can fire with any oracle and HO. -/
theorem next_enabled_round0 (s : GState n) (h : s.round = 0) :
    enabled (blNext n) s := by
  let ho : HOCollection (Fin n) := fun _ _ => false
  let oracle : Fin n → Bool := fun _ => false
  let s' : GState n :=
    { round := 1,
      locals := fun p =>
        let msgs := deliveredMsgs' n (fun q => if oracle q then .bid q else .noBid) ho p
        let bids := collectBids n msgs
        { (s.locals p) with picked := List.minFin? bids } }
  exact ⟨s', Or.inl ⟨ho, oracle, h, rfl, fun _ => rfl⟩⟩

/-- At round 1, the next action is enabled: stepAck can fire with any HO. -/
theorem next_enabled_round1 (s : GState n) (h : s.round = 1) :
    enabled (blNext n) s := by
  let ho : HOCollection (Fin n) := fun _ _ => false
  let s' : GState n :=
    { round := 2,
      locals := fun p =>
        let send_fn := fun q => match (s.locals q).picked with
          | some c => Msg.pick c
          | none   => Msg.noPick
        let msgs := deliveredMsgs' n send_fn ho p
        let picks := collectPicks n msgs
        { picked := (s.locals p).picked, leader := findMajority n picks } }
  exact ⟨s', Or.inr (Or.inl ⟨ho, h, rfl, fun _ => rfl⟩)⟩

/-- At round >= 2, the next action is enabled: stepDone fires as stutter. -/
theorem next_enabled_round_ge2 (s : GState n) (h : s.round ≥ 2) :
    enabled (blNext n) s :=
  ⟨s, Or.inr (Or.inr ⟨h, rfl⟩)⟩

/-- The next action is always enabled. -/
theorem next_always_enabled (s : GState n) :
    enabled (blNext n) s := by
  by_cases h0 : s.round = 0
  · exact next_enabled_round0 s h0
  · by_cases h1 : s.round = 1
    · exact next_enabled_round1 s h1
    · exact next_enabled_round_ge2 s (by omega)

/-! ### Round step lemmas -/

/-- Any next step from round 0 goes to round >= 1. -/
theorem round0_step {s s' : GState n}
    (hr : s.round = 0) (h : blNext n s s') : s'.round ≥ 1 := by
  rcases h with ⟨ho, oracle, h0, h1, _⟩ | ⟨ho, h0, h1, _⟩ | ⟨h0, heq⟩
  · omega
  · omega
  · omega

/-- Any next step from round 1 goes to round >= 2. -/
theorem round1_step {s s' : GState n}
    (hr : s.round = 1) (h : blNext n s s') : s'.round ≥ 2 := by
  rcases h with ⟨ho, oracle, h0, h1, _⟩ | ⟨ho, h0, h1, _⟩ | ⟨h0, heq⟩
  · omega
  · omega
  · omega

/-! ### WF1: round 0 ↝ round >= 1 -/

theorem round0_to_ge1 :
    pred_implies (ballotLeaderFair n).formula
      (leads_to (state_pred (fun s : GState n => s.round = 0))
                (state_pred (fun s : GState n => s.round ≥ 1))) := by
  intro e ⟨_, hnext, hwf⟩
  have hwf : weak_fairness (blNext n) e := by
    simp only [ballotLeaderFair, tla_bigwedge, Foldable.fold, tla_true] at hwf
    exact hwf.1
  apply wf1
    (state_pred (fun s : GState n => s.round = 0))
    (state_pred (fun s : GState n => s.round ≥ 1))
    (blNext n) (blNext n) e
  refine ⟨?safety, ?progress, ?enablement, hnext, hwf⟩
  case safety =>
    intro m ⟨hp, hstep⟩
    simp only [action_pred, state_pred, exec.drop] at hp hstep ⊢
    right ; exact round0_step hp hstep
  case progress =>
    intro m ⟨hp, _, hstep⟩
    simp only [action_pred, state_pred, exec.drop] at hp hstep ⊢
    exact round0_step hp hstep
  case enablement =>
    intro m _
    simp only [state_pred, tla_enabled, exec.drop, tla_or] at *
    left ; exact next_always_enabled _

/-! ### WF1: round 1 ↝ round >= 2 -/

theorem round1_to_ge2 :
    pred_implies (ballotLeaderFair n).formula
      (leads_to (state_pred (fun s : GState n => s.round = 1))
                (state_pred (fun s : GState n => s.round ≥ 2))) := by
  intro e ⟨_, hnext, hwf⟩
  have hwf : weak_fairness (blNext n) e := by
    simp only [ballotLeaderFair, tla_bigwedge, Foldable.fold, tla_true] at hwf
    exact hwf.1
  apply wf1
    (state_pred (fun s : GState n => s.round = 1))
    (state_pred (fun s : GState n => s.round ≥ 2))
    (blNext n) (blNext n) e
  refine ⟨?safety, ?progress, ?enablement, hnext, hwf⟩
  case safety =>
    intro m ⟨hp, hstep⟩
    simp only [action_pred, state_pred, exec.drop] at hp hstep ⊢
    right ; exact round1_step hp hstep
  case progress =>
    intro m ⟨hp, _, hstep⟩
    simp only [action_pred, state_pred, exec.drop] at hp hstep ⊢
    exact round1_step hp hstep
  case enablement =>
    intro m _
    simp only [state_pred, tla_enabled, exec.drop, tla_or] at *
    left ; exact next_always_enabled _

/-! ### Composition: round 0 ↝ round >= 2 -/

/-- Helper: round >= 1 ↝ round >= 2 (case split on round = 1 vs round >= 2). -/
theorem round_ge1_to_ge2 :
    pred_implies (ballotLeaderFair n).formula
      (leads_to (state_pred (fun s : GState n => s.round ≥ 1))
                (state_pred (fun s : GState n => s.round ≥ 2))) := by
  intro e hΓ k hp
  simp only [state_pred, exec.drop] at hp
  by_cases heq : (e.drop k 0).round = 1
  · have h1 : state_pred (fun s : GState n => s.round = 1) (e.drop k) := by
      simp only [state_pred, exec.drop] ; exact heq
    exact round1_to_ge2 e hΓ k h1
  · exact ⟨0, by simp only [state_pred, exec.drop, Nat.add_zero] at hp heq ⊢ ; omega⟩

/-- **Main theorem**: under weak fairness, the protocol eventually
    completes both rounds. -/
theorem rounds_complete :
    pred_implies (ballotLeaderFair n).formula
      (leads_to (state_pred (fun s : GState n => s.round = 0))
                (state_pred (fun s : GState n => s.round ≥ 2))) := by
  intro e hΓ k hp
  obtain ⟨k1, hk1⟩ := round0_to_ge1 e hΓ k hp
  -- hk1 : exec.drop k1 (exec.drop k e) |=tla= ...
  -- Need to convert to exec.drop (k + k1) e
  rw [exec.drop_drop] at hk1
  obtain ⟨k2, hk2⟩ := round_ge1_to_ge2 e hΓ (k + k1) hk1
  rw [exec.drop_drop] at hk2
  exact ⟨k1 + k2, by rw [exec.drop_drop, ← Nat.add_assoc] ; exact hk2⟩

end BallotLeaderLiveness
