import Leslie.Refinement
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Probe Counter Liveness: Validating leads_to_via_nat

    A simple countdown protocol: state is a Nat counter.
    One fair action decrements the counter (if > 0).
    Under weak fairness, the counter eventually reaches 0.

    **Property**: `counter > 0 ↝ counter = 0`

    This validates the `leads_to_via_nat` well-founded induction rule.
    The pattern transfers to TileLink's probing_leads_to_grantReady proof
    (where the "counter" is |{j | probesRemaining j = true}|).
-/

open TLA

namespace ProbeCounter

/-! ### Spec: state = Nat, action = decrement -/

def decrement (s s' : Nat) : Prop := s > 0 ∧ s' = s - 1

def countdownSpec : Spec Nat where
  init := fun _s => True
  next := decrement
  fair := [decrement]

/-! ### Basic lemmas -/

theorem decrement_enabled_of_pos {s : Nat} (h : s > 0) : enabled decrement s :=
  ⟨s - 1, h, rfl⟩

theorem decrement_decreases {s s' : Nat} (h : decrement s s') : s' < s := by
  rcases h with ⟨hpos, hs'⟩; omega

/-! ### Main theorem using leads_to_via_nat

    Property: counter > 0 ↝ counter = 0.
    Measure: the counter value itself.
    Each decrement step decreases the measure by 1. -/

theorem countdown_reaches_zero :
    pred_implies countdownSpec.formula
      (leads_to (state_pred (fun s : Nat => s > 0))
                (state_pred (fun s : Nat => s = 0))) := by
  -- Use leads_to_via_nat with μ = state value
  apply leads_to_via_nat (fun e => e 0)
  · -- Step case: k > 0, counter = k ↝ (counter = 0) ∨ (counter > 0 ∧ counter < k)
    intro k hk e ⟨_, hnext, hwf⟩ i hp hμ
    -- Extract WF(decrement) from fairness
    have hwf : weak_fairness decrement e := by
      simp only [countdownSpec, tla_bigwedge, Foldable.fold, tla_true] at hwf
      exact hwf.1
    -- Use WF1 on the original execution to get one decrement step
    -- WF1 gives: (counter > 0 ∧ counter = k) ↝ (counter = 0 ∨ (counter > 0 ∧ counter < k))
    have h1 : leads_to
        (fun e => e 0 > 0 ∧ e 0 = k)
        (fun e => e 0 = 0 ∨ (e 0 > 0 ∧ e 0 < k))
        e := by
      apply wf1 _ _ decrement decrement e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: p ∧ next → ◯p ∨ ◯q. After decrement, counter changes → always ◯q.
        intro m ⟨⟨hp', hcount⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, decrement] at *
        rcases hstep with ⟨hpos, hs'⟩
        right
        by_cases h0 : e m - 1 = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Progress: p ∧ next ∧ a → ◯q
        intro m ⟨⟨hp', hcount⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, decrement] at *
        rcases hstep with ⟨hpos, hs'⟩
        by_cases h0 : e m - 1 = 0
        · left; rw [hs']; exact h0
        · right; constructor
          · rw [hs']; omega
          · rw [hs', hcount]; omega
      · -- Enablement: p → Enabled a ∨ q
        intro m ⟨hp', _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact decrement_enabled_of_pos hp'
    -- Apply leads_to at position i
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ⟩
    simp only [exec.drop_drop] at hj
    rcases hj with hq | ⟨hp'', hlt⟩
    · exact ⟨j, Or.inl hq⟩
    · exact ⟨j, Or.inr ⟨hp'', hlt⟩⟩
  · -- Base case: counter = 0 → counter > 0 is false → contradiction
    intro e _ i hp hμ
    -- hp : (e.drop i) 0 > 0, hμ : (e.drop i) 0 = 0 → contradiction
    simp only [state_pred, exec.drop] at hp hμ
    omega

end ProbeCounter

/-! ## Variant 1: Stutter + Decrement

    Two actions: `stutter` (s' = s) and `decrement` (s' = s - 1).
    The combined next-step is their disjunction. Only `decrement` is fair.
    Stutter steps can happen arbitrarily often but don't block progress.

    **Property**: `counter > 0 ↝ counter = 0`

    This is closer to TileLink where many actions leave the probe count
    unchanged and only specific actions (recvProbeAck) decrease it. -/

namespace StutterDecrement

def stutter (s s' : Nat) : Prop := s' = s
def decrement (s s' : Nat) : Prop := s > 0 ∧ s' = s - 1
def next (s s' : Nat) : Prop := stutter s s' ∨ decrement s s'

def spec : Spec Nat where
  init := fun _ => True
  next := next
  fair := [decrement]  -- only decrement is fair; stutter can starve

theorem decrement_enabled_of_pos {s : Nat} (h : s > 0) : enabled decrement s :=
  ⟨s - 1, h, rfl⟩

theorem countdown_reaches_zero :
    pred_implies spec.formula
      (leads_to (state_pred (fun s : Nat => s > 0))
                (state_pred (fun s : Nat => s = 0))) := by
  apply leads_to_via_nat (fun e => e 0)
  · -- Step case: k > 0
    intro k hk e ⟨_, hnext, hwf⟩ i hp hμ
    have hwf : weak_fairness decrement e := by
      simp only [spec, tla_bigwedge, Foldable.fold, tla_true] at hwf; exact hwf.1
    -- WF1 with next = stutter ∨ decrement, fair action = decrement
    have h1 : leads_to
        (fun e => e 0 > 0 ∧ e 0 = k)
        (fun e => e 0 = 0 ∨ (e 0 > 0 ∧ e 0 < k))
        e := by
      apply wf1 _ _ next decrement e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: stutter preserves p; decrement gives q
        intro m ⟨⟨hp', hcount⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, next] at *
        rcases hstep with hstut | hdec
        · -- Stutter: s' = s → p preserved
          left; rw [stutter] at hstut; rw [hstut]; exact ⟨hp', hcount⟩
        · -- Decrement: counter changes → q
          right; rcases hdec with ⟨hpos, hs'⟩
          by_cases h0 : e m - 1 = 0
          · left; rw [hs']; exact h0
          · right; rw [hs', hcount]; omega
      · -- Progress: decrement fires → q
        intro m ⟨⟨hp', hcount⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, decrement] at *
        rcases hstep with ⟨hpos, hs'⟩
        by_cases h0 : e m - 1 = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Enablement: counter > 0 → decrement enabled
        intro m ⟨hp', _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact decrement_enabled_of_pos hp'
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ⟩
    simp only [exec.drop_drop] at hj
    rcases hj with hq | ⟨hp'', hlt⟩
    · exact ⟨j, Or.inl hq⟩
    · exact ⟨j, Or.inr ⟨hp'', hlt⟩⟩
  · -- Base case
    intro e _ i hp hμ
    simp only [state_pred, exec.drop] at hp hμ; omega

end StutterDecrement

/-! ## Variant 2: Stutter + Non-deterministic Decrement

    Two actions: `stutter` (s' = s) and `ndDecrement` (s' = s - d for
    non-deterministic d ∈ [1, s]). Only ndDecrement is fair.

    **Property**: `counter > 0 ↝ counter = 0`

    Combines both patterns: stutter-resilience and non-deterministic jumps.
    This is the closest model to TileLink probing, where most actions leave
    the probe count unchanged and the decrement action (recvProbeAck) may
    process probes in varying order. -/

namespace NondetDecrement

def stutter (s s' : Nat) : Prop := s' = s
def ndDecrement (s s' : Nat) : Prop := ∃ d, d ≥ 1 ∧ d ≤ s ∧ s' = s - d
def next (s s' : Nat) : Prop := stutter s s' ∨ ndDecrement s s'

def spec : Spec Nat where
  init := fun _ => True
  next := next
  fair := [ndDecrement]  -- only ndDecrement is fair

theorem ndDecrement_enabled_of_pos {s : Nat} (h : s > 0) : enabled ndDecrement s :=
  ⟨s - 1, 1, by omega, by omega, by omega⟩

theorem countdown_reaches_zero :
    pred_implies spec.formula
      (leads_to (state_pred (fun s : Nat => s > 0))
                (state_pred (fun s : Nat => s = 0))) := by
  apply leads_to_via_nat (fun e => e 0)
  · -- Step case: k > 0
    intro k hk e ⟨_, hnext, hwf⟩ i hp hμ
    have hwf : weak_fairness ndDecrement e := by
      simp only [spec, tla_bigwedge, Foldable.fold, tla_true] at hwf; exact hwf.1
    have h1 : leads_to
        (fun e => e 0 > 0 ∧ e 0 = k)
        (fun e => e 0 = 0 ∨ (e 0 > 0 ∧ e 0 < k))
        e := by
      apply wf1 _ _ next ndDecrement e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: stutter preserves p; ndDecrement gives q
        intro m ⟨⟨hp', hcount⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, next] at *
        rcases hstep with hstut | hdec
        · -- Stutter: p preserved
          left; rw [stutter] at hstut; rw [hstut]; exact ⟨hp', hcount⟩
        · -- ndDecrement: q holds
          right
          obtain ⟨d, hd1, hd2, hs'⟩ := hdec
          by_cases h0 : e m - d = 0
          · left; rw [hs']; exact h0
          · right; rw [hs', hcount]; omega
      · -- Progress: ndDecrement fires → q
        intro m ⟨⟨hp', hcount⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, ndDecrement] at *
        obtain ⟨d, hd1, hd2, hs'⟩ := hstep
        by_cases h0 : e m - d = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Enablement
        intro m ⟨hp', _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact ndDecrement_enabled_of_pos hp'
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ⟩
    simp only [exec.drop_drop] at hj
    rcases hj with hq | ⟨hp'', hlt⟩
    · exact ⟨j, Or.inl hq⟩
    · exact ⟨j, Or.inr ⟨hp'', hlt⟩⟩
  · -- Base case
    intro e _ i hp hμ
    simp only [state_pred, exec.drop] at hp hμ; omega

end NondetDecrement

/-! ## Variant 3: Lexicographic Countdown

    State: (x, y) : Nat × Nat. Three actions:
    (a) stutter: (x, y) → (x, y)
    (b) decX:    (x, y) → (x - 1, y') for arbitrary y' (decreases x, resets y)
    (c) decY:    (x, y) → (x, y - 1) when y > 0 (decreases y, keeps x)

    Only decX and decY are fair. Goal: (x, y) ≠ (0, 0) ↝ (x, y) = (0, 0).

    Uses `leads_to_via_lex` with measures μ₁ = x, μ₂ = y.
    Action (b) decreases μ₁ (and may increase μ₂ arbitrarily).
    Action (c) keeps μ₁ fixed and decreases μ₂.
    This is the canonical lexicographic ranking example. -/

namespace LexCountdown

abbrev LState := Nat × Nat

def stutterL (s s' : LState) : Prop := s' = s
def decX (s s' : LState) : Prop := s.1 > 0 ∧ s'.1 = s.1 - 1
def decY (s s' : LState) : Prop := s.2 > 0 ∧ s'.1 = s.1 ∧ s'.2 = s.2 - 1
def nextL (s s' : LState) : Prop := stutterL s s' ∨ decX s s' ∨ decY s s'

/-- Combined fair action: decX ∨ decY. The spec gives WF to this combined action.
    When either decX or decY is enabled, eventually one of them fires. -/
def progress (s s' : LState) : Prop := decX s s' ∨ decY s s'

def spec : Spec LState where
  init := fun _ => True
  next := nextL
  fair := [progress]

def notDone : pred LState := state_pred (fun s => s.1 > 0 ∨ s.2 > 0)
def done : pred LState := state_pred (fun s => s.1 = 0 ∧ s.2 = 0)

theorem progress_enabled_of_notDone {s : LState} (h : s.1 > 0 ∨ s.2 > 0) :
    enabled progress s := by
  rcases h with hx | hy
  · -- x > 0: decX enabled (choose any y')
    exact ⟨(s.1 - 1, 0), Or.inl ⟨hx, rfl⟩⟩
  · -- y > 0: decY enabled
    exact ⟨(s.1, s.2 - 1), Or.inr ⟨hy, rfl, rfl⟩⟩

theorem lex_countdown :
    pred_implies spec.formula (leads_to notDone done) := by
  apply leads_to_via_lex (fun e => (e 0).1) (fun e => (e 0).2)
  · -- Step case: (k₁, k₂) with k₁ > 0 ∨ k₂ > 0
    intro k₁ k₂ hpos e ⟨_, hnext, hwf⟩ i hp hμ₁ hμ₂
    have hwf : weak_fairness progress e := by
      simp only [spec, tla_bigwedge, Foldable.fold, tla_true] at hwf; exact hwf.1
    -- WF1 with measure-aware predicates
    -- p_wf1 = notDone ∧ μ₁ = k₁ ∧ μ₂ = k₂
    -- q_wf1 = done ∨ (notDone ∧ lex_decreased)
    have h1 : leads_to
        (fun e => ((e 0).1 > 0 ∨ (e 0).2 > 0) ∧ (e 0).1 = k₁ ∧ (e 0).2 = k₂)
        (fun e => ((e 0).1 = 0 ∧ (e 0).2 = 0) ∨
          (((e 0).1 > 0 ∨ (e 0).2 > 0) ∧
            ((e 0).1 < k₁ ∨ ((e 0).1 = k₁ ∧ (e 0).2 < k₂))))
        e := by
      apply wf1 _ _ nextL progress e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: stutter preserves p; decX/decY give q
        intro m ⟨⟨hnd, hx, hy⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, nextL,
          stutterL, decX, decY] at hnd hx hy hstep ⊢
        rcases hstep with hstut | ⟨hxp, hx'⟩ | ⟨hyp, hx', hy'⟩
        · -- Stutter: s' = s → p preserved
          left; rw [hstut]; exact ⟨hnd, hx, hy⟩
        · -- decX: x' = x - 1. Done or lex decreased.
          by_cases hnd' : (e (m + 1)).1 > 0 ∨ (e (m + 1)).2 > 0
          · right; right; refine ⟨hnd', Or.inl ?_⟩; omega
          · right; left
            have hnd1 : ¬(e (m + 1)).1 > 0 := fun h => hnd' (Or.inl h)
            have hnd2 : ¬(e (m + 1)).2 > 0 := fun h => hnd' (Or.inr h)
            exact ⟨by omega, by omega⟩
        · -- decY: x' = x, y' = y - 1. Either done or lex decreased.
          by_cases hnd' : (e (m + 1)).1 > 0 ∨ (e (m + 1)).2 > 0
          · right; right; exact ⟨hnd', Or.inr ⟨by omega, by omega⟩⟩
          · right; left
            have hnd1 : ¬(e (m + 1)).1 > 0 := fun h => hnd' (Or.inl h)
            have hnd2 : ¬(e (m + 1)).2 > 0 := fun h => hnd' (Or.inr h)
            exact ⟨by omega, by omega⟩
      · -- Progress: decX or decY → q
        intro m ⟨⟨hnd, hx, hy⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, progress,
          decX, decY] at hnd hx hy hstep ⊢
        rcases hstep with ⟨hxp, hx'⟩ | ⟨hyp, hx', hy'⟩
        · by_cases hnd' : (e (m + 1)).1 > 0 ∨ (e (m + 1)).2 > 0
          · right; refine ⟨hnd', Or.inl ?_⟩; omega
          · left
            have hnd1 : ¬(e (m + 1)).1 > 0 := fun h => hnd' (Or.inl h)
            have hnd2 : ¬(e (m + 1)).2 > 0 := fun h => hnd' (Or.inr h)
            exact ⟨by omega, by omega⟩
        · by_cases hnd' : (e (m + 1)).1 > 0 ∨ (e (m + 1)).2 > 0
          · right; exact ⟨hnd', Or.inr ⟨by omega, by omega⟩⟩
          · left
            have hnd1 : ¬(e (m + 1)).1 > 0 := fun h => hnd' (Or.inl h)
            have hnd2 : ¬(e (m + 1)).2 > 0 := fun h => hnd' (Or.inr h)
            exact ⟨by omega, by omega⟩
      · -- Enablement: notDone → progress enabled
        intro m ⟨hnd, _, _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact progress_enabled_of_notDone hnd
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ₁, hμ₂⟩
    simp only [exec.drop_drop] at hj
    rcases hj with ⟨hq₁, hq₂⟩ | ⟨hnd', hlt⟩
    · exact ⟨j, Or.inl ⟨hq₁, hq₂⟩⟩
    · exact ⟨j, Or.inr ⟨hnd', hlt⟩⟩
  · -- Base case: (0, 0) → done immediately
    intro e _ i hp hμ₁ hμ₂
    simp only [notDone, done, state_pred, exec.drop] at hp hμ₁ hμ₂
    omega

end LexCountdown
