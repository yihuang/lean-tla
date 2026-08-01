import Leslie.Round

/-! ## Ballot-Based Leader Election (Single Ballot)

    A round-based leader election protocol for `n` processes (`Fin n`).

    **Protocol (single ballot, two rounds):**

    **Round 0 (New phase):**
    - Each process nondeterministically decides whether to bid for leadership.
    - It broadcasts `Bid(my_id)` if bidding, `NoBid` otherwise.
    - Upon receiving, each process picks the minimum bidder among received bids.

    **Round 1 (Ack phase):**
    - Each process broadcasts its pick (or NoPick if it didn't pick anyone).
    - Upon receiving, if a strict majority (> n/2) of received picks
      agree on the same candidate, that candidate is elected leader.

    **Safety: at most one leader is ever elected.**

    The core argument is pigeonhole: two distinct candidates cannot both
    have majority support among n senders. If both have > n/2 supporters,
    that requires > n total, but there are only n senders.

    **Note on multi-ballot extension:** Repeating this protocol across
    multiple ballots without additional mechanisms (like Paxos's
    prepare/promise) would break safety — a new ballot could elect a
    different leader. Cross-ballot consistency requires processes to
    learn about previous elections before starting new ones.
-/

open TLA

namespace BallotLeader

variable (n : Nat)

/-! ### State and messages -/

/-- Local state of each process. -/
structure LState (n : Nat) where
  /-- The candidate this process picked (min bidder) after the New phase. -/
  picked : Option (Fin n)
  /-- Elected leader. -/
  leader : Option (Fin n)
  deriving DecidableEq, Repr

/-- Message type. -/
inductive Msg (n : Nat) where
  | bid (id : Fin n)
  | noBid
  | pick (id : Fin n)
  | noPick
  deriving DecidableEq, Repr

/-- Global state. -/
structure GState (n : Nat) where
  round : Nat
  locals : Fin n → LState n

/-! ### Protocol logic -/

/-- Minimum element of a list of Fin n. -/
def List.minFin? {n : Nat} : List (Fin n) → Option (Fin n)
  | [] => none
  | x :: xs => match List.minFin? xs with
    | none => some x
    | some y => if x.val ≤ y.val then some x else some y

/-- Extract bid IDs from received messages. -/
def collectBids (msgs : Fin n → Option (Msg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.bid id) => some id
    | _ => none

/-- Extract pick IDs from received messages. -/
def collectPicks (msgs : Fin n → Option (Msg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.pick id) => some id
    | _ => none

/-- Count occurrences of `c` in a list. -/
def countVotes (c : Fin n) (picks : List (Fin n)) : Nat :=
  (picks.filter (· == c)).length

/-- Check if `c` has strict majority (> n/2, equivalently 2 * count > n). -/
def hasMajority (c : Fin n) (picks : List (Fin n)) : Bool :=
  countVotes n c picks * 2 > n

/-- Find a candidate with majority support, if any. -/
def findMajority (picks : List (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? fun c => hasMajority n c picks

/-- Messages delivered to process p (broadcast model, filtered by HO). -/
def deliveredMsgs' (send_fn : Fin n → Msg n)
    (ho : HOCollection (Fin n)) (p : Fin n) :
    Fin n → Option (Msg n) :=
  fun q => if ho p q then some (send_fn q) else none

/-! ### Round transitions -/

/-- Round 0 (New → picked): processes bid and compute picks. -/
def stepNew (s s' : GState n) (ho : HOCollection (Fin n))
    (oracle : Fin n → Bool) : Prop :=
  s.round = 0 ∧ s'.round = 1 ∧
  ∀ p, s'.locals p =
    let msgs := deliveredMsgs' n
      (fun q => if oracle q then .bid q else .noBid) ho p
    let bids := collectBids n msgs
    { (s.locals p) with picked := List.minFin? bids }

/-- Round 1 (Ack → done): processes exchange picks and elect. -/
def stepAck (s s' : GState n) (ho : HOCollection (Fin n)) : Prop :=
  s.round = 1 ∧ s'.round = 2 ∧
  ∀ p, s'.locals p =
    let send_fn := fun q => match (s.locals q).picked with
      | some c => Msg.pick c
      | none   => Msg.noPick
    let msgs := deliveredMsgs' n send_fn ho p
    let picks := collectPicks n msgs
    { picked := (s.locals p).picked, leader := findMajority n picks }

/-- After round 1, the protocol is done (stutter). -/
def stepDone (s s' : GState n) : Prop :=
  s.round ≥ 2 ∧ s' = s

def ballotLeaderSpec : Spec (GState n) where
  init := fun s => s.round = 0 ∧
    ∀ p, s.locals p = { picked := none, leader := none }
  next := fun s s' =>
    (∃ ho oracle, stepNew n s s' ho oracle) ∨
    (∃ ho, stepAck n s s' ho) ∨
    stepDone n s s'

/-! ### Safety invariant -/

/-- At most one leader: all processes that have elected a leader agree. -/
def at_most_one_leader (s : GState n) : Prop :=
  ∀ p q l₁ l₂,
    (s.locals p).leader = some l₁ →
    (s.locals q).leader = some l₂ →
    l₁ = l₂

/-! ### Helper lemmas

    `filter_disjoint_length_le` and `filterMap_filter_count_le` are
    imported from `Round.lean` via `open TLA`. -/

/-- The message extraction in `collectPicks` simplifies: with the specific
    send function for the Ack phase, `collectPicks` equals a `filterMap`
    that directly extracts `actual_picks` filtered by the HO set. -/
private theorem collectPicks_eq
    (actual_picks : Fin n → Option (Fin n))
    (ho : HOCollection (Fin n)) (p : Fin n) :
    let send_fn := fun q => match actual_picks q with
      | some c => Msg.pick c
      | none   => Msg.noPick
    collectPicks n (deliveredMsgs' n send_fn ho p) =
    (List.finRange n).filterMap (fun q => if ho p q then actual_picks q else none) := by
  simp only [collectPicks]
  congr 1 ; funext q
  simp only [deliveredMsgs']
  by_cases hho : ho p q = true
  · simp [hho] ; cases actual_picks q with | none => simp | some c => simp
  · have hf : ho p q = false := by revert hho ; cases ho p q <;> simp
    simp [hf]

/-! ### Pigeonhole lemma -/

/-- **Pigeonhole for majorities (general n).**
    Among n processes, if > n/2 support c₁ and > n/2 support c₂, then c₁ = c₂.
    Two disjoint subsets of size > n/2 would need > n elements total,
    but only n are available. -/
theorem picks_pigeonhole
    (actual_picks : Fin n → Option (Fin n)) (c₁ c₂ : Fin n)
    (h₁ : ((List.finRange n).filter fun q =>
            decide (actual_picks q = some c₁)).length * 2 > n)
    (h₂ : ((List.finRange n).filter fun q =>
            decide (actual_picks q = some c₂)).length * 2 > n)
    : c₁ = c₂ := by
  by_contra hne
  have h_sum := filter_disjoint_length_le
    (fun q => decide (actual_picks q = some c₁))
    (fun q => decide (actual_picks q = some c₂))
    (List.finRange n)
    (by intro x ⟨h1, h2⟩
        simp [decide_eq_true_eq] at h1 h2
        rw [h1] at h2 ; exact hne (Option.some.inj h2))
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Connecting votes to actual picks -/

/-- Each vote for candidate `c` in a process's collected picks came from
    a sender who actually picked `c`. So the vote count for `c` is bounded
    by the number of actual supporters of `c` among all n senders. -/
theorem countVotes_le_supporters
    (actual_picks : Fin n → Option (Fin n))
    (ho : HOCollection (Fin n))
    (p c : Fin n) :
    let send_fn := fun q => match actual_picks q with
      | some c => Msg.pick c
      | none   => Msg.noPick
    let msgs := deliveredMsgs' n send_fn ho p
    countVotes n c (collectPicks n msgs) ≤
      ((List.finRange n).filter fun q =>
        decide (actual_picks q = some c)).length := by
  simp only [countVotes]
  rw [collectPicks_eq n actual_picks ho p]
  apply filterMap_filter_count_le
  intro q hq
  simp only [decide_eq_true_eq]
  by_cases hho : ho p q = true
  · simp [hho] at hq ; exact hq
  · have hf : ho p q = false := by revert hho ; cases ho p q <;> simp
    simp [hf] at hq

/-! ### Linking findMajority to the pigeonhole -/

/-- If findMajority returns some c, then c has majority support. -/
theorem findMajority_hasMajority {picks : List (Fin n)} {c : Fin n}
    (h : findMajority n picks = some c) :
    hasMajority n c picks = true := by
  unfold findMajority at h
  have := List.find?_some h
  exact this

/-- hasMajority means countVotes * 2 > n. -/
theorem hasMajority_iff {c : Fin n} {picks : List (Fin n)} :
    hasMajority n c picks = true ↔ countVotes n c picks * 2 > n := by
  simp [hasMajority]

/-! ### Main safety proof -/

theorem at_most_one_leader_invariant :
    pred_implies (ballotLeaderSpec n).safety
      [tlafml| □ ⌜at_most_one_leader n⌝] := by
  apply init_invariant
  · -- Init: no leaders
    intro s ⟨_, hinit⟩ p q l₁ l₂ hl₁ hl₂
    simp [hinit p] at hl₁
  · -- Inductive step
    intro s s' hnext hinv
    intro p q l₁ l₂ hl₁ hl₂
    rcases hnext with ⟨ho, oracle, hstep⟩ | ⟨ho, hstep⟩ | hstep
    · -- Round 0 (New): leader field is not set (only `picked` changes)
      obtain ⟨_, _, hlocals⟩ := hstep
      rw [hlocals p] at hl₁ ; rw [hlocals q] at hl₂
      exact hinv p q l₁ l₂ (by simp_all) (by simp_all)
    · -- Round 1 (Ack): leaders are elected via findMajority
      obtain ⟨_, _, hlocals⟩ := hstep
      rw [hlocals p] at hl₁ ; rw [hlocals q] at hl₂
      simp only at hl₁ hl₂
      -- hl₁ : findMajority n (collectPicks n msgs_p) = some l₁
      -- hl₂ : findMajority n (collectPicks n msgs_q) = some l₂
      -- The actual senders' picks in this round
      let actual_picks := fun r => (s.locals r).picked
      -- Step 1: findMajority → hasMajority → countVotes * 2 > n
      have hm₁ := (hasMajority_iff n).mp (findMajority_hasMajority n hl₁)
      have hm₂ := (hasMajority_iff n).mp (findMajority_hasMajority n hl₂)
      -- Step 2: countVotes ≤ actual supporters
      have hc₁ := countVotes_le_supporters n actual_picks ho p l₁
      have hc₂ := countVotes_le_supporters n actual_picks ho q l₂
      -- Step 3: actual supporters * 2 > n
      --   From countVotes * 2 > n and countVotes ≤ supporters,
      --   we get supporters * 2 ≥ countVotes * 2 > n.
      have hs₁ : ((List.finRange n).filter fun r =>
          decide (actual_picks r = some l₁)).length * 2 > n :=
        Nat.lt_of_lt_of_le hm₁ (Nat.mul_le_mul_right 2 hc₁)
      have hs₂ : ((List.finRange n).filter fun r =>
          decide (actual_picks r = some l₂)).length * 2 > n :=
        Nat.lt_of_lt_of_le hm₂ (Nat.mul_le_mul_right 2 hc₂)
      -- Step 4: pigeonhole
      exact picks_pigeonhole n actual_picks l₁ l₂ hs₁ hs₂
    · -- Round ≥ 2 (Done): state unchanged
      obtain ⟨_, heq⟩ := hstep
      subst heq
      exact hinv p q l₁ l₂ hl₁ hl₂

end BallotLeader
