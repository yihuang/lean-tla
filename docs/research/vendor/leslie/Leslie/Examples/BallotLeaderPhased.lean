import Leslie.PhaseRound

/-! ## Ballot-Based Leader Election via PhaseRoundAlg

    Refactoring of `BallotLeader.lean` to use the `PhaseRoundAlg` framework
    from `PhaseRound.lean`. The protocol is identical:

    **Phase 0 (New):** Each process broadcasts Bid(id) or NoBid, then picks
    the minimum bidder among received bids.

    **Phase 1 (Ack):** Each process broadcasts its pick, then elects a leader
    if a strict majority of received picks agree on the same candidate.

    **Safety: at most one leader is ever elected.**

    ### Design: modeling nondeterministic bidding

    The original `BallotLeader` uses an external `oracle : Fin n → Bool` to
    decide which processes bid. `PhaseRoundAlg.Phase.send` is deterministic
    (`P → S → M`), so we cannot introduce nondeterminism there.

    Solution: we add a `bidding : Bool` field to the local state. The
    nondeterminism is in the INITIAL state — any assignment of `bidding`
    values across processes is valid. Phase 0's `send` function then reads
    `bidding` deterministically. This is standard: lifting oracle choices
    into initial-state nondeterminism.

    ### Structure

    1. Define local state, message types per phase, and the `PhaseRoundAlg`.
    2. Wrap it in a `PhaseRoundSpec` with lossy communication.
    3. State the safety invariant (at most one leader).
    4. Prove safety using `phase_round_invariant`.
-/

open TLA

namespace BallotLeaderPhased

variable (n : Nat)

/-! ### State and messages -/

/-- Local state of each process.
    `bidding` encodes the nondeterministic bid decision (set at init). -/
structure LState (n : Nat) where
  /-- Whether this process is bidding for leadership (set at init, read in phase 0). -/
  bidding : Bool
  /-- The candidate this process picked (min bidder) after phase 0. -/
  picked : Option (Fin n)
  /-- Elected leader (set in phase 1). -/
  leader : Option (Fin n)
  deriving DecidableEq, Repr

/-- Message for phase 0 (New): bid announcement. -/
inductive NewMsg (n : Nat) where
  | bid (id : Fin n)
  | noBid
  deriving DecidableEq, Repr

/-- Message for phase 1 (Ack): pick announcement. -/
inductive AckMsg (n : Nat) where
  | pick (id : Fin n)
  | noPick
  deriving DecidableEq, Repr

/-! ### Helpers (reused from BallotLeader) -/

/-- Minimum element of a list of `Fin n`. -/
def List.minFin? {n : Nat} : List (Fin n) → Option (Fin n)
  | [] => none
  | x :: xs => match List.minFin? xs with
    | none => some x
    | some y => if x.val ≤ y.val then some x else some y

/-- Extract bid IDs from received phase-0 messages. -/
def collectBids (msgs : Fin n → Option (NewMsg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.bid id) => some id
    | _ => none

/-- Extract pick IDs from received phase-1 messages. -/
def collectPicks (msgs : Fin n → Option (AckMsg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.pick id) => some id
    | _ => none

/-- Count occurrences of `c` in a list. -/
def countVotes (c : Fin n) (picks : List (Fin n)) : Nat :=
  (picks.filter (· == c)).length

/-- Check if `c` has strict majority (> n/2). -/
def hasMajority (c : Fin n) (picks : List (Fin n)) : Bool :=
  countVotes n c picks * 2 > n

/-- Find a candidate with majority support, if any. -/
def findMajority (picks : List (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? fun c => hasMajority n c picks

/-! ### Uniform message type

    To avoid dependent-type casts in the phase definitions, we use a
    single message type for all phases. Each phase sends/receives a
    specific subset of constructors and ignores the others. This is
    standard practice and matches real protocol implementations. -/

inductive BLMsg (n : Nat) where
  | bid (id : Fin n)
  | noBid
  | pick (id : Fin n)
  | noPick
  deriving DecidableEq, Repr

/-- Uniform message type for both phases. -/
def BLMsgs : PhaseMessages 2 := fun _ => BLMsg n

/-! ### Phase definitions -/

/-- Phase 0 (New): broadcast bid/noBid, compute minimum bidder pick. -/
def newPhase : Phase (Fin n) (LState n) (BLMsg n) where
  send := fun p s => if s.bidding then .bid p else .noBid
  update := fun _p s msgs =>
    let bids := (List.finRange n).filterMap fun q =>
      match msgs q with
      | some (.bid id) => some id
      | _ => none
    { s with picked := List.minFin? bids }

/-- Extract pick IDs directly from BLMsg messages. -/
def collectBLPicks (msgs : Fin n → Option (BLMsg n)) : List (Fin n) :=
  (List.finRange n).filterMap fun q =>
    match msgs q with
    | some (.pick id) => some id
    | _ => none

/-- Phase 1 (Ack): broadcast pick, elect leader via majority. -/
def ackPhase : Phase (Fin n) (LState n) (BLMsg n) where
  send := fun _p s =>
    match s.picked with
    | some c => .pick c
    | none   => .noPick
  update := fun _p s msgs =>
    { s with leader := findMajority n (collectBLPicks n msgs) }

/-- The ballot leader as a 2-phase round algorithm. -/
def blAlg : PhaseRoundAlg (Fin n) (LState n) 2 (BLMsgs n) where
  init := fun _p s => s.picked = none ∧ s.leader = none
  phases := fun i =>
    if i.val = 0 then newPhase n else ackPhase n

/-! ### PhaseRoundSpec -/

def blSpec : PhaseRoundSpec (Fin n) (LState n) 2 (BLMsgs n) where
  alg := blAlg n
  comm := fun _ _ _ => True

def blLeslieSpec : Spec (PhaseRoundState (Fin n) (LState n) 2) :=
  (blSpec n).toSpec (by omega)

/-! ### Safety invariant -/

/-- At most one leader: all processes that have elected a leader agree. -/
def at_most_one_leader (s : PhaseRoundState (Fin n) (LState n) 2) : Prop :=
  ∀ p q l₁ l₂,
    (s.locals p).leader = some l₁ →
    (s.locals q).leader = some l₂ →
    l₁ = l₂

/-! ### Proof helpers -/

/-- The `collectPicks` applied to delivered messages simplifies to a filterMap
    that extracts actual picks filtered by the HO set.
    (Analogous to `BallotLeader.collectPicks_eq`.) -/
private theorem collectPicks_eq
    (actual_picks : Fin n → Option (Fin n))
    (ho : HOCollection (Fin n)) (p : Fin n) :
    let send_fn := fun q => match actual_picks q with
      | some c => AckMsg.pick c
      | none   => AckMsg.noPick
    collectPicks n (fun q => if ho p q then some (send_fn q) else none) =
    (List.finRange n).filterMap (fun q => if ho p q then actual_picks q else none) := by
  simp only [collectPicks]
  congr 1 ; funext q
  by_cases hho : ho p q = true
  · simp [hho] ; cases actual_picks q with | none => simp | some c => simp
  · have hf : ho p q = false := by revert hho ; cases ho p q <;> simp
    simp [hf]

/-! ### Pigeonhole lemma -/

/-- Two distinct candidates cannot both have majority support among n senders.
    (Restatement of `BallotLeader.picks_pigeonhole`.) -/
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

/-- Votes for candidate `c` in BLMsg-collected picks ≤ total supporters.
    Each vote came from a sender whose `picked` field matched. -/
theorem countVotes_le_supporters
    (locals : Fin n → LState n)
    (ho : HOCollection (Fin n))
    (p c : Fin n) :
    countVotes n c (collectBLPicks n (fun q =>
      if ho p q then some ((ackPhase n).send q (locals q)) else none)) ≤
    ((List.finRange n).filter fun q =>
      decide ((locals q).picked = some c)).length := by
  simp only [countVotes, collectBLPicks, ackPhase]
  apply filterMap_filter_count_le
  intro q hq
  simp only [decide_eq_true_eq]
  by_cases hho : ho p q = true
  · simp [hho] at hq
    cases h : (locals q).picked <;> simp_all
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

/-! ### Main safety proof

    We prove the invariant `at_most_one_leader` using `phase_round_invariant`.

    The key insight: leaders are only set during phase 1 (Ack). In phase 0
    (New), only `picked` changes, and `leader` is preserved. In phase 1,
    leaders are elected via `findMajority`, and the pigeonhole argument
    ensures at most one candidate can have majority support.

    Since the `PhaseRoundAlg` definition involves dependent-type casts that
    complicate direct symbolic reasoning, we use `sorry` for the inductive
    step, noting that the mathematical argument is identical to the original
    `BallotLeader.at_most_one_leader_invariant`. -/

theorem at_most_one_leader_invariant :
    pred_implies (blLeslieSpec n).safety
      [tlafml| □ ⌜at_most_one_leader n⌝] := by
  apply phase_round_invariant (blSpec n) (by omega)
  · -- Init: no leaders
    intro s ⟨_, _, hinit⟩ p q l₁ l₂ hl₁ _
    have := (hinit p).2
    simp_all
  · -- Inductive step: phase step preserves at most one leader
    intro s ho hinv _ s' ⟨hadvance, hlocals⟩
    intro p q l₁ l₂ hl₁ hl₂
    -- Case split on the current phase (0 or 1)
    have hph : s.phase.val = 0 ∨ s.phase.val = 1 := by
      have := s.phase.isLt ; omega
    -- The phase determines which Phase struct is used:
    -- (blAlg n).phases i = if i.val = 0 then newPhase n else ackPhase n
    -- After phase_step, hlocals gives:
    -- s'.locals p = ((blAlg n).phases s.phase).update p (s.locals p) (delivered ...)
    -- We need to show this preserves at_most_one_leader.
    -- Key fact: newPhase.update only changes `picked` (not `leader`).
    -- ackPhase.update only changes `leader` via findMajority.
    rcases hph with hph0 | hph1
    · -- Phase 0 (New): newPhase.update preserves `leader`
      -- Reduce: (blAlg n).phases s.phase = newPhase n (since phase = 0)
      have hph : (blAlg n).phases s.phase = newPhase n := by
        show (if s.phase.val = 0 then newPhase n else ackPhase n) = newPhase n
        simp [hph0]
      have h_pres : ∀ r, (s'.locals r).leader = (s.locals r).leader := by
        intro r
        have hr := hlocals r
        simp only [blSpec, blAlg, hph0, ite_true, newPhase, phase_delivered] at hr
        rw [hr]
      rw [h_pres p] at hl₁ ; rw [h_pres q] at hl₂
      exact hinv p q l₁ l₂ hl₁ hl₂
    · -- Phase 1 (Ack): leaders set via findMajority; pigeonhole applies
      -- Unfold ackPhase in hl₁ and hl₂
      have hp := hlocals p ; have hq := hlocals q
      simp only [blSpec, blAlg, show ¬(s.phase.val = 0) by omega, ite_false,
                  ackPhase] at hp hq
      rw [hp] at hl₁ ; rw [hq] at hl₂
      simp only at hl₁ hl₂
      -- hl₁ : findMajority n (collectPicks n (filtered_p)) = some l₁
      -- hl₂ : findMajority n (collectPicks n (filtered_q)) = some l₂
      -- Both l₁ and l₂ require majority support. The actual senders'
      -- picks are (s.locals ·).picked. By countVotes_le_supporters,
      -- votes for any candidate ≤ total supporters. By picks_pigeonhole,
      -- two candidates with majority support must be equal.
      -- Chain: findMajority → hasMajority → countVotes → actual supporters → pigeonhole
      have hm₁ := (hasMajority_iff n).mp (findMajority_hasMajority n hl₁)
      have hm₂ := (hasMajority_iff n).mp (findMajority_hasMajority n hl₂)
      have hc₁ := countVotes_le_supporters n s.locals ho p l₁
      have hc₂ := countVotes_le_supporters n s.locals ho q l₂
      have hs₁ : ((List.finRange n).filter fun r =>
          decide ((s.locals r).picked = some l₁)).length * 2 > n :=
        Nat.lt_of_lt_of_le hm₁ (Nat.mul_le_mul_right 2 hc₁)
      have hs₂ : ((List.finRange n).filter fun r =>
          decide ((s.locals r).picked = some l₂)).length * 2 > n :=
        Nat.lt_of_lt_of_le hm₂ (Nat.mul_le_mul_right 2 hc₂)
      exact picks_pigeonhole n (fun r => (s.locals r).picked) l₁ l₂ hs₁ hs₂

end BallotLeaderPhased
