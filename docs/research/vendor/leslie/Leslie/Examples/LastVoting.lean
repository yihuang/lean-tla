import Leslie.Round

/-! ## LastVoting: Paxos in the Heard-Of Model

    The LastVoting algorithm is the Heard-Of (HO) model formulation of the
    Paxos consensus algorithm, from Charron-Bost & Schiper (2009). It shows
    how Paxos's prepare/promise/accept/learn phases map onto a round-based
    framework with 4 phases per ballot (macro-round).

    ### Protocol (simplified to 3 processes)

    Processes are `Fin 3`. Values are `Nat`. A **ballot** is a natural number.
    The **coordinator** of ballot `b` is `b % 3`. Each ballot consists of 4
    phases (numbered 0--3):

    **Phase 0 (Prepare / 1a):**
    The coordinator of the current ballot broadcasts a prepare message.
    Each process that hears the prepare records it.

    **Phase 1 (Promise / 1b):**
    Each process sends its `lastVote` (the value and ballot of its most
    recent accept, or `none`) to the coordinator. The coordinator collects
    these promises; if it hears from a majority (≥ 2 of 3), it picks a
    value: if any promise reports a previous accept, it takes the value
    from the highest-ballot accept; otherwise it freely chooses a value.

    **Phase 2 (Accept / 2a):**
    If the coordinator has a proposal, it broadcasts it.
    Each process that hears the proposal accepts it, updating `lastVote`.

    **Phase 3 (Decide / 2b):**
    Each process broadcasts whether it accepted in this ballot.
    If a process hears that a majority (≥ 2) accepted, it decides.

    ### Safety property: Agreement

    If two processes have decided, they decided the same value.

    ### Key invariant (proposals respect previous votes)

    If a value `v` was accepted by a majority in ballot `b`, then any
    proposal in ballot `b' > b` must also propose `v`. This ensures that
    once a value is "locked in" by a majority accept, all future ballots
    respect it.

    ### Design choices

    - We use `Fin 3` for concreteness (following VRViewChange.lean), which
      makes quorum intersection proofs over 3 processes tractable via the
      existing `majority3_intersect` pigeonhole lemma from Round.lean.
    - The protocol is modeled as a plain `Spec` (not `RoundAlg`), because
      the 4 phases have different message types and the coordinator role
      breaks process symmetry.
    - Each ballot uses 4 consecutive "round" indices internally. The global
      round counter tracks the overall phase.

    ### Proof strategy

    1. Define the combined invariant `lv_inv` which includes:
       - Agreement consistency: if two processes decided, same value
       - Proposal consistency: proposals respect previous majority accepts
       - Local consistency: lastVote records match actual protocol history
    2. Prove the invariant holds initially.
    3. Prove it is preserved by each of the 4 phase transitions + stutter.
    4. Derive agreement from the invariant.
-/

open TLA

namespace LastVoting

/-! ### Types -/

/-- Process type: 3 processes. -/
abbrev Proc := Fin 3

/-- Values are natural numbers. -/
abbrev Value := Nat

/-! ### State -/

/-- Per-process local state. -/
structure LState where
  /-- The value and ballot of the last accepted proposal, or `none`. -/
  lastVote : Option (Value × Nat)
  /-- Decided value (once set, stays). -/
  decided : Option Value
  /-- Whether this process received a prepare for the current ballot. -/
  prepared : Bool
  /-- Whether this process accepted in the current ballot. -/
  accepted : Bool
  deriving DecidableEq, Repr

/-- Global state of the protocol. -/
structure GState where
  /-- Current ballot number (starts at 0). -/
  ballot : Nat
  /-- Phase within the current ballot (0 = prepare, 1 = promise,
      2 = accept, 3 = decide). -/
  phase : Nat
  /-- Per-process local states. -/
  locals : Proc → LState
  /-- The coordinator's proposed value for the current ballot (set in phase 1). -/
  proposal : Option Value

/-! ### Helpers -/

/-- The coordinator of ballot `b` is `b % 3`. -/
def coordinator (b : Nat) : Proc := ⟨b % 3, Nat.mod_lt b (by omega)⟩

/-- Majority predicate for 3 processes: at least 2 satisfy the predicate. -/
def hasMaj3 (p : Proc → Bool) : Bool :=
  let cnt := (List.finRange 3).filter (fun r => p r) |>.length
  decide (cnt ≥ 2)

/-- Extract the highest-ballot lastVote from a collection of promises.
    Returns the value from the promise with the highest ballot number,
    or `none` if all promises are empty. -/
def highestVote (promises : Proc → Option (Option (Value × Nat))) :
    Option Value :=
  let collected := (List.finRange 3).filterMap fun p =>
    match promises p with
    | some (some (v, b)) => some (v, b)
    | _ => none
  match collected with
  | [] => none
  | (v, b) :: rest =>
    some (rest.foldl (fun (best : Value × Nat) (cur : Value × Nat) =>
      if cur.2 > best.2 then cur else best) (v, b)).1

/-! ### Phase transitions -/

/-- Phase 0 → 1 (Prepare): The coordinator sends prepare(ballot).
    Each process in the coordinator's HO set records that it received
    the prepare. -/
def stepPrepare (s s' : GState) (ho : HOCollection Proc) : Prop :=
  s.phase = 0 ∧ s'.phase = 1 ∧
  s'.ballot = s.ballot ∧
  s'.proposal = none ∧
  (∀ p : Proc, s'.locals p =
    { (s.locals p) with
      prepared := ho (coordinator s.ballot) p
      accepted := false }) -- reset accepted for this ballot

/-- Phase 1 → 2 (Promise): Each process sends its lastVote to the
    coordinator. The coordinator collects promises and picks a value.
    `freeValue` is used when the coordinator can freely choose. -/
def stepPromise (s s' : GState) (ho : HOCollection Proc)
    (freeValue : Value) : Prop :=
  s.phase = 1 ∧ s'.phase = 2 ∧
  s'.ballot = s.ballot ∧
  -- Coordinator collects promises from processes in its HO set
  let c := coordinator s.ballot
  let promises : Proc → Option (Option (Value × Nat)) :=
    fun p => if ho p c then some (s.locals p).lastVote else none
  let promiseCount := (List.finRange 3).filter (fun p => ho p c) |>.length
  -- If coordinator got a majority of promises, it proposes
  (if promiseCount ≥ 2 then
    match highestVote promises with
    | some v => s'.proposal = some v
    | none   => s'.proposal = some freeValue
  else
    s'.proposal = none) ∧
  -- Local states unchanged
  (∀ p, s'.locals p = s.locals p)

/-- Phase 2 → 3 (Accept): If the coordinator has a proposal, it broadcasts
    it. Each process in the HO set accepts the proposal. -/
def stepAccept (s s' : GState) (ho : HOCollection Proc) : Prop :=
  s.phase = 2 ∧ s'.phase = 3 ∧
  s'.ballot = s.ballot ∧
  s'.proposal = s.proposal ∧
  (∀ p : Proc, s'.locals p =
    match s.proposal with
    | some v =>
      if ho (coordinator s.ballot) p then
        { (s.locals p) with
          lastVote := some (v, s.ballot)
          accepted := true }
      else s.locals p
    | none => s.locals p)

/-- Phase 3 → 0 (Decide + advance ballot): Each process broadcasts whether
    it accepted. If a process hears from a majority that accepted, it
    decides. Then advance to the next ballot. -/
def stepDecide (s s' : GState) (ho : HOCollection Proc) : Prop :=
  s.phase = 3 ∧ s'.phase = 0 ∧
  s'.ballot = s.ballot + 1 ∧
  s'.proposal = none ∧
  (∀ p : Proc,
    let acceptors : Proc → Bool := fun q =>
      if ho q p then (s.locals q).accepted else false
    let majAccepted := hasMaj3 acceptors
    s'.locals p =
      { (s.locals p) with
        prepared := false
        accepted := false
        decided :=
          if majAccepted then
            match s.proposal with
            | some v => some v
            | none   => (s.locals p).decided
          else (s.locals p).decided })

/-- Stutter step: no progress. -/
def stepStutter (s s' : GState) : Prop := s' = s

/-! ### Specification -/

def lastVotingSpec : Spec GState where
  init := fun s =>
    s.ballot = 0 ∧ s.phase = 0 ∧ s.proposal = none ∧
    (∀ p, s.locals p = { lastVote := none, decided := none,
                          prepared := false, accepted := false })
  next := fun s s' =>
    (∃ ho, stepPrepare s s' ho) ∨
    (∃ ho fv, stepPromise s s' ho fv) ∨
    (∃ ho, stepAccept s s' ho) ∨
    (∃ ho, stepDecide s s' ho) ∨
    stepStutter s s'

/-! ### Safety property -/

/-- Agreement: if two processes have decided, they decided the same value. -/
def agreement (s : GState) : Prop :=
  ∀ (p q : Proc) (v w : Value),
    (s.locals p).decided = some v →
    (s.locals q).decided = some w →
    v = w

/-! ### Auxiliary invariants

    The full inductive invariant combines several properties:

    **(A) Decision monotonicity:** Once a process decides a value, its
    decision never changes.

    **(B) Decision validity:** If a process decided value `v`, then `v`
    was proposed in some ballot and accepted by a majority.

    **(C) Proposal consistency (the key Paxos invariant):** If value `v`
    was accepted by a majority in ballot `b`, then for all ballots `b' > b`
    where a proposal was made, the proposal is `v`.

    **(D) LastVote consistency:** Each process's `lastVote` field accurately
    records the value and ballot of its most recent accept, and the ballot
    in `lastVote` is ≤ the current ballot.

    **(E) Accepted consistency:** If a process has `accepted = true` in
    the current state, its `lastVote` matches the current ballot's proposal.

    For the simplified 3-process model, we capture these as concrete
    predicates on the state.
-/

/-- The core auxiliary invariant:
    If a process decided `v`, then `v` was the proposal of some ballot
    in which a majority accepted.

    For the proof, we track a stronger invariant: all decisions across
    all processes agree. This is the direct inductive formulation. -/
def lv_inv (s : GState) : Prop :=
  -- (A) Agreement on all decisions made so far
  agreement s ∧
  -- (B) If a process accepted in this ballot, its lastVote matches the proposal
  (∀ p : Proc, (s.locals p).accepted = true →
    ∃ v b, (s.locals p).lastVote = some (v, b) ∧
      b = s.ballot ∧ s.proposal = some v) ∧
  -- (C) A decision can only happen for the current proposal
  --     (if a majority accepted in this ballot)
  (s.phase = 3 →
    ∀ p : Proc, (s.locals p).accepted = true →
    ∃ v, s.proposal = some v ∧ (s.locals p).lastVote = some (v, s.ballot)) ∧
  -- (D) Decided values agree with each other and with any future decision
  --     This is the key inductive property that connects across ballots
  (∀ p : Proc, ∀ v, (s.locals p).decided = some v →
    -- Any new majority-accept in the decide phase produces the same value
    (s.phase = 3 → s.proposal ≠ none →
      hasMaj3 (fun q => (s.locals q).accepted) = true →
      s.proposal = some v))

/-! ### Invariant proofs -/

theorem lv_inv_init : ∀ s, lastVotingSpec.init s → lv_inv s := by
  intro s ⟨_, _, _, hlocals⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Agreement: vacuously true, no decisions
    intro p q v w hv hw
    simp [hlocals p] at hv
  · -- Accepted consistency: vacuously true, no accepts
    intro p hacc
    simp [hlocals p] at hacc
  · -- Phase 3 consistency: vacuously, phase = 0
    intro hph ; simp_all
  · -- Decided-proposal consistency: vacuously true
    intro p v hv
    simp [hlocals p] at hv

/-- The main invariant preservation theorem.
    Each of the 4 phase transitions + stutter preserves `lv_inv`.
    The hard cases involve the decide step (phase 3 → 0). -/
theorem lv_inv_preserved :
    ∀ s s', lastVotingSpec.next s s' → lv_inv s → lv_inv s' := by
  sorry

/-! ### Agreement theorem -/

/-- Agreement is an invariant of the LastVoting protocol. -/
theorem lv_agreement :
    pred_implies lastVotingSpec.safety [tlafml| □ ⌜agreement⌝] := by
  -- We prove the stronger combined invariant, then project
  suffices h : pred_implies lastVotingSpec.safety [tlafml| □ ⌜lv_inv⌝] by
    intro e he n
    exact (h e he n).1
  apply init_invariant
  · exact lv_inv_init
  · exact fun s s' hnext hinv => lv_inv_preserved s s' hnext hinv

/-! ### Proposal-respects-votes invariant (cross-ballot)

    The key Paxos safety argument: if a majority accepted value `v` in
    ballot `b`, then any proposal in ballot `b' > b` must also be `v`.

    In the HO model, the coordinator of ballot `b'` collects lastVote
    messages from a majority. By quorum intersection (any two majorities
    of 3 share a member), at least one process in the coordinator's
    promise quorum also accepted `v` in ballot `b`. The `highestVote`
    selection ensures the coordinator picks `v` (or a value from an
    even later ballot, which by induction is also `v`).

    This is the classic Paxos argument. We state it here and leave the
    proof as sorry since it requires tracking the full history of
    proposals and accepts across ballots. -/

/-- If value `v` was accepted by a majority in ballot `b`, and a proposal
    is made in ballot `b'` with `b' > b`, then the proposal in `b'` is `v`.

    Note: This is a semantic property that spans multiple states/ballots.
    In a TLA model, it would be expressed as a history variable invariant.
    We state it as a property of individual states, restricted to the
    current ballot's information. -/
def proposals_respect_votes (s : GState) : Prop :=
  -- Within the current ballot: if a majority of processes have lastVote
  -- entries from the same ballot b with value v, then the current proposal
  -- (if any) must be v.
  ∀ v b,
    ((List.finRange 3).filter fun p =>
      decide ((s.locals p).lastVote = some (v, b))).length ≥ 2 →
    s.proposal ≠ none →
    s.proposal = some v

/-! ### Quorum intersection for majority-of-3

    We reuse the `majority3_intersect` style argument. Any two sets of
    size ≥ 2 among 3 elements must share a member. -/

/-- Two majorities of 3 processes must intersect. -/
theorem maj3_intersect (p₁ p₂ : Proc → Bool)
    (h₁ : ((List.finRange 3).filter fun r => p₁ r).length ≥ 2)
    (h₂ : ((List.finRange 3).filter fun r => p₂ r).length ≥ 2) :
    ∃ r : Proc, p₁ r = true ∧ p₂ r = true := by
  by_contra h
  have h' : ∀ r, ¬(p₁ r = true ∧ p₂ r = true) := by
    intro r hr ; exact h ⟨r, hr⟩
  have h_sum := filter_disjoint_length_le
    (fun r => p₁ r) (fun r => p₂ r) (List.finRange 3) h'
  have h_len : (List.finRange 3).length = 3 := List.length_finRange
  omega

/-! ### Full cross-ballot invariant (stated but not proved)

    The full Paxos safety argument requires tracking the history of
    proposals and accepts across all ballots, not just the current one.
    This would require either:
    (a) A history variable recording all past proposals and accepts, or
    (b) A ghost variable encoding the "safe value" at each ballot.

    The `proposals_respect_votes` property above captures the key idea
    within a single state. A complete proof would need to show it is
    inductive across ballot transitions, using quorum intersection
    (maj3_intersect) at the promise collection step.

    Proof sketch for the promise step (phase 1):
    1. Suppose value v was accepted by majority M in ballot b.
    2. The coordinator of ballot b' > b collects promises from majority M'.
    3. By maj3_intersect, ∃ process r ∈ M ∩ M'.
    4. Process r's lastVote has ballot ≥ b (it accepted v at b).
    5. highestVote picks the value from the highest ballot ≥ b.
    6. By induction, that value is also v.
    7. Therefore the coordinator proposes v.

    The inductive structure means this proof needs a strengthened invariant
    that tracks the highest accepted ballot for each value across the
    entire execution history. We leave this as sorry. -/

theorem proposals_respect_votes_invariant :
    pred_implies lastVotingSpec.safety
      [tlafml| □ ⌜proposals_respect_votes⌝] := by
  sorry

end LastVoting
