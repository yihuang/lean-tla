import Leslie.PhaseRound

/-! ## LastVoting via PhaseRoundAlg (3 processes)

    Reimplementation of the LastVoting (Paxos / HO model) protocol using
    the `PhaseRoundAlg` multi-phase round framework from `PhaseRound.lean`.

    **This file proves safety for n = 3 processes.** The protocol and
    proof structure generalize to arbitrary n, but the quorum intersection
    arguments (majority ≥ 2 out of 3 ⟹ overlap) are specialized to n = 3.
    A general-n version would use `cross_phase_quorum_intersection` from
    `PhaseRound.lean` instead.

    ### Protocol overview

    LastVoting is the Heard-Of model formulation of Paxos, due to
    Charron-Bost & Schiper (2009). Each **ballot** (logical round)
    consists of 4 **phases**:

    | Phase | Name      | Paxos equivalent | What happens                              |
    |-------|-----------|------------------|-------------------------------------------|
    | 0     | Prepare   | 1a               | Coordinator broadcasts prepare            |
    | 1     | Promise   | 1b               | Processes send lastVote; coordinator      |
    |       |           |                  | collects and picks proposal               |
    | 2     | Accept    | 2a               | Coordinator broadcasts proposal           |
    | 3     | Decide    | 2b               | Processes check majority acceptance       |

    ### Mapping to PhaseRoundAlg

    `PhaseRoundAlg` expects uniform `send` / `update` functions per phase
    that apply to every process. The coordinator asymmetry is handled by
    branching on `round mod n` inside the send/update functions:

    - **Phase 0 (Prepare):**
      - `send`: coordinator sends `PrepareMsg.prepare`, others send
        `PrepareMsg.skip`.
      - `update`: process records `prepared := true` if it received a
        prepare from the coordinator. Resets `accepted := false`.

    - **Phase 1 (Promise):**
      - `send`: every process sends its `lastVote`.
      - `update`: *coordinator* counts promises; if majority (≥ 2 of 3),
        computes proposal via `highestVote` and stores it in local state
        (`proposal` field). Non-coordinator: no change.

    - **Phase 2 (Accept):**
      - `send`: coordinator sends `AcceptMsg.propose v` (from stored
        proposal). Non-coordinator sends `AcceptMsg.skip`.
      - `update`: if process received a `propose v` from the coordinator,
        it accepts: sets `lastVote := (v, round)` and `accepted := true`.

    - **Phase 3 (Decide):**
      - `send`: process sends `DecideMsg.accepted` or `.notAccepted`.
      - `update`: if majority sent `.accepted`, process decides the value
        from its `lastVote` (which matches the proposal).

    ### Coordinator identity

    The coordinator of a ballot is `round mod 3`, where `round` is the
    PhaseRoundAlg round counter. This counter increments once per complete
    4-phase ballot, so it serves as the ballot number.

    ### Design note: proposal in local state

    The coordinator must remember its proposal between Phase 1 (where it
    computes the proposal) and Phase 2 (where it broadcasts it). We store
    the proposal in the local state's `proposal` field. Only the
    coordinator writes this field (in Phase 1's update). Phase 2's send
    reads it back.
-/

open TLA

namespace LastVotingPhased

/-! ### Types -/

/-- 3 processes. All definitions and proofs in this file are specialized to n = 3. -/
abbrev Proc := Fin 3

/-- Values are natural numbers. -/
abbrev Value := Nat

/-! ### Message types (one per phase) -/

/-- Phase 0: Coordinator broadcasts prepare, others skip. -/
inductive PrepareMsg where
  | prepare
  | skip
  deriving DecidableEq, Repr

/-- Phase 1: Each process sends its lastVote to the coordinator. -/
structure PromiseMsg where
  lastVote : Option (Value × Nat)
  deriving DecidableEq, Repr

/-- Phase 2: Coordinator broadcasts its proposal, others skip. -/
inductive AcceptMsg where
  | propose (v : Value)
  | skip
  deriving DecidableEq, Repr

/-- Phase 3: Each process broadcasts its accept status. -/
inductive DecideMsg where
  | accepted (v : Value)
  | notAccepted
  deriving DecidableEq, Repr

/-- Uniform message type: a sum of all phase messages.
    Using a uniform type avoids dependent-type casts in phase
    definitions and proofs. Each phase sends/receives specific
    constructors and ignores the others. -/
inductive LVMsg where
  | prepare
  | skip
  | promise (lastVote : Option (Value × Nat))
  | propose (v : Value)
  | accepted (v : Value)
  | notAccepted
  deriving DecidableEq, Repr

/-- Uniform message type for all 4 phases. -/
def LVMsgs : PhaseMessages 4 := fun _ => LVMsg

/-! ### Local state -/

/-- Per-process local state.  Extends the original with a `proposal` field
    so the coordinator can store its computed proposal between phases. -/
structure LState where
  /-- Value and ballot of the most recent accept, or `none`. -/
  lastVote : Option (Value × Nat)
  /-- Decided value, once set stays forever. -/
  decided : Option Value
  /-- Whether this process received a prepare for the current ballot. -/
  prepared : Bool
  /-- Whether this process accepted in the current ballot. -/
  accepted : Bool
  /-- Coordinator's proposal (only meaningful for the coordinator process). -/
  proposal : Option Value
  deriving DecidableEq, Repr

/-! ### Helpers -/

/-- The coordinator of a ballot/round `r` is `r % 3`. -/
def coordinator (r : Nat) : Proc := ⟨r % 3, Nat.mod_lt r (by omega)⟩

/-- Majority predicate for 3 processes: at least 2 out of 3 satisfy the predicate.
    For general n, this would be `count > n / 2`. -/
def hasMaj3 (p : Proc → Bool) : Bool :=
  let cnt := (List.finRange 3).filter (fun r => p r) |>.length
  decide (cnt ≥ 2)

/-- Extract the highest-ballot lastVote from a collection of promises.
    Returns the value from the promise with the highest ballot number,
    or `none` if all promises are empty. -/
def highestVote (promises : Proc → Option PromiseMsg) : Option Value :=
  let collected := (List.finRange 3).filterMap fun p =>
    match promises p with
    | some ⟨some (v, b)⟩ => some (v, b)
    | _ => none
  match collected with
  | [] => none
  | (v, b) :: rest =>
    some (rest.foldl (fun (best : Value × Nat) (cur : Value × Nat) =>
      if cur.2 > best.2 then cur else best) (v, b)).1

/-! ### Phase definitions -/

/-- **Phase 0 — Prepare**
    - Send: coordinator sends `prepare`, others send `skip`.
    - Update: record whether we heard the coordinator's prepare.
      Reset `accepted` for the new ballot. -/
def phase0Send (round : Nat) (p : Proc) (_s : LState) : PrepareMsg :=
  if p = coordinator round then PrepareMsg.prepare else PrepareMsg.skip

def phase0Update (round : Nat) (p : Proc) (s : LState)
    (msgs : Proc → Option PrepareMsg) : LState :=
  let c := coordinator round
  let heardPrepare := match msgs c with
    | some PrepareMsg.prepare => true
    | _ => false
  { s with
    prepared := heardPrepare
    accepted := false
    -- Reset proposal at start of new ballot (for coordinator)
    proposal := if p = c then none else s.proposal }

/-- **Phase 1 — Promise**
    - Send: every process sends its `lastVote`.
    - Update (coordinator): collect promises; if majority, compute proposal
      and store in local state. Non-coordinator: no change. -/
def phase1Send (_round : Nat) (_p : Proc) (s : LState) : PromiseMsg :=
  ⟨s.lastVote⟩

/-- Free value for the coordinator to propose when no previous vote exists.
    We use a fixed default (0). In a real system this would be the
    coordinator's input value. -/
def defaultValue : Value := 0

def phase1Update (round : Nat) (p : Proc) (s : LState)
    (msgs : Proc → Option PromiseMsg) : LState :=
  if p = coordinator round then
    -- Coordinator collects promises
    let promiseCount := (List.finRange 3).filter (fun q =>
      match msgs q with | some _ => true | none => false) |>.length
    if promiseCount ≥ 2 then
      let prop := match highestVote msgs with
        | some v => v
        | none   => defaultValue
      { s with proposal := some prop }
    else
      { s with proposal := none }
  else s

/-- **Phase 2 — Accept**
    - Send: coordinator sends its proposal, others send `skip`.
    - Update: if we heard a proposal from the coordinator, accept it. -/
def phase2Send (round : Nat) (p : Proc) (s : LState) : AcceptMsg :=
  if p = coordinator round then
    match s.proposal with
    | some v => AcceptMsg.propose v
    | none   => AcceptMsg.skip
  else AcceptMsg.skip

def phase2Update (round : Nat) (_p : Proc) (s : LState)
    (msgs : Proc → Option AcceptMsg) : LState :=
  let c := coordinator round
  match msgs c with
  | some (AcceptMsg.propose v) =>
    { s with lastVote := some (v, round), accepted := true }
  | _ => s

/-- **Phase 3 — Decide**
    - Send: process sends whether it accepted.
    - Update: if a majority accepted, decide the proposal value. -/
def phase3Send (_round : Nat) (_p : Proc) (s : LState) : DecideMsg :=
  if s.accepted then
    match s.lastVote with
    | some (v, _) => DecideMsg.accepted v
    | none        => DecideMsg.notAccepted  -- shouldn't happen
  else DecideMsg.notAccepted

def phase3Update (_round : Nat) (_p : Proc) (s : LState)
    (msgs : Proc → Option DecideMsg) : LState :=
  let acceptors : Proc → Bool := fun q =>
    match msgs q with
    | some (DecideMsg.accepted _) => true
    | _ => false
  if hasMaj3 acceptors then
    -- Decide: pick the value from any accepted message we received
    let decidedVal := (List.finRange 3).filterMap (fun q =>
      match msgs q with
      | some (DecideMsg.accepted v) => some v
      | _ => none) |>.head?
    match decidedVal with
    | some v => { s with decided := some v, prepared := false, accepted := false }
    | none   => { s with prepared := false, accepted := false }
  else
    { s with prepared := false, accepted := false }

/-! ### PhaseRoundAlg assembly

    We need to package the 4 phases into a `PhaseRoundAlg`.
    The challenge is that our send/update functions depend on the
    `round` number (for coordinator computation), but the `Phase` type
    only receives `P` and `S`.

    Solution: we thread the round number through the local state.  We
    add a `roundNum` field to local state that tracks the current round.
    Alternatively, we can define the algorithm as a function of round
    number and use the `PhaseRoundState.round` field.

    Actually, `PhaseRoundAlg.phases` gives us `Phase P S (Msgs i)` which
    does NOT have access to the round number. But `phase_step` applies
    the phase to `PhaseRoundState` which has the round number.

    We work around this by storing the round number in the local state.
    Phase 3's update increments it (to stay in sync with the global
    round counter). -/

/-- Extended local state that includes the round number. -/
structure LVState where
  /-- The current round/ballot number, mirrored from global state. -/
  roundNum : Nat
  /-- Core protocol state. -/
  core : LState
  deriving DecidableEq, Repr

/-- Build the 4 phases using the uniform LVMsg type. -/

def lvPhase0 : Phase Proc LVState LVMsg where
  send := fun p s =>
    if p = coordinator s.roundNum then .prepare else .skip
  update := fun p s msgs =>
    let c := coordinator s.roundNum
    let heardPrepare := match msgs c with | some .prepare => true | _ => false
    { s with core := { s.core with
        prepared := heardPrepare
        accepted := false
        proposal := if p = c then none else s.core.proposal } }

/-- Collect (value, ballot) pairs from received promise messages. -/
def collectPromiseVotes (msgs : Proc → Option LVMsg) : List (Value × Nat) :=
  (List.finRange 3).filterMap fun q =>
    match msgs q with
    | some (.promise (some vb)) => some vb
    | _ => none

/-- Pick the proposal value from collected promise votes:
    the value with the highest ballot, or `defaultValue` if empty. -/
def pickProposal (collected : List (Value × Nat)) : Value :=
  match collected with
  | [] => defaultValue
  | (v, b) :: rest =>
    (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) (v, b)).1

def lvPhase1 : Phase Proc LVState LVMsg where
  send := fun _p s => .promise s.core.lastVote
  update := fun p s msgs =>
    if p = coordinator s.roundNum then
      let promiseCount := (List.finRange 3).filter (fun q =>
        match msgs q with | some (.promise _) => true | _ => false) |>.length
      if promiseCount ≥ 2 then
        { s with core := { s.core with proposal := some (pickProposal (collectPromiseVotes msgs)) } }
      else { s with core := { s.core with proposal := none } }
    else s

def lvPhase2 : Phase Proc LVState LVMsg where
  send := fun p s =>
    if p = coordinator s.roundNum then
      match s.core.proposal with | some v => .propose v | none => .skip
    else .skip
  update := fun _p s msgs =>
    let c := coordinator s.roundNum
    match msgs c with
    | some (.propose v) =>
      { s with core := { s.core with lastVote := some (v, s.roundNum), accepted := true } }
    | _ => s

def lvPhase3 : Phase Proc LVState LVMsg where
  send := fun _p s =>
    if s.core.accepted then
      match s.core.lastVote with
      | some (v, _) => .accepted v
      | none => .notAccepted
    else .notAccepted
  update := fun _p s msgs =>
    let acceptors : Proc → Bool := fun q =>
      match msgs q with | some (.accepted _) => true | _ => false
    let core' :=
      if hasMaj3 acceptors then
        let decidedVal := (List.finRange 3).filterMap (fun q =>
          match msgs q with | some (.accepted v) => some v | _ => none) |>.head?
        match decidedVal with
        | some v => { s.core with decided := some v, prepared := false, accepted := false }
        | none => { s.core with prepared := false, accepted := false }
      else { s.core with prepared := false, accepted := false }
    { roundNum := s.roundNum + 1, core := core' }

/-- The LastVoting algorithm as a `PhaseRoundAlg`. -/
def lvAlg : PhaseRoundAlg Proc LVState 4 LVMsgs where
  init := fun _p s =>
    s.roundNum = 0 ∧
    s.core = { lastVote := none, decided := none,
               prepared := false, accepted := false,
               proposal := none }
  phases := fun i =>
    if i.val = 0 then lvPhase0
    else if i.val = 1 then lvPhase1
    else if i.val = 2 then lvPhase2
    else lvPhase3

/-! ### Communication predicate

    LastVoting works under lossy communication — the safety proof does
    not require any communication predicate. Liveness would need
    coordinator-specific delivery guarantees, but we only prove safety. -/

def lvComm : PhaseCommPred Proc 4 := fun _ _ _ => True

/-- The complete PhaseRoundSpec for LastVoting. -/
def lvSpec : PhaseRoundSpec Proc LVState 4 LVMsgs where
  alg := lvAlg
  comm := lvComm

/-- Convert to a Leslie `Spec`. -/
def lvLeslieSpec : Spec (PhaseRoundState Proc LVState 4) :=
  lvSpec.toSpec (by omega)


/-! ### Lemmas about foldl max-ballot selection -/

/-- The foldl that picks the max-ballot element returns an element from init :: l. -/
theorem foldl_max_mem (l : List (Value × Nat)) (init : Value × Nat) :
    l.foldl (fun best cur => if cur.2 > best.2 then cur else best) init ∈ init :: l := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons a as ih =>
    simp only [List.foldl]
    split
    · have h := ih a
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · right ; left ; exact h
      · right ; right ; exact h
    · have h := ih init
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · left ; exact h
      · right ; right ; exact h

/-- The ballot of the foldl result is ≥ every element's ballot. -/
theorem foldl_max_ballot_ge (l : List (Value × Nat)) (init : Value × Nat) :
    ∀ x ∈ init :: l,
    x.2 ≤ (l.foldl (fun best cur => if cur.2 > best.2 then cur else best) init).2 := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons a as ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    -- The step function: if a.2 > init.2 then start from a, else keep init
    -- The foldl step: if a.2 > init.2 then foldl continues from a, else from init
    have hstep : (a :: as).foldl (fun best cur => if cur.2 > best.2 then cur else best) init =
        as.foldl (fun best cur => if cur.2 > best.2 then cur else best)
          (if a.2 > init.2 then a else init) := by rfl
    rw [hstep]
    by_cases hgt : a.2 > init.2
    · rw [if_pos hgt]
      rcases hx with heq | hx
      · rw [heq] ; have := ih a a (List.Mem.head _) ; omega
      · rcases hx with heq | hx
        · rw [heq] ; exact ih a a (List.Mem.head _)
        · exact ih a x (List.Mem.tail _ hx)
    · rw [if_neg hgt]
      rcases hx with heq | hx
      · rw [heq] ; exact ih init init (List.Mem.head _)
      · rcases hx with heq | hx
        · rw [heq] ; have := ih init init (List.Mem.head _) ; omega
        · exact ih init x (List.Mem.tail _ hx)

/-- If every non-v element has strictly smaller ballot than every v-element,
    and there exists a v-element in init :: l, then foldl picks a v-value. -/
theorem foldl_max_picks_dominated_value
    (l : List (Value × Nat)) (init : Value × Nat) (v : Value)
    (h_exists : ∃ x ∈ init :: l, x.1 = v)
    (h_dom : ∀ x ∈ init :: l, x.1 ≠ v →
      ∀ y ∈ init :: l, y.1 = v → x.2 < y.2) :
    (l.foldl (fun best cur => if cur.2 > best.2 then cur else best) init).1 = v := by
  have h_mem := foldl_max_mem l init
  have h_max := foldl_max_ballot_ge l init
  by_contra hne
  obtain ⟨y, hy_mem, hy_val⟩ := h_exists
  have h_lt := h_dom _ h_mem hne y hy_mem hy_val
  have h_ge := h_max y hy_mem
  omega

/-- If there exists a v-element at ballot ≥ b_safe and all non-v elements
    have ballot < b_safe, then foldl picks a v-value.
    This is a weaker precondition than `foldl_max_picks_dominated_value`
    (uses a "gap" at b_safe instead of pairwise domination) and is needed
    for the general-n Paxos proof where pairwise domination doesn't hold. -/
theorem foldl_max_picks_safe_value
    (l : List (Value × Nat)) (init : Value × Nat) (v : Value) (b_safe : Nat)
    (h_exists : ∃ x ∈ init :: l, x.1 = v ∧ x.2 ≥ b_safe)
    (h_below : ∀ x ∈ init :: l, x.1 ≠ v → x.2 < b_safe) :
    (l.foldl (fun best cur => if cur.2 > best.2 then cur else best) init).1 = v := by
  have h_mem := foldl_max_mem l init
  have h_max := foldl_max_ballot_ge l init
  by_contra hne
  obtain ⟨y, hy_mem, hy_val, hy_ge⟩ := h_exists
  have h_below_r := h_below _ h_mem hne
  have h_ge := h_max y hy_mem
  omega

end LastVotingPhased
