# Multi-Phase Round Extension for Leslie

## Motivation

The current `RoundAlg` in `Leslie/Round.lean` captures round-based algorithms
where each round is a single send-receive-update cycle. This cleanly models
protocols like OneThirdRule, where every round has the same structure.

However, many important distributed protocols have **multiple phases per
logical round** (variously called a ballot, view, or epoch):

- **Paxos**: 4 phases per ballot (1a: prepare, 1b: promise, 2a: accept, 2b: accepted)
- **Viewstamped Replication**: 2 phases per view change (DoViewChange, StartView) plus normal operation
- **PBFT**: 3 phases per view (pre-prepare, prepare, commit)
- **Two-Phase Commit**: 2 phases (vote, decide)

In the current framework, these are modeled as plain `Spec` values with
ad-hoc phase tracking (see `VRViewChange.lean` and `BallotLeader.lean`).
This works but loses the structural benefits of `RoundAlg`:

1. No reusable proof rules (must reprove induction structure each time)
2. No connection to the HO communication model per phase
3. No path to cutoff results for multi-phase protocols
4. Phase sequencing is encoded manually, making specs error-prone

## Design Overview

We introduce `PhaseRoundAlg`, a generalization of `RoundAlg` where each
logical round consists of a fixed sequence of phases. Each phase is a
communication-closed send-receive-update cycle with its own message type.
Phases within a round are sequenced: phase 0 completes before phase 1
begins, and so on.

The key insight is that a k-phase round is isomorphic to k consecutive
single-phase rounds with a structured state that tracks position within
the logical round. The `PhaseRoundAlg` abstraction makes this structure
explicit and provides dedicated proof rules that exploit it.

## Proposed Lean Definitions

### Phase Specification

A single phase within a multi-phase round. Each phase has its own message
type, send function, and update function.

```lean
/-- A single phase of a multi-phase round.
    - `P` : process type
    - `S` : local state type
    - `M` : message type for this phase -/
structure Phase (P : Type) (S : Type) (M : Type) where
  /-- The message that process `p` broadcasts in this phase. -/
  send : P → S → M
  /-- How process `p` updates its state given received messages. -/
  update : P → S → (P → Option M) → S
```

### Phase-Indexed Message Type

Since different phases have different message types, we need a way to
associate a message type with each phase index.

```lean
/-- A family of message types indexed by phase number.
    `MsgType i` is the message type for phase `i`. -/
abbrev PhaseMessages (k : Nat) := Fin k → Type
```

### Multi-Phase Round Algorithm

```lean
/-- A multi-phase round-based distributed algorithm.
    - `P` : process type
    - `S` : local state type
    - `k` : number of phases per round
    - `Msgs` : message type for each phase

    Each logical round consists of `k` phases executed in sequence.
    Phase `i` uses message type `Msgs i` and has its own send/update. -/
structure PhaseRoundAlg (P : Type) (S : Type)
    (k : Nat) (Msgs : PhaseMessages k) where
  /-- Initial local state predicate for each process. -/
  init : P → S → Prop
  /-- The phase specifications, one per phase index. -/
  phases : (i : Fin k) → Phase P S (Msgs i)
```

### Global State

```lean
/-- Global state of a multi-phase round system.
    Tracks both the logical round number and the current phase
    within that round. -/
structure PhaseRoundState (P : Type) (S : Type) (k : Nat) where
  /-- Current logical round number (0 = initial). -/
  round : Nat
  /-- Current phase within the round (0 ≤ phase < k). -/
  phase : Fin k
  /-- Local state of each process. -/
  locals : P → S
```

### Message Delivery (Per Phase)

```lean
/-- Messages delivered to process `p` in a given phase. -/
def phase_delivered (ph : Phase P S M) (locals : P → S)
    (ho : HOCollection P) (p : P) : P → Option M :=
  fun q => if ho p q then some (ph.send q (locals q)) else none
```

### Phase Transition

```lean
/-- One phase step: all processes transition simultaneously within
    the current phase, then advance to the next phase (or next round). -/
def phase_step (alg : PhaseRoundAlg P S k Msgs)
    (ho : HOCollection P)
    (s s' : PhaseRoundState P S k) : Prop :=
  let ph := alg.phases s.phase
  -- Phase index advances (with wraparound to next round)
  (if h : s.phase.val + 1 < k then
    s'.round = s.round ∧ s'.phase = ⟨s.phase.val + 1, h⟩
  else
    s'.round = s.round + 1 ∧ s'.phase = ⟨0, by omega⟩) ∧
  -- All processes update using this phase's send/update
  ∀ p, s'.locals p = ph.update p (s.locals p)
    (phase_delivered ph s.locals ho p)
```

### Communication Predicate (Per Phase)

```lean
/-- Communication predicate for multi-phase rounds.
    The predicate can depend on both the round number and the
    current phase, allowing different fault assumptions per phase. -/
def PhaseCommPred (P : Type) (k : Nat) :=
  Nat → Fin k → HOCollection P → Prop
```

### Multi-Phase Round Specification

```lean
/-- A complete multi-phase round specification. -/
structure PhaseRoundSpec (P : Type) (S : Type)
    (k : Nat) (Msgs : PhaseMessages k) where
  alg : PhaseRoundAlg P S k Msgs
  comm : PhaseCommPred P k
```

### Conversion to Leslie `Spec`

```lean
/-- Convert a multi-phase round specification to a Leslie `Spec`.
    The HO collection is existentially quantified per phase step. -/
def PhaseRoundSpec.toSpec (prs : PhaseRoundSpec P S k Msgs) :
    Spec (PhaseRoundState P S k) where
  init := fun s =>
    s.round = 0 ∧ s.phase = ⟨0, by omega⟩ ∧
    ∀ p, prs.alg.init p (s.locals p)
  next := fun s s' =>
    ∃ ho, prs.comm s.round s.phase ho ∧
      phase_step prs.alg ho s s'
```

### Flattening to Single-Phase Rounds

An important structural result: a k-phase round algorithm can be
"flattened" into a single-phase round algorithm over an enriched state.
This connects multi-phase rounds to the existing `RoundAlg` theory.

```lean
/-- The flattened state: local state tagged with phase position. -/
structure FlatState (S : Type) (k : Nat) where
  phaseTag : Fin k
  inner : S

/-- The flattened message type: a dependent sum over phase messages. -/
inductive FlatMsg (k : Nat) (Msgs : PhaseMessages k) where
  | mk (i : Fin k) (m : Msgs i) : FlatMsg k Msgs

/-- Flatten a multi-phase round algorithm into a single-phase one.
    Each "round" of the flat algorithm corresponds to one phase of
    the original. The phase tag in the state ensures phases execute
    in sequence. -/
def PhaseRoundAlg.flatten (alg : PhaseRoundAlg P S k Msgs) :
    RoundAlg P (FlatState S k) (FlatMsg k Msgs) where
  init := fun p fs => fs.phaseTag = ⟨0, by omega⟩ ∧ alg.init p fs.inner
  send := fun p fs =>
    .mk fs.phaseTag ((alg.phases fs.phaseTag).send p fs.inner)
  update := fun p fs msgs =>
    let ph := alg.phases fs.phaseTag
    let phase_msgs : P → Option (Msgs fs.phaseTag) := fun q =>
      match msgs q with
      | some (.mk i m) =>
        if h : i = fs.phaseTag then some (h ▸ m) else none
      | none => none
    let new_inner := ph.update p fs.inner phase_msgs
    let new_tag := if h : fs.phaseTag.val + 1 < k
      then ⟨fs.phaseTag.val + 1, h⟩
      else ⟨0, by omega⟩
    { phaseTag := new_tag, inner := new_inner }

/-- The flattened spec simulates the multi-phase spec (bisimulation).
    This theorem lets us transfer results between the two views. -/
theorem PhaseRoundAlg.flatten_bisim
    (prs : PhaseRoundSpec P S k Msgs)
    -- ... (statement relating prs.toSpec and prs.alg.flatten) :=
  sorry
```

## Proof Rules

### Phase-Aware Round Invariant

The main proof rule: an invariant that is preserved by each phase step.

```lean
/-- **Phase Round Invariant Rule**: if `inv` holds initially and is
    preserved by every phase step (for any phase, any valid HO
    collection), then `inv` holds at all times. -/
theorem phase_round_invariant
    (prs : PhaseRoundSpec P S k Msgs)
    (inv : PhaseRoundState P S k → Prop)
    (hinit : ∀ s, prs.toSpec.init s → inv s)
    (hstep : ∀ s ho, inv s → prs.comm s.round s.phase ho →
             ∀ s', phase_step prs.alg ho s s' → inv s') :
    pred_implies prs.toSpec.safety [tlafml| □ ⌜inv⌝] := by
  apply init_invariant hinit
  intro s s' ⟨ho, hcomm, hphase⟩ hinv
  exact hstep s ho hinv hcomm s' hphase
```

### Phase-Specific Invariants

Often, invariants hold only at specific phases (e.g., "after the promise
phase, all acceptors have promised"). This rule supports phase-conditional
invariants.

```lean
/-- **Phase-Conditional Invariant**: an invariant that holds whenever
    the system is at or past a specific phase. -/
theorem phase_conditional_invariant
    (prs : PhaseRoundSpec P S k Msgs)
    (target_phase : Fin k)
    (inv : PhaseRoundState P S k → Prop)
    (hinit : ∀ s, prs.toSpec.init s →
      s.phase = target_phase → inv s)
    (hstep_enter : ∀ s ho, prs.comm s.round s.phase ho →
      ∀ s', phase_step prs.alg ho s s' →
      s'.phase = target_phase → inv s')
    (hstep_preserve : ∀ s ho, inv s →
      s.phase.val ≥ target_phase.val →
      prs.comm s.round s.phase ho →
      ∀ s', phase_step prs.alg ho s s' →
      s'.round = s.round → inv s') :
    pred_implies prs.toSpec.safety
      [tlafml| □ ⌜fun s => s.phase.val ≥ target_phase.val → inv s⌝] :=
  sorry
```

### Cross-Phase Reasoning

A rule for invariants that relate the states across phase boundaries.
The key pattern: information gathered in phase i constrains behavior
in phase i+1.

```lean
/-- **Cross-Phase Invariant**: an invariant relating two consecutive
    phases. The invariant `inv_pre` established at phase `i` implies
    `inv_post` at phase `i+1`, using a transfer lemma. -/
theorem cross_phase_transfer
    (prs : PhaseRoundSpec P S k Msgs)
    (i : Fin k) (hi : i.val + 1 < k)
    (inv_pre : PhaseRoundState P S k → Prop)
    (inv_post : PhaseRoundState P S k → Prop)
    (h_pre_inductive : ∀ s ho, inv_pre s → s.phase = i →
      prs.comm s.round s.phase ho →
      ∀ s', phase_step prs.alg ho s s' → inv_pre s')
    (h_transfer : ∀ s ho, inv_pre s → s.phase = i →
      prs.comm s.round s.phase ho →
      ∀ s', phase_step prs.alg ho s s' →
      s'.phase = ⟨i.val + 1, hi⟩ → inv_post s') :
    -- ... (conclusion: inv_pre at phase i implies inv_post at phase i+1)
    True := sorry
```

### Phase Round Refinement

```lean
/-- **Phase Round Refinement**: a multi-phase spec refines an abstract
    spec, with stuttering allowed on intra-round phases. -/
theorem phase_round_refinement
    (prs : PhaseRoundSpec P S k Msgs)
    (abstract : Spec τ)
    (f : PhaseRoundState P S k → τ)
    (hinit : ∀ s, prs.toSpec.init s → abstract.init (f s))
    (hstep : ∀ s ho, prs.comm s.round s.phase ho →
             ∀ s', phase_step prs.alg ho s s' →
             abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f prs.toSpec.safety abstract.safety_stutter :=
  sorry
```

### Quorum Intersection Across Phases

The central proof technique for multi-phase protocols: quorums used in
different phases must overlap.

```lean
/-- **Cross-Phase Quorum Intersection**: if phase `i` uses a quorum
    Q_i and phase `j` uses a quorum Q_j, and both require majority,
    then Q_i ∩ Q_j is nonempty. This is the multi-phase analogue of
    `majority3_intersect` from VRViewChange.lean. -/
theorem cross_phase_quorum_intersection
    (n : Nat)
    (ho_i ho_j : HOCollection (Fin n))
    (p_i p_j : Fin n)
    (h_i : ((List.finRange n).filter fun q => ho_i p_i q).length * 2 > n)
    (h_j : ((List.finRange n).filter fun q => ho_j p_j q).length * 2 > n) :
    ∃ q : Fin n, ho_i p_i q = true ∧ ho_j p_j q = true := by
  -- Follows from filter_disjoint_length_le and pigeonhole
  sorry
```

## Refactoring Existing Examples

### BallotLeader as PhaseRoundAlg

The current `BallotLeader.lean` manually encodes a 2-phase protocol
(New phase + Ack phase) with explicit round tracking. Here is how it
would look as a `PhaseRoundAlg`.

```lean
namespace BallotLeaderPhased

variable (n : Nat)

/-- Local state (same as before). -/
structure LState (n : Nat) where
  picked : Option (Fin n)
  leader : Option (Fin n)
  deriving DecidableEq, Repr

/-- Phase 0 message: bid or no-bid. -/
inductive NewMsg (n : Nat) where
  | bid (id : Fin n)
  | noBid

/-- Phase 1 message: pick or no-pick. -/
inductive AckMsg (n : Nat) where
  | pick (id : Fin n)
  | noPick

/-- Message types per phase. -/
def blMsgs : PhaseMessages 2
  | ⟨0, _⟩ => NewMsg n
  | ⟨1, _⟩ => AckMsg n

/-- The ballot leader as a 2-phase round algorithm.

    Note: the original BallotLeader uses a nondeterministic oracle
    for bidding decisions. In the PhaseRoundAlg framework, this
    oracle would be part of the local state (set during init) or
    modeled as additional nondeterminism in the send function.
    For simplicity, we assume each process has a `bidding : Bool`
    field in its state set at init. -/
def blPhaseAlg : PhaseRoundAlg (Fin n) (LState n) 2 (blMsgs n) where
  init := fun _p s => s.picked = none ∧ s.leader = none
  phases := fun
    | ⟨0, _⟩ => {
        send := fun p s =>
          -- In the original, bidding is oracle-driven.
          -- Here we'd need the bid decision in state.
          NewMsg.noBid  -- simplified
        update := fun _p s msgs =>
          let bids := (List.finRange n).filterMap fun q =>
            match msgs q with
            | some (.bid id) => some id
            | _ => none
          { s with picked := List.minFin? bids }
      }
    | ⟨1, _⟩ => {
        send := fun _p s =>
          match s.picked with
          | some c => AckMsg.pick c
          | none => AckMsg.noPick
        update := fun _p s msgs =>
          let picks := (List.finRange n).filterMap fun q =>
            match msgs q with
            | some (.pick id) => some id
            | _ => none
          { s with leader := findMajority n picks }
      }
```

**What changes:**
- The `round` field and manual `stepNew`/`stepAck`/`stepDone` transitions
  are replaced by the framework's `phase_step` and `PhaseRoundState`.
- The `ballotLeaderSpec` definition reduces to `blPhaseSpec.toSpec`.
- The safety proof uses `phase_round_invariant` instead of manual
  case-splitting on the round number.

**What stays the same:**
- The core logic (bid collection, pick majority) is unchanged.
- The pigeonhole argument (`picks_pigeonhole`) still applies.
- Helper lemmas like `countVotes_le_supporters` carry over directly.

### VRViewChange as PhaseRoundAlg

The current `VRViewChange.lean` models a 2-phase protocol (normal
operation + view change) as a plain `Spec`. Here is the refactoring.

```lean
namespace VRViewChangePhased

/-- Phase 0 message: the leader's proposed command. -/
structure NormalOpMsg where
  cmd : Option Cmd

/-- Phase 1 message: DoViewChange carrying replica state. -/
structure DVCMsg where
  log : Option Cmd
  accepted : Bool

/-- Message types per phase. -/
def vrMsgs : PhaseMessages 2
  | ⟨0, _⟩ => NormalOpMsg
  | ⟨1, _⟩ => DVCMsg

/-- Local state. -/
structure RState where
  log : Option Cmd
  accepted : Bool
  newLeaderLog : Option Cmd

def vrPhaseAlg : PhaseRoundAlg Replica RState 2 vrMsgs where
  init := fun _r s =>
    s.log = none ∧ s.accepted = false ∧ s.newLeaderLog = none
  phases := fun
    | ⟨0, _⟩ => {
        -- Normal operation: leader (replica 0) proposes
        send := fun _r _s => { cmd := none }  -- simplified
        update := fun r s msgs =>
          match msgs ⟨0, by omega⟩ with
          | some msg =>
            match msg.cmd with
            | some c => { s with log := some c, accepted := true }
            | none => s
          | none => s
      }
    | ⟨1, _⟩ => {
        -- View change: replicas send DVC to new leader (replica 1)
        send := fun _r s => { log := s.log, accepted := s.accepted }
        update := fun r s msgs =>
          if r = ⟨1, by omega⟩ then
            -- New leader collects DVCs and picks log
            let heard := (List.finRange 3).filterMap fun q =>
              match msgs q with
              | some dvc => if dvc.accepted then dvc.log else none
              | none => none
            { s with newLeaderLog := heard.head? }
          else s
      }
```

**What changes:**
- Phase tracking (`s.phase = 0`, `s.phase = 1`, etc.) is automatic.
- The `stepDone` stutter step is no longer needed; the framework
  handles round completion.
- The `vrSpec` definition simplifies to `vrPhaseSpec.toSpec`.
- The safety proof can use `phase_round_invariant`, eliminating the
  manual three-way case split on `stepNormalOp / stepViewChange / stepDone`.

**What the quorum intersection proof would look like:**

```lean
theorem vc_safety_phased :
    pred_implies vrPhaseSpec.toSpec.safety [tlafml| □ ⌜vc_safety⌝] := by
  apply phase_round_invariant
  · -- Init: newLeaderLog = none, vacuously true
    intro s ⟨_, _, hinit⟩ cmd _ _ hne
    sorry -- similar to original
  · -- Phase step preservation
    intro s ho hinv hcomm s' hstep
    -- The framework gives us s.phase (which phase we're in)
    -- Case split on s.phase:
    --   Phase 0: newLeaderLog stays none
    --   Phase 1: quorum intersection via cross_phase_quorum_intersection
    sorry
```

## Extending Cutoff Theory to Multi-Phase Protocols

### The Challenge

The current cutoff theory in `Leslie/Cutoff.lean` applies to
**symmetric threshold protocols** with a single phase per round.
The key assumptions are:

1. **Process symmetry**: send and update are process-ID-independent.
2. **Threshold-based decisions**: updates depend on messages only through
   threshold comparisons.
3. **Counting invariants**: safety properties talk about counts, not
   identities.

Multi-phase protocols introduce a complication: information flows
**across phases within a round**. Phase 1 of Paxos (prepare/promise)
produces promises that constrain phase 2 (accept). The state after
phase 1 is not just a value count -- it includes structured information
(which ballot was promised, what was the highest accepted value).

### When Cutoffs Still Work

Cutoffs extend naturally when **each phase individually** satisfies the
symmetry/threshold conditions:

**Per-phase threshold abstraction.** If each phase's send and update
functions are symmetric (process-ID-independent) and threshold-based,
then the configuration after each phase depends only on the threshold
view of the configuration going into that phase.

```lean
/-- Multi-phase configuration: counts at each phase boundary. -/
structure PhaseConfig (k_vals : Nat) (k_phases : Nat) (n : Nat) where
  /-- Configuration at each phase boundary (including initial). -/
  configs : Fin (k_phases + 1) → Config k_vals n

/-- Symmetric threshold multi-phase algorithm. -/
structure SymThreshPhaseAlg (k_vals : Nat) (k_phases : Nat)
    (α_num α_den : Nat) where
  /-- Per-phase update function (same structure as SymThreshAlg). -/
  phase_update : Fin k_phases → Fin k_vals → ThreshView k_vals → Fin k_vals
```

The cutoff bound for a k-phase protocol with k_vals value types and
threshold alpha is the same as the single-phase bound, because:

1. The threshold view has at most `2^k_vals` possibilities per phase.
2. After k_phases phases, the total number of reachable threshold-view
   sequences is at most `(2^k_vals)^k_phases` -- still finite and
   independent of n.
3. The scaling lemma (`thresh_scaling_down`) applies at each phase
   boundary independently.

```lean
/-- **Multi-Phase Cutoff Theorem**: if a threshold-determined invariant
    holds for all n <= K and all phase sequences, it holds for all n.

    The bound K is the same as the single-phase bound because each
    phase's threshold view depends only on the configuration, not on
    which specific phase we're in. -/
theorem phase_cutoff_reliable
    (alg : SymThreshPhaseAlg k_vals k_phases α_num α_den)
    (hα : α_num < α_den)
    (h_half : 2 * α_num ≥ α_den)
    (inv : (n : Nat) → PhaseConfig k_vals k_phases n → Prop)
    (h_thresh : ∀ n₁ n₂
      (c₁ : PhaseConfig k_vals k_phases n₁)
      (c₂ : PhaseConfig k_vals k_phases n₂),
      (∀ i, (c₁.configs i).threshView α_num α_den =
            (c₂.configs i).threshView α_num α_den) →
      (inv n₁ c₁ ↔ inv n₂ c₂))
    (h_all_small : ∀ n, n ≤ cutoffBound k_vals α_num α_den →
      ∀ c : PhaseConfig k_vals k_phases n, inv n c) :
    ∀ n (c : PhaseConfig k_vals k_phases n), inv n c :=
  sorry
```

### When Cutoffs Do Not Directly Apply

Protocols like Paxos break the symmetry assumption:

- **Role asymmetry**: proposers and acceptors have different behaviors.
- **Non-threshold decisions**: the "pick the highest ballot" rule in
  Paxos 2a is not a threshold comparison -- it depends on the specific
  ballot numbers reported.
- **Cross-phase dependencies**: the value chosen in phase 2a depends on
  the specific content of phase 1b responses, not just counts.

For these protocols, cutoff results require additional techniques:

1. **Role decomposition**: Separate the process set into roles
   (proposers, acceptors) and apply cutoffs to each role independently
   where symmetry holds within the role.

2. **Partial symmetry**: Even in Paxos, the acceptors are symmetric
   among themselves. Cutoff results may apply to the acceptor
   population while the proposer count remains fixed.

3. **Data-independent arguments**: Some safety properties (like "at most
   one value is chosen") can be reduced to quorum intersection, which
   depends only on quorum sizes, not on n. This avoids the need for
   configuration-level cutoffs entirely.

### Proposed Cutoff Pipeline for Multi-Phase Protocols

```
Protocol (n processes, k phases)
    |
    v
[Per-phase symmetry check]
    |
    +---> All phases symmetric + threshold-based
    |         |
    |         v
    |     Apply phase_cutoff_reliable
    |     (same bound as single-phase)
    |
    +---> Some phases break symmetry
              |
              v
          [Role decomposition]
              |
              v
          Apply cutoff per symmetric sub-population
          + verify cross-role properties separately
```

## Summary of Proof Rules

| Rule | Purpose | Analogous single-phase rule |
|------|---------|---------------------------|
| `phase_round_invariant` | Inductive invariant across all phases | `round_invariant` |
| `phase_conditional_invariant` | Invariant that holds from a specific phase onward | (none) |
| `cross_phase_transfer` | Information flow from phase i to phase i+1 | (none) |
| `phase_round_refinement` | Refinement with per-phase stuttering | `round_refinement` |
| `cross_phase_quorum_intersection` | Quorum overlap across phases | `majority3_intersect` |
| `phase_cutoff_reliable` | Cutoff for symmetric multi-phase protocols | `cutoff_reliable` |
| `PhaseRoundAlg.flatten_bisim` | Equivalence with single-phase view | (none) |

## Design Decisions and Tradeoffs

### Fixed vs. Variable Phase Count

This design uses a **fixed** number of phases `k` per round. An
alternative would allow different rounds to have different numbers of
phases (e.g., Paxos skipping phase 1 when the leader is stable). We
chose fixed `k` for simplicity; variable phase counts can be modeled by
adding "no-op" phases where `send` returns a dummy message and `update`
is the identity.

### Dependent Message Types

Using `PhaseMessages k = Fin k → Type` makes message types depend on
the phase index. This is the most precise encoding (phase 1 messages
cannot appear in phase 2) but introduces dependent types that can
complicate proofs. The flattening construction (`FlatMsg`) provides
an escape hatch: work in the flat (non-dependent) view when the
dependent types become unwieldy.

### Relationship to Existing `RoundAlg`

`PhaseRoundAlg P S 1 (fun _ => M)` is isomorphic to `RoundAlg P S M`.
The flattening construction makes this precise: a 1-phase
`PhaseRoundAlg` flattens to a `RoundAlg` with trivial phase tags.
This means all existing single-phase results and examples remain valid
without modification.

### Phase-Level vs. Round-Level Communication Predicates

We allow the communication predicate to vary by phase
(`PhaseCommPred P k = Nat → Fin k → HOCollection P → Prop`). This
is important for protocols where different phases have different
reliability assumptions (e.g., normal operation may tolerate more
message loss than view change).

## Implementation Plan

1. **Phase 1**: Define `Phase`, `PhaseRoundAlg`, `PhaseRoundState`,
   `phase_step`, and `PhaseRoundSpec.toSpec`. Prove `phase_round_invariant`.

2. **Phase 2**: Implement the flattening construction and prove
   `flatten_bisim`. This validates the design by connecting to the
   existing `RoundAlg` theory.

3. **Phase 3**: Refactor `BallotLeader` and `VRViewChange` to use
   `PhaseRoundAlg`. Verify that the safety proofs simplify.

4. **Phase 4**: Develop `phase_conditional_invariant` and
   `cross_phase_transfer`. Apply to Paxos-style reasoning.

5. **Phase 5**: Extend cutoff theory to multi-phase protocols.
   Implement `SymThreshPhaseAlg` and `phase_cutoff_reliable`.
