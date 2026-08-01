# TileLink Model Sequence and Refinement History

This document records the intended sequence of TileLink TL-C models in Leslie,
from the smallest proof-friendly abstraction to a much more complete TL-C
model. The goal is not just project planning. It is also to preserve a worked
example of how to model a complex protocol by introducing one semantic burden
at a time and proving a stable theorem before adding the next burden.

The current codebase already covers the early part of this sequence:

- shared TileLink vocabulary and helper lemmas are in place
- an atomic single-line coherence model is implemented and proved
- the atomic model already refines to a sequential one-line memory view
- the first explicit message-level slice is implemented for acquires plus
  probes, grants, and grant acknowledgments
- the explicit release path and its preservation proofs are now in place

Everything after that is the staged path toward a fuller TL-C model.

## Why keep this history

For complex distributed protocols, the hard part is usually not writing one big
model. The hard part is choosing a sequence of models where:

- each stage introduces one new source of semantic complexity
- the proof burden stays local to that new feature
- the previous theorem becomes either a reusable lemma or a refinement target
- the files stay short enough that the proof structure remains legible

This document is meant to preserve that modeling discipline explicitly.

## General stepwise-refinement principles

These principles are adapted to TileLink, but they are meant to be reusable for
future Leslie developments as well. Following `docs/proof-strategy-help.md`,
the key tactic is to make each stage small enough that frame lemmas,
hierarchical invariants, and action-local preservation proofs do most of the
work.

### Principle 1: Separate semantic novelty from transport novelty

First prove who may own data and how permissions move. Only after that should
the model expose the transport layer details that realize the same transfer.

For TileLink, that means:

- first prove atomic permission-transfer waves
- then split the same wave into explicit A/B/C/D/E messages

### Principle 2: Add one kind of concurrency at a time

Do not introduce all legal overlaps from the concrete spec at once.

Instead:

- start with at most one active coherence wave
- then add explicit pending probes
- then add explicit grants and acknowledgments
- only later add release overlap, access overlap, and forwarded traffic

### Principle 3: Each stage should have a theorem, not just a model

A stage is complete only when it has:

- a clear statement of what it abstracts away
- a proved invariant or refinement theorem
- a stable interface for the next stage

Otherwise the next stage has no trustworthy foundation.

### Principle 4: Use refinement to retire proof obligations

When a later model is more detailed, it should not have to re-prove every
property from scratch. Prefer proving that the detailed model refines a simpler
one whose safety theorem is already established.

### Principle 5: Group proofs by footprint

Following the proof-strategy guide:

- actions should be factored into named predicates or small action families
- frame lemmas should capture what each action does not change
- invariants should be split by read footprint

This matters even more than usual for TileLink, because channel state explodes
quickly once explicit B/C/D/E traffic appears.

### Principle 6: Keep every stage honest about what is missing

Each stage below lists:

- what new features it adds
- what it still collapses or omits
- what theorem it should prove
- why that theorem is the right stopping point

That explicit omission list is part of the design, not an apology.

## Sequence of models

Status markers:

- `done`: implemented and proved at the intended checkpoint
- `active`: implemented in part; currently being extended
- `planned`: not implemented yet

### Stage 0: Shared TileLink Vocabulary

Status: `done`

Files:

- `Types.lean`
- `Permissions.lean`
- `Common.lean`

What this stage adds:

- TileLink-shaped permissions and parameter enums
- shared opcode types
- basic cache-line representation
- helper lemmas about permission growth, pruning, readability, and dirtiness

What it intentionally omits:

- protocol transitions
- global invariants
- any notion of concurrency

Theorem target:

- local algebraic lemmas only

Why this stage exists:

- isolate spec vocabulary from protocol structure
- prevent later proof files from duplicating case analysis over TileLink params

General lesson:

- shared protocol vocabulary deserves its own module boundary before the first
  executable model exists

### Stage 1a: Atomic Single-Line Coherence Skeleton

Status: `done`

Files:

- `Atomic/Model.lean`
- `Atomic/Invariant.lean`
- `Atomic/StepProof.lean`
- `Atomic/Theorem.lean`

What this stage adds:

- one manager and `n` symmetric masters
- one cache line only
- atomic `AcquireBlock`, `AcquirePerm`, `Release`, `ReleaseData`, `GrantAck`,
  and `ReleaseAck`-style transitions
- home memory, directory summary, and local permission/data state

What it intentionally omits:

- explicit A/B/C/D/E channels
- per-message ordering
- explicit probe messages
- source/sink bookkeeping beyond abstract metadata

Theorem target:

- atomic safety invariant:
  writer exclusivity, line well-formedness, directory agreement, pending-ack
  discipline, and clean/dirty data coherence

Why this stage exists:

- establish the coherence meaning of TL-C permissions before dealing with
  network detail

General lesson:

- for cache coherence, permission-transfer semantics should be proved in a
  model that is still simple enough to understand in one screen

### Stage 1b: Atomic Wave Splitting and Sequential Refinement

Status: `done`

Files:

- `Atomic/Model.lean`
- `Atomic/Refinement.lean`

What this stage adds:

- `AcquirePerm` as permission-only, without valid data
- split pending-grant metadata for scheduled vs delivered phases
- explicit `finishGrant`
- logical-data view of the line
- refinement to a sequential one-line memory abstraction

What it intentionally omits:

- explicit messages
- explicit per-probe responses as separate transitions
- realistic same-block overlap beyond the simplified pending-ack discipline

Theorem target:

- sequential one-line refinement theorem on top of the atomic safety theorem

Why this stage exists:

- prove that the atomic TL-C-like model already enforces the intended memory
  behavior
- give later message-level work a simpler semantic target

General lesson:

- a refinement theorem early in the project helps prevent the detailed model
  from drifting away from the intended semantic core

### Stage 2a: Message-Level Acquire Submission

Status: `done`

Files:

- `Messages/ModelDefs.lean`
- `Messages/Helpers.lean`
- `Messages/Model.lean`
- `Messages/FrameLemmas.lean`
- `Messages/InvariantCore.lean`
- `Messages/InvariantChannels.lean`
- `Messages/InitProof.lean`
- `Messages/StepAcquire.lean`

What this stage adds:

- explicit A/B/C/D/E endpoint slots
- message records for coherence traffic
- manager transaction state
- send-acquire and receive-acquire transitions

What it intentionally omits:

- explicit probe handling at masters
- grant delivery
- release traffic
- message-level refinement

Theorem target:

- invariant for the acquire-submission slice

Why this stage exists:

- separate the introduction of explicit messages from the introduction of
  explicit invalidation effects

General lesson:

- when transport detail is first introduced, start with the smallest slice
  that exercises channel well-formedness and manager bookkeeping

### Stage 2b: Message-Level Probe Scheduling and Probe Acknowledgments

Status: `done`

Files:

- `Messages/StepProbe.lean`
- `Messages/Theorem.lean`

What this stage adds:

- explicit `recvProbeAtMaster`
- explicit `recvProbeAckAtManager`
- manager phase progression from `probing` to `grantReady`
- temporary directory/local mismatch discipline while C-channel acks are still
  in flight

What it intentionally omits:

- D-channel grant delivery
- E-channel `GrantAck`
- C/D release paths
- stronger serialization facts about completed transactions

Theorem target:

- the first message-level theorem for the acquire/probe wave:
  `messages_acquire_inv_invariant`

Why this stage exists:

- validate the first real decomposition of an atomic coherence wave into
  explicit message steps

General lesson:

- the first explicit-message theorem should usually stop at the first protocol
  cut where the manager has enough information to decide the next phase

### Stage 2c: Explicit Grant Delivery and `GrantAck`

Status: `done`

Files:

- `Messages/StepGrant.lean`
- `Messages/Theorem.lean`

What this stage adds:

- D-channel `Grant` and `GrantData`
- E-channel `GrantAck`
- sink allocation and sink matching as live obligations
- transition from `grantReady` to delivered-grant and then to idle

What it can still omit:

- releases
- forwarded TL-UH/TL-UL accesses
- multibeat data

Theorem target:

- message-level safety for the full acquire/grant/ack round-trip
- stronger serialization invariants connecting active transaction state,
  pending sink metadata, and D/E channel contents

Why this stage should come next:

- `GrantAck` is the spec’s core same-block serialization mechanism, so the
  message model is not yet a serious TL-C model without it

General lesson:

- after probe traffic, the next detail to expose should be the serialization
  edge that closes the wave

Current checkpoint note:

- the current message theorem now covers the acquire/probe/grant path through
  explicit D and E handling
- release traffic is now present in both the executable model and the proved
  message-level invariant

### Stage 2d: Explicit Release and Release Acknowledgment Paths

Status: `active`

Files:

- `Messages/StepRelease.lean`

What this stage adds:

- C-channel `Release` and `ReleaseData`
- D-channel `ReleaseAck`
- manager-side processing of voluntary downgrades and writeback
- local `releaseInFlight` bookkeeping

What it can still omit:

- non-coherence access traffic
- forwarded B/C access path
- multibeat details

Theorem target:

- safety and data-coherence preservation across both manager-driven invalidation
  waves and cache-driven release waves

Current checkpoint:

- `Messages/Model.lean` (with helpers in `Helpers.lean` and types in
  `ModelDefs.lean`) includes the release send/receive/ack actions
- the core and channel invariants mention release messages and
  `pendingReleaseAck`
- `Messages/Theorem.lean` now routes through `Messages/StepRelease.lean`
- `Messages/StepRelease.lean` now proves preservation for the explicit release
  slice

Why this stage is separate:

- releases introduce a different source of protocol initiative and should not
  be mixed with acquire/grant work unless necessary

General lesson:

- separate "manager pulls permissions back" from "cache gives permissions up"
  when building the proof decomposition
- once a new action family is stable in the model, it can still be useful to
  checkpoint the proof split before finishing every preservation lemma

### Stage 2e: Message-Level Refinement Back to the Atomic Model

Status: `active`

Likely files:

- `Messages/Refinement.lean`

What this stage should add:

- a refinement map from explicit messages and transaction state back to the
  atomic wave-level model
- refinement-specific reachability facts for the current message slice, so the
  forward simulation can talk about the same semantic fragment as Stage 1

What it intentionally omits:

- parameterized focus/environment abstraction
- full TL-C optional features

Theorem target:

- every message-level execution refines the already-proved atomic model

Current checkpoint:

- `Messages/Refinement.lean` now exists and contains the first refinement-side
  helper invariants: `noDirtyInv`, `txnDataInv`, and `refinementInv`, together
  with their init lemmas
- the message model has been tightened to match the current atomic scope more
  closely:
  manager-side `AcquireBlock` now accepts only the Stage 1 no-dirty,
  requester-from-`N` cases, and queued C-channel releases are now serialized
  on the single modeled line
- live acquire transactions now carry a `preLines` snapshot of the pre-wave
  local cache-line state; the refinement map uses that snapshot so explicit
  probe handling can stutter against the atomic model
- the refinement map also synthesizes the abstract post-release
  `pendingReleaseAck` view from a queued clean release, which aligns concrete
  release timing with the atomic release step more closely
- the atomic model now accepts `NtoN` release/report transitions, so the
  current atomic/message pair is closer to the TL-C prune/report space
- the forward-simulation theorem itself is still pending

Why this stage matters:

- it prevents the message model from requiring a separate top-to-bottom proof
  of every semantic fact already captured by Stage 1

General lesson:

- message-level safety theorems are easier to manage if they can discharge
  semantic obligations by refinement instead of restating them all directly
- when the concrete protocol exposes intermediate transport steps that mutate
  local state before the abstract linearization point, it is often cheaper to
  snapshot the pre-step semantic state than to force the abstract model to grow
  a matching intermediate phase

### Stage 3: More Complete Single-Line TL-C Transfer Layer

Status: `planned`

What this stage should add:

- remaining single-line coherence-transfer features from TL-C that fit the
  current one-manager scope
- stronger same-block exclusion rules
- more faithful source/sink lifecycle constraints
- possibly `denied` and `corrupt` bits if they are needed for the target proof

Likely theorem targets:

- a stronger message-level invariant covering the full single-line transfer
  discipline
- refinement to the Stage 2 model or directly to the atomic model

Why this stage exists:

- there is value in finishing a realistic single-line transfer protocol before
  introducing forwarded accesses, multiple lines, or hierarchy

General lesson:

- finish one semantic slice completely before widening the address or topology
  dimensions

### Stage 4: Forwarded Accesses and the B/C Access Path

Status: `planned`

What this stage should add:

- forwarded non-coherence traffic on B/C
- interaction between accesses and coherence transfers
- serialization constraints that mix access acks with grant/release acks

Likely theorem targets:

- safety of coexistence between coherence traffic and access traffic
- refined same-block concurrency invariants

Why this stage is late:

- this is orthogonal complexity; it is not needed to validate the core
  coherence protocol first

General lesson:

- postpone orthogonal protocol families until the central coherence discipline
  is stable

### Stage 5: Beyond One Line

Status: `planned`

What this stage should add:

- multiple addresses or an indexed line model
- address-parametric transaction keys
- invariants factored into per-line properties plus cross-line framing lemmas

Likely theorem targets:

- per-line safety lifted to a finite address space
- reuse of single-line invariants via locality arguments

Why this stage is separate:

- multi-line state multiplies proof size quickly unless the single-line proof
  structure is already stable

General lesson:

- prove line-locality first; then widen the address space by decomposition, not
  by rewriting the protocol proof

### Stage 6: Hierarchical and More Faithful Coherence Trees

Status: `planned`

What this stage should add:

- intermediate caches or a more explicit coherence-tree structure
- possible `TrunkOnly`-style internal states
- parent/child relationships in the directory or explicit topology metadata

Likely theorem targets:

- tree-shape coherence invariants
- permission-transfer soundness in a hierarchical topology

Why this stage is late:

- hierarchy changes the shape of the ownership relation itself, not just the
  message schedule

General lesson:

- add hierarchy only after the leaf-level protocol is understood and proved

### Stage 7: Parameterized Scaling and Environment Abstraction

Status: `planned`

Likely files:

- `Parameterized/Model.lean`
- `Parameterized/FocusModel.lean`
- `Parameterized/EnvSummary.lean`
- `Parameterized/EnvProof.lean`
- `Parameterized/Safety.lean`
- `Parameterized/Refinement.lean`

What this stage should add:

- a focus-process proof style
- summarized environment behavior
- soundness of the environment abstraction against the concrete small model

Likely theorem targets:

- safety for arbitrary `n`
- refinement or export theorems connecting the parameterized model back to the
  small-model semantics

Why this stage is late:

- abstraction works best after the small explicit model has stabilized and the
  right environment summary is obvious

General lesson:

- do not guess the environment summary too early; derive it from the concrete
  proof obligations that actually appeared

### Stage 8: Liveness and Deadlock-Oriented Properties

Status: `planned`

What this stage should add:

- fairness assumptions
- progress of probe waves, grants, and acknowledgments
- possibly channel-priority reasoning aligned with TL-C deadlock arguments

Likely theorem targets:

- eventual completion of legal coherence waves
- absence of specific stuck states under fairness

Why this stage is last:

- liveness arguments are fragile if the safety model is still moving

General lesson:

- prove stable safety and refinement layers before introducing fairness

## What "full TL-C spec" should mean here

For this project, "full TL-C spec" should not mean every feature appears in
the first serious theorem. A more realistic meaning is:

- the single-line explicit model covers the full coherence-transfer discipline
- forwarded traffic is modeled if it materially interacts with coherence claims
- source/sink and serialization rules are represented faithfully enough that
  the safety argument depends on them for the right reasons
- hierarchy and parameterization are added only once the leaf-level transfer
  proof is already stable

This is still a staged endpoint, not a single jump.

## Reusable pattern for future complex specs

If this sequence works, the general recipe for future Leslie developments
should look like this:

1. Define shared protocol vocabulary and local algebraic lemmas.
2. Build the smallest executable model that captures the core semantic
   ownership transfer.
3. Prove a safety invariant there.
4. Add a refinement map to the intended abstract behavior.
5. Introduce explicit messages for one action family at a time.
6. Prove message-level invariants in slices, grouped by modification footprint.
7. Refine the explicit model back to the simpler semantic model.
8. Only then scale out in topology, address space, and liveness.

That is the main historical record this document is intended to preserve.
