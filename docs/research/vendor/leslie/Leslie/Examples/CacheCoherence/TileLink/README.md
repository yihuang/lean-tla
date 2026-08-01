# TileLink TL-C in Leslie

This directory is the planned home for a Leslie model and proof development for
the TileLink cached protocol (TL-C), with emphasis on coherent cache-block
transfers for a single cache line.

## Goal

Build a staged, modular verification effort for TileLink coherence that:

- starts from small, atomic models that are easy to prove
- refines toward explicit message-level models with A/B/C/D/E channels
- keeps invariants split across small files instead of one monolithic proof
- scales to symmetric many-master systems using Leslie's shared-memory
  symmetry and environment-abstraction machinery

## Why this needs its own structure

TileLink TL-C is more than a MESI state machine. The concrete protocol also
tracks:

- explicit transfer messages (`Acquire*`, `Probe*`, `Grant*`, `Release*`)
- transaction identifiers (`source`, `sink`)
- same-block serialization obligations (`GrantAck`, `ReleaseAck`)
- in-flight protocol waves that may overlap without point-to-point ordering

Because of that, the development should not jump directly to a fully explicit
model. The intended approach is:

1. prove an atomic transfer-level model first
2. refine it to an explicit message-level model
3. lift per-process proofs to parameterized systems

## Planned contents

- `README.md`
  This overview and directory roadmap.
- `IMPLEMENTATION_PLAN.md`
  Detailed staged implementation and proof plan.
- `MODEL_SEQUENCE.md`
  Design history of the staged models and the refinement path toward fuller
  TL-C coverage.
- `Types.lean`
  Shared enums and basic records.
- `Permissions.lean`
  Permission lattice and transition classification.
- `Atomic/`
  Small wave-level models and safety proofs.
- `Messages/`
  Explicit channel-level models, invariants, and later refinement back to the
  atomic model.
- `Parameterized/`
  Symmetric shared-memory model, environment abstraction, scaling proofs, and
  later refinement/export theorems.

## Intended first proof scope

The first end-to-end theorem should target:

- one cache line
- one managing slave
- many symmetric masters
- invalidation-based coherence only
- single-beat transfers
- no `denied` or `corrupt`
- safety only

That first scope should prove:

- permission exclusivity / SWMR-style coherence
- data coherence for clean and dirty ownership
- same-block serialization obligations for the simplified transfer set
- refinement to a simple sequential line abstraction

## Existing Leslie patterns to copy

- `GermanSimple.lean`
  Atomic controller-level coherence model.
- `GermanMessages/`
  Explicit message-level model with layered invariants and split proof files.
- `MESIParam.lean`
  Symmetric parameterized cache-coherence development using `SymSharedSpec`.
- `EnvAbstraction.lean`
  Focus/environment abstraction for scaling local proofs to arbitrary `n`.

## Current atomic scope

The current `Atomic/` files are at an early Stage 1b checkpoint:

- `AcquirePerm` installs writable authority without valid data
- `Release` and `ReleaseData` are separate actions with abstract TileLink
  prune/report parameters
- shared state tracks home memory, a directory summary, pending grant metadata,
  and pending `GrantAck`/`ReleaseAck` obligations
- acquires now schedule a pending probe/grant wave, and `finishGrant`
  discharges that wave before `GrantAck`
- the proved safety theorem now covers writer exclusivity, pending-ack
  discipline, directory agreement, local line well-formedness, and clean valid
  data agreement with memory
- a derived theorem now identifies the dirty owner as the source of the
  atomic model's logical line value
- `Atomic/Refinement.lean` now proves refinement to a sequential one-line
  memory via that logical line value
- the metadata invariant now distinguishes scheduled and delivered grant
  phases, but it intentionally tracks phase/shape facts rather than a full
  post-grant state correspondence

The remaining Stage 1 work is to strengthen that phase metadata if needed.
After that, the next major step is the explicit message-level model from the
implementation plan.

## Current message-level scope

The current `Messages/` files now implement the next Stage 2 checkpoint:

- explicit A/B/C/D/E endpoint slots are present in local state
- shared state tracks home memory, a permission directory, the current manager
  transaction, and pending sink / ack metadata
- the modeled action slice is still intentionally narrow:
  `sendAcquireBlock`, `sendAcquirePerm`, `recvAcquireAtManager`,
  `recvProbeAtMaster`, `recvProbeAckAtManager`, `sendGrantToRequester`,
  `recvGrantAtMaster`, `recvGrantAckAtManager`, `sendRelease`,
  `sendReleaseData`, `recvReleaseAtManager`, and `recvReleaseAckAtMaster`
- `recvAcquireAtManager` explicitly schedules B-channel probes into target
  endpoints rather than hiding them in atomic metadata
- `recvProbeAtMaster` consumes a B probe, downgrades the local line, and emits
  a C probe acknowledgment
- `recvProbeAckAtManager` consumes one C acknowledgment, updates the manager's
  directory entry for that responder, and can move the current transaction to
  `grantReady`
- `sendGrantToRequester` emits the D-channel `Grant`/`GrantData`
- `recvGrantAtMaster` consumes that D message, installs the granted line, and
  emits E-channel `GrantAck`
- `recvGrantAckAtManager` retires the current transaction and clears the live
  grant-ack obligation
- `sendRelease` / `sendReleaseData` now explicitly emit C-channel release
  traffic and update the releaser's local line to the reported/pruned result
- `recvReleaseAtManager` explicitly consumes that C message, updates memory
  and directory state, and emits a D-channel `ReleaseAck`
- `recvReleaseAckAtMaster` consumes the D ack and clears the releaser's local
  `releaseInFlight` flag
- the proof is already split by concern into model, frame lemmas, core
  invariants, serialization invariants, init proof, acquire-step preservation,
  probe-step preservation, grant-step preservation, release-step preservation,
  and the exported theorem

The proved theorem at this checkpoint is:

- `Messages/Theorem.lean`: `messages_acquire_inv_invariant`

That theorem now covers the acquire/probe/grant slice together with the
explicit release path. The established invariant covers:

- local line well-formedness
- directory/local permission agreement, with explicit allowance for a
  directory entry to lag behind a just-downgraded local line only while a
  C-channel probe acknowledgment is still pending at that node
- well-scoped pending `GrantAck` / `ReleaseAck` metadata
- factored serialization consequences for pending grant/release acknowledgments
  and release/grant channel obligations
- well-formed manager transaction metadata for the active acquire/probe wave
- well-formed D/E grant state for a live `grantPendingAck` transaction
- A-channel well-formedness for in-flight acquires
- B-channel well-formedness for the scheduled probe wave
- C-channel well-formedness for returned probe acknowledgments
- D-channel well-formedness for live grants
- E-channel well-formedness for returned `GrantAck`s

The next Stage 2 step is message-to-atomic refinement in
[Refinement.lean](/Users/rupak/Code/tla/leslie/Leslie/Examples/CacheCoherence/TileLink/Messages/Refinement.lean).

At the current Stage 2e checkpoint, that refinement work has started but is
not finished yet:

- manager-side `AcquireBlock` acceptance has been tightened to the Stage 1
  atomic scope: requester starts from `N`, the no-dirty case only, and the
  requested result permission now matches the current sharing situation
- `sendRelease` / `sendReleaseData` now serialize queued C-channel releases so
  the single-line message model no longer admits overlapping release waves
- `Messages/Refinement.lean` now contains refinement-specific helper
  invariants (`noDirtyInv`, `txnDataInv`, `refinementInv`) and their initial
  lemmas
- the refinement map now uses a per-transaction snapshot of pre-wave local
  lines (`preLines`) so probe-side local mutations can be hidden until the
  atomic linearization point
- the refinement map also synthesizes the abstract post-release
  `pendingReleaseAck` view as soon as a clean release is queued, matching the
  atomic release timing more closely
- the atomic release model now accepts `NtoN`, so the prune/report parameter
  space is aligned more closely with TL-C and with the message model

What remains is the actual forward-simulation theorem from the explicit
message model back to the atomic model.
