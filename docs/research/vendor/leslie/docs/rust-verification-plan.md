# Implementation Plan: Verifying Rust Round-Based Protocols

**Status: UNDER REVIEW**

This document breaks the design in `rust-verification.md` into
concrete implementation steps with dependencies, deliverables, and
estimated scope.

## Prerequisites

- Leslie project with round-based framework and proved examples — **done**
- Rust `Communication`/`InboxExt` API — **done** (provided by user)
- [TraceForge](https://github.com/awslabs/TraceForge) — systematic
  exploration of message interleavings with DPOR + monitors
- [DesCartes](https://github.com/rupakm/DesCartes/) — deterministic
  discrete-event simulation of tokio/tonic-based Rust services

## Overview: The Verification Spectrum

Not every property requires the same level of assurance. We organize
verification into a spectrum from lightweight (fast, low effort) to
heavyweight (strong guarantees, high effort). Each level catches
different classes of bugs and can discharge different proof obligations.

| Level | Tool | What it checks | Trust basis |
|-------|------|---------------|-------------|
| 0 | Typestate (Rust types) | Phase discipline | Compiler |
| 1 | clippy / custom lints | Structural patterns | Static analysis |
| 2 | Custom dataflow analysis | Communication closure, determinism | MIR analysis |
| 3a | TraceForge | Safety on reachable states (abstract model) | DPOR completeness |
| 3b | DesCartes | Safety + liveness (real async code, scheduling) | Deterministic simulation |
| 4 | Verus / SMT | Functional VCs (send_corr, update_corr) | SMT solver |
| 5 | Leslie (Lean) | Inductive invariants, refinement | Lean kernel |

**Important distinction**: Levels 3a/3b check properties on
**reachable** states (forward exploration from init). They do NOT
check inductiveness — that requires reasoning about ALL states
satisfying the invariant, including unreachable ones. Inductive
invariant proofs remain at Level 5 (Lean). See the discussion
in "What Exploration Can and Cannot Do" below.

## What Exploration Can and Cannot Do

### Forward reachability vs. inductiveness

Tools like TraceForge and DesCartes are forward explorers: they
start from initial states and systematically explore reachable
states. This is fundamentally different from checking inductiveness.

| Check | What it proves | What it requires |
|-------|---------------|-----------------|
| Forward reachability | Property holds on all **reachable** states | Explore from init |
| Inductiveness | `inv(s) ∧ next(s,s') → inv(s')` for **all** s | Enumerate or reason about all inv-satisfying states |

Inductiveness checking requires examining states that may be
**unreachable** — that is precisely why auxiliary invariant
conjuncts are needed. For example, in LastVotingPhased, the
cross-ballot invariant (G) is needed because there exist states
satisfying agreement (A) that are unreachable but whose successors
violate (A). Forward exploration from init would never visit those
states and thus would never discover the need for (G).

### What forward exploration IS useful for

1. **Validating safety properties for fixed instances**: For a
   concrete instance (fixed N, bounded rounds, concrete value
   domain), forward reachability is a complete proof that the
   property holds on all reachable states of that instance.
   No inductive invariant is needed — the exploration IS the proof.

2. **Catching overly-strong invariants**: If a candidate invariant
   excludes reachable states, forward exploration will find a
   reachable state violating the invariant. This catches invariants
   that are too strong (they aren't actually invariants).

3. **Sanity-checking correspondence**: Before attempting a Lean
   proof that Rust code matches the Leslie model, we can run both
   and compare outputs on all reachable states for small instances.

4. **Regression testing**: After code changes, quickly verify that
   safety still holds on concrete instances.

5. **Counterexample generation**: When a property fails, the
   exploration tool produces a concrete execution trace — useful
   for debugging both code and proof attempts.

### What forward exploration CANNOT do

1. **Check inductiveness**: Cannot find non-inductive states that
   are unreachable. The invariant may hold on all reachable states
   but fail the induction step on some unreachable inv-satisfying
   state.

2. **Discover auxiliary conjuncts**: The auxiliary predicates
   (like cross-ballot invariants) needed to make an invariant
   inductive typically constrain unreachable states. Forward
   exploration doesn't visit these states and thus can't discover
   the need for these conjuncts.

3. **Prove properties for all N**: Even with cutoff results,
   exploration proves the property for specific instances, not
   symbolically for all N.

### How to extend exploration toward inductiveness testing

There are several approaches to get closer to inductiveness checking
without full symbolic reasoning:

**Approach A: Random state sampling ("QuickChick-style")**

Generate random states satisfying the candidate invariant, then
check one transition step:

```
repeat:
  s ← random state satisfying inv
  for each possible next step (s, s'):
    check inv(s')
```

This is what tools like Ivy and Apalache's "inductive invariant
mode" do. It is **not complete** but catches many inductiveness
failures quickly. The challenge is generating valid random states
satisfying a complex invariant — this requires either a constraint
solver or a custom state generator.

For round-based protocols, a natural generator is: run the protocol
forward for some random number of rounds with random HO sets, then
use the resulting state as the starting point. This biases toward
reachable states but can be combined with random perturbation to
explore near-reachable states.

**Approach B: Bounded backward exploration**

From states where `inv(s')` fails, work backward: what predecessor
states `s` could lead to `s'`? If any of those predecessors satisfy
`inv(s)`, we have a counterexample to inductiveness (and the
predecessor reveals what conjunct is missing).

**Approach C: Symbolic model checking (IC3/PDR)**

Use a symbolic engine (e.g., via SMT) to find `s` such that
`inv(s) ∧ next(s,s') ∧ ¬inv(s')`. This is what property-directed
reachability (IC3/PDR) does. It's complete for finite-state systems
and can sometimes handle parameterized ones. This would be a
separate tool, not TraceForge/DesCartes.

**Approach D: Lean-side simulation**

Leslie's `Simulate.lean` can evaluate protocol transitions
symbolically. A hybrid approach: use Lean to generate the set of
`inv`-satisfying states (or sample from it), then check transitions.
This keeps the invariant specification in Lean where it belongs.

### Recommended approach for this project

- Use TraceForge/DesCartes for **forward reachability** (items 1-5
  above) — validating properties, correspondence checking,
  regression testing.
- Use **random state sampling** (Approach A) as a lightweight
  inductiveness pre-check, implemented either in the Rust explorer
  or in Lean.
- Use **Lean proofs** (Level 5) for the actual inductiveness
  argument. The exploration tools provide confidence and catch
  mistakes early, but do not replace the proof.

## Phase 1: Typestate API for Phase Discipline

**Goal**: Make phase violations a compile error. Pure Rust type system.

### Step 1.1: Define the typestate round API

Create `rust-lib/src/typestate.rs`:

```rust
pub struct Ready;
pub struct Sent;
pub struct Received;

pub struct RoundCtx<P, R, T, Phase> { ... }
```

Transitions:
- `RoundCtx<..., Ready>` → `.send(msg)` → `RoundCtx<..., Sent>`
- `RoundCtx<..., Sent>` → `.inbox(pred, done)` → `(RoundCtx<..., Received>, BTreeMap<P, M>)`
- `RoundCtx<..., Received>` → `.tick()` → `RoundCtx<..., Ready>`

**Deliverable**: A Rust crate `leslie-rounds` wrapping the
`Communication`/`InboxExt` API with typestate enforcement.

**Dependency**: None.

### Step 1.2: Multi-phase typestate variant

For protocols with k phases per round:

```rust
pub struct PhaseCtx<P, R, T, const PHASE: usize> { ... }
```

Transitions advance `PHASE` from 0 to k-1, then tick to next round.

**Deliverable**: Extension of `leslie-rounds` for multi-phase protocols.

**Dependency**: Step 1.1.

### Step 1.3: Port a protocol to typestate API

Implement a representative protocol using `RoundCtx`, verifying
that the typestate prevents phase violations at compile time.

**Deliverable**: `rust-examples/<protocol>/src/main.rs`.

**Dependency**: Step 1.1.

## Phase 2: RoundProtocol Trait

**Goal**: Define the `RoundProtocol` trait that serves as the shared
interface between protocol implementations, state-space explorers
(TraceForge/DesCartes), and the ghost encoding for formal verification.

### Step 2.1: Define the RoundProtocol trait

Create `rust-lib/src/protocol.rs`:

```rust
pub trait RoundProtocol {
    type State: Clone + Debug;
    type Msg: Clone + Debug + Message;
    type Oracle: Clone;

    /// Initial states (may be nondeterministic via oracle).
    fn init(id: PeerId, n: usize, oracle: Self::Oracle) -> Self::State;

    /// The message to send, given current state.
    fn send(id: PeerId, state: &Self::State) -> Self::Msg;

    /// The new state, given current state and inbox.
    fn update(
        id: PeerId,
        state: &Self::State,
        inbox: &BTreeMap<PeerId, Self::Msg>,
    ) -> Self::State;

    /// All possible oracle values (for nondeterministic protocols).
    fn oracle_values(n: usize) -> Vec<Self::Oracle>;
}
```

Note: the safety invariant is NOT part of the trait — it is
specified separately and may reference global state, ghost state,
or properties that don't map to a simple `&[State] -> bool`.

**Deliverable**: Trait definition in `leslie-rounds`.

**Dependency**: None (parallel with Phase 1).

### Step 2.2: Multi-phase variant

```rust
pub trait PhaseRoundProtocol {
    type State: Clone + Debug;
    type Msg: Clone + Debug + Message;
    type Oracle: Clone;
    const NUM_PHASES: usize;

    fn init(id: PeerId, n: usize, oracle: Self::Oracle) -> Self::State;
    fn send(phase: usize, id: PeerId, state: &Self::State) -> Self::Msg;
    fn update(
        phase: usize,
        id: PeerId,
        state: &Self::State,
        inbox: &BTreeMap<PeerId, Self::Msg>,
    ) -> Self::State;
    fn oracle_values(n: usize) -> Vec<Self::Oracle>;
}
```

**Deliverable**: Multi-phase trait in `leslie-rounds`.

**Dependency**: Step 2.1.

### Step 2.3: Implement protocols

Implement `RoundProtocol` / `PhaseRoundProtocol` for representative
protocols covering the design space:
- Single-phase (e.g., OneThirdRule, FloodMin)
- Multi-phase (e.g., LastVoting/Paxos, BenOr)
- With nondeterminism (e.g., BenOr: oracle = coin flip)

**Deliverable**: `rust-examples/` per protocol.

**Dependency**: Steps 2.1, 2.2.

## Phase 3: Ghost Encoding and Correspondence

**Goal**: Define the mapping between Rust protocol state and Leslie
(Lean) state. State the correspondence conditions. Prove the
transfer theorem in Lean.

### Step 3.1: Define ghost encoding functions

For each protocol, define pure functions mapping Rust types to
their Leslie counterparts:

```rust
mod ghost {
    pub fn encode(s: &RustState) -> LeslieState { ... }
    pub fn encode_inbox(
        inbox: &BTreeMap<PeerId, RustMsg>
    ) -> LeslieInbox { ... }
}
```

These are "specification-only" functions — testable and auditable,
not ghost-erased. They define the abstraction function from the
Rust implementation to the Leslie model.

**Deliverable**: Ghost modules per protocol.

**Dependency**: Step 2.1.

### Step 3.2: Leslie correspondence theorem (Lean side)

```lean
structure RustCorrespondence (RS LS M : Type) where
  encode : RS → LS
  encode_msg : RustMsg → M
  encode_inbox : (PeerId → Option RustMsg) → (PeerId → Option M)

structure CorrespondenceProof (rc : RustCorrespondence RS LS M)
    (alg : RoundAlg P LS M) where
  init_corr : ∀ rs, rust_init rs → alg.init (rc.encode rs)
  send_corr : ∀ rs, rc.encode_msg (rust_send rs) = alg.send (rc.encode rs)
  update_corr : ∀ rs inbox,
    rc.encode (rust_update rs inbox) =
    alg.update (rc.encode rs) (rc.encode_inbox inbox)

theorem rust_inherits_safety
    (rc : RustCorrespondence RS LS M)
    (proof : CorrespondenceProof rc alg)
    (leslie_safety : pred_implies spec.safety [tlafml| □ ⌜inv⌝])
    : -- The Rust system satisfies inv ∘ encode
    ...
```

The correspondence conditions (`send_corr`, `update_corr`) are
verification obligations. How they are discharged depends on the
protocol — see "Discharging VCs" section below.

**Deliverable**: `Leslie/RustCorrespondence.lean`.

**Dependency**: None (parallel with Phases 1-2).

## Phase 4: Static Analysis (Levels 1-2)

**Goal**: Lightweight static checks that catch structural bugs
without heavyweight verification tooling.

### Step 4.1: Custom clippy-style lints (Level 1)

Structural patterns checkable by syntactic/type analysis:

- **Purity of send/update**: `RoundProtocol` methods must be
  pure functions of their arguments. Lint flags access to global
  mutable state (`static mut`, `lazy_static`, `thread_local`,
  `Arc<Mutex>`, `Cell`, `RefCell`) within `send()` and `update()`.

- **Message type serialization roundtrip**: `Msg` types must
  derive `Serialize + Deserialize` and pass a proptest roundtrip.

- **No panics in protocol core**: `send()` and `update()` should
  be total. Lint flags `unwrap()`, `expect()`, array indexing,
  division in protocol methods.

**Deliverable**: `leslie-rounds-lint` crate or clippy config.

**Dependency**: Step 2.1.

### Step 4.2: Communication closure dataflow check (Level 2)

The critical property: `round_pred` must only accept same-round
(same-ballot, same-phase) messages. This is an information-flow
property — the predicate's return value must depend only on the
round/phase fields of its arguments.

**Approach**: MIR-level taint analysis.

1. Tag the round/phase fields of the message metadata as "tainted".
2. Propagate taint through the `round_pred` function body.
3. Check: the return value depends only on tainted fields
   (round/phase comparison), not on message content.

**Alternative**: For protocols using the typestate API, the type
system already enforces this. The dataflow check is for code that
bypasses the typestate layer.

**Deliverable**: MIR analysis pass in `leslie-rounds-check`.

**Dependency**: Step 1.1.

### Step 4.3: Send determinism check (Level 2)

`RoundProtocol::send()` must be deterministic. Check via MIR
analysis (no RNG, clock, I/O, mutable globals) or via proptest
(call twice with same inputs, assert equal outputs).

**Deliverable**: Part of `leslie-rounds-check`.

**Dependency**: Step 2.1.

## Phase 5A: TraceForge Integration (Level 3a)

**Goal**: Use TraceForge for systematic exploration of the abstract
protocol model. TraceForge checks properties on **reachable states**
for concrete instances (fixed N, fixed rounds, concrete values).

### What TraceForge provides

- **DPOR with reads-from equivalence**: Reduces the interleaving
  space while maintaining completeness.
- **Monitor/Observer infrastructure**: State machine monitors that
  observe messages and check properties.
- **Counterexample traces**: Replayable, debuggable.
- **Coverage goals**: `cover!` macro for reachability checks.
- **Nondet**: `<bool>::nondet()` for nondeterministic choices
  (message loss, oracle values).

### Step 5A.1: RoundProtocol → TraceForge adapter

Bridge `RoundProtocol` to TraceForge's thread/message-passing:

```rust
fn traceforge_explore<P: RoundProtocol>(
    n: usize,
    rounds: usize,
    invariant: impl Fn(&GlobalState<P>) -> bool,
) {
    traceforge::verify(Config::builder().build(), || {
        let handles: Vec<_> = (0..n).map(|i| {
            thread::spawn(move || {
                let mut state = P::init(i, n, oracle);
                for _round in 0..rounds {
                    let msg = P::send(i, &state);
                    for j in 0..n {
                        // Message loss is nondeterministic
                        if <bool>::nondet() {
                            send_msg(peers[j], (i, msg.clone()));
                        }
                    }
                    let inbox = collect_round_messages(i, n);
                    state = P::update(i, &state, &inbox);
                }
                publish(state);
            })
        }).collect();
    });
}
```

**Deliverable**: `leslie-rounds/src/traceforge_adapter.rs`.

**Dependency**: Steps 2.1, TraceForge.

### Step 5A.2: Safety monitors

Implement safety property checks as TraceForge monitors:

```rust
impl<P: RoundProtocol> Monitor for SafetyMonitor<P> {
    fn on_stop(&mut self, end: &ExecutionEnd) -> MonitorResult {
        let states = /* collect published states */;
        if !check_safety(&states) {
            Err("Safety violation".into())
        } else { Ok(()) }
    }
}
```

Also: per-step monitors that observe messages and check properties
after each round (not just at termination). This catches transient
violations.

**Deliverable**: Monitor implementations.

**Dependency**: Step 5A.1.

### Step 5A.3: Correspondence testing

Use TraceForge to validate the ghost encoding correspondence
conditions (Phase 3) on reachable states:

For every reachable `(state, inbox)` pair encountered during
exploration, check:
- `encode(rust_send(s)) == leslie_send(encode(s))`
- `encode(rust_update(s, inbox)) == leslie_update(encode(s), encode_inbox(inbox))`

This is **not** a proof of the correspondence VCs — it only
checks them on reachable states for concrete instances. But it
catches all bugs that manifest in the explored instance.

**Deliverable**: Correspondence-checking mode.

**Dependency**: Steps 3.1, 5A.1.

### Step 5A.4: Inductiveness pre-checking (Approach A)

Extend the adapter to support **random-state inductiveness testing**:

```rust
fn test_inductiveness<P: RoundProtocol>(
    n: usize,
    invariant: impl Fn(&GlobalState<P>) -> bool,
    num_samples: usize,
) {
    for _ in 0..num_samples {
        // Generate a candidate state:
        // Option 1: Run forward from init with random HO sets,
        //           stop at a random round, perturb the state.
        // Option 2: Use a constraint-based generator.
        // Option 3: Enumerate (for small finite domains).
        let s = generate_inv_satisfying_state(n, &invariant);
        // Check one step from s with all possible HO collections
        for ho in all_ho_collections(n) {
            let s_prime = step(s, ho);
            if !invariant(&s_prime) {
                panic!("Inductiveness failure: {s} --{ho}--> {s_prime}");
            }
        }
    }
}
```

The hard part is `generate_inv_satisfying_state`. For protocols
with finite state (bounded values, bounded ballots), we can
enumerate. For richer domains, we use:
- Forward runs stopped at random points (biases toward reachable
  states, but with perturbation explores near-reachable).
- Domain-specific generators (e.g., for Paxos: generate any
  combination of `lastVote`, `proposal`, `decided` fields
  satisfying the candidate invariant conjuncts).

**Completeness**: This is **not complete** — it can miss
counterexamples. But it catches many inductiveness failures
quickly and is far cheaper than a Lean proof attempt. Think of
it as a fast pre-check: "is this invariant even plausibly
inductive?" before investing in a Lean proof.

**Deliverable**: Inductiveness testing mode.

**Dependency**: Step 5A.1.

## Phase 5B: DesCartes Integration (Level 3b)

**Goal**: Use DesCartes for testing the **real async Rust
implementation** (tokio/tonic-based), not just the abstract
`RoundProtocol` model.

### Why DesCartes (complementary to TraceForge)

| | TraceForge | DesCartes |
|---|---|---|
| **Model** | Abstract (thread + message passing) | Real async Rust (tokio/tonic) |
| **Exploration** | DPOR (exhaustive for interleavings) | Schedule search + rare-event biasing |
| **Nondeterminism** | Message ordering + `nondet()` | DES frontier + tokio ready-task + RNG |
| **Best for** | Protocol logic, correspondence testing | Implementation bugs, async races, timing |
| **Corresponds to** | Leslie `RoundAlg` model | Actual deployed code |

**Use TraceForge** to check the abstract protocol model.
**Use DesCartes** to check the real async implementation.
Together they cover the full abstraction stack.

### Step 5B.1: RoundProtocol → DesCartes adapter

Bridge `RoundProtocol` to DesCartes' simulated tokio runtime:

```rust
async fn descartes_explore<P: RoundProtocol>(
    sim: &mut Simulation,
    n: usize,
    rounds: usize,
) {
    descartes_tokio::runtime::install(sim);
    for i in 0..n {
        descartes_tokio::spawn(async move {
            let mut state = P::init(i, n, oracle);
            for _round in 0..rounds {
                let msg = P::send(i, &state);
                broadcast(&comm, i, msg).await;
                let inbox = collect_inbox(&comm, i).await;
                state = P::update(i, &state, &inbox);
            }
        });
    }
}
```

**Deliverable**: `leslie-rounds/src/descartes_adapter.rs`.

**Dependency**: Steps 2.1, DesCartes.

### Step 5B.2: Schedule exploration for bug finding

Use `des-explore`'s policy search to find adversarial schedules
that trigger safety violations in real async code:

- **Frontier ordering**: Different orderings of same-time DES events
- **Tokio ready-task ordering**: Which async task runs next
- **Decision scripts**: Replay specific interleavings
- **Rare-event biasing**: Focus exploration on near-deadline,
  high-contention scenarios

This finds bugs that TraceForge misses — async runtime scheduling
issues, timer races, incomplete inbox collection due to tokio
task ordering.

**Deliverable**: Schedule exploration harness.

**Dependency**: Step 5B.1.

### Step 5B.3: Production code testing

For protocols with real tokio/tonic implementations (not just
`RoundProtocol` implementations), DesCartes tests the actual code
by swapping in simulated tokio:

```rust
// The real production code, unchanged:
async fn proposer(comm: &Communication, state: &mut State) {
    let responses = comm.inbox(same_ballot, majority_done).await?;
    let proposal = pick_highest(&responses);
    comm.send(Accept { ballot: state.ballot, value: proposal }).await?;
}

// DesCartes test: run the real code under simulated transport
#[test]
fn test_safety() {
    let mut sim = Simulation::new(SimulationConfig::default());
    descartes_tokio::runtime::install(&mut sim);
    // Spawn the real code with simulated communication
}
```

**Deliverable**: Integration test harness.

**Dependency**: Steps 1.1, 5B.1.

## Phase 6: Verus / SMT Verification (Level 4)

**Goal**: For VCs that cannot be adequately checked by testing
(unbounded domains, parametric N, no cutoff), use Verus for
SMT-based verification.

### When to use each level for discharging VCs

| Situation | Approach |
|-----------|----------|
| Finite state, small instance | TraceForge exhaustive (complete for that instance) |
| Finite state + cutoff theorem | TraceForge up to cutoff (complete) |
| Infinite state, bounded values | Random testing + Lean proof |
| Parametric N, unbounded domain | Verus (SMT) or Lean proof |
| Structural property (purity, closure) | Dataflow analysis (Level 2) |
| Timing/scheduling property | DesCartes (Level 3b) |

### Step 6.1: Annotate critical VCs (when needed)

```rust
#[ensures(encode(&result) == leslie_update(encode(state), encode_inbox(inbox)))]
fn update(state: &State, inbox: &BTreeMap<PeerId, Msg>) -> State { ... }
```

**Dependency**: Steps 3.1, Verus toolchain.

## Phase 7: End-to-End Pipeline

**Goal**: Complete pipeline from Leslie proof to checked Rust code.

### Step 7.1: Assemble the pipeline for a protocol

1. **Leslie proof**: Inductive invariant proved in Lean (Level 5)
2. **Rust `RoundProtocol` impl**: Protocol logic in Rust
3. **Ghost encoding**: `encode`, `encode_inbox` (Phase 3.1)
4. **Typestate wrapper**: Phase discipline at compile time (Phase 1)
5. **Static checks**: Purity, closure, determinism (Phase 4)
6. **TraceForge**: Forward reachability check on concrete instances;
   correspondence VC validation on reachable states (Phase 5A)
7. **DesCartes**: Real async code under adversarial scheduling (Phase 5B)
8. **Leslie metatheorem**: `rust_inherits_safety` (Phase 3.2)
9. **VC discharge**: By appropriate level per VC

**Trust chain**:
- Leslie proves safety of the abstract model (all N, all executions).
- Correspondence VCs assert Rust code matches the abstract model.
- VCs are discharged by: Verus (SMT, strongest), or testing (bounded
  but combined with cutoff can be complete), or dataflow (structural).
- Typestate prevents phase discipline bugs at compile time.
- DesCartes checks that the real async code matches the synchronous
  `RoundProtocol` under adversarial scheduling.

Each layer in the trust chain may have a different assurance level.
The overall guarantee is as strong as the weakest link.

### Step 7.2: Proof feedback loop

The exploration tools provide feedback to the proof process,
even though they cannot check inductiveness directly:

```
 ┌──────────────────┐
 │  Candidate inv    │
 │  (conjuncts A-X)  │
 └────────┬─────────┘
          │
          ▼
 ┌──────────────────┐     reachable cex      ┌──────────────┐
 │  TraceForge       │ ─────────────────────▶ │  Proof Agent  │
 │  forward reach    │   "inv too strong"     │  (human/AI)   │
 └──────────────────┘                         └──────┬───────┘
          │                                          │
   no reachable cex                                  │
          │                                          │
          ▼                                          │
 ┌──────────────────┐     random cex                 │
 │  Inductiveness    │ ─────────────────────▶        │
 │  pre-check        │   "step fails on              │
 │  (Approach A)     │    sampled state"              │
 └──────────────────┘                                │
          │                                          │
   no sampled cex                                    │
          │                                          │
          ▼                               strengthened inv
 ┌──────────────────┐                                │
 │  Lean proof       │ ◄────────────────────────────┘
 │  attempt          │
 └──────────────────┘
          │
   proof succeeds / gets stuck
   (stuck case → new conjunct → loop)
```

**Phase 1**: TraceForge checks that the candidate invariant
actually holds on reachable states. If it fails here, the
invariant is too strong or just wrong.

**Phase 2**: Random state sampling tests inductiveness on
sampled `inv`-satisfying states. This catches many inductiveness
failures cheaply (missing conjuncts that constrain unreachable
states). Not complete, but fast.

**Phase 3**: Lean proof attempt. If the proof gets stuck on a
specific case (e.g., "Phase 2→3, conjunct G1"), the stuck case
itself may suggest a new auxiliary conjunct. Add it and loop.

The first two phases are cheap pre-checks that prevent wasting
time on Lean proofs that are doomed to fail. They are most
valuable when the state space is complex (many conjuncts) and
the proof agent is iterating on invariant candidates.

### Step 7.3: Write up the case study

Document the complete pipeline for a representative protocol:
what was proved where, what was checked how, what the trust
assumptions are, where each level of the verification spectrum
was used and why.

**Deliverable**: `docs/case-study.md`.

**Dependency**: Steps 7.1, 7.2.

## Dependency Graph

```
Phase 1 (Typestate)     Phase 2 (Protocol)     Phase 3 (Correspondence)
  1.1 ─── 1.2            2.1 ─── 2.2             3.1
   │                      │       │                │
  1.3                    2.3      │               3.2 (Lean)
                          │       │
Phase 4 (Static)          │       │
  4.1 (lints)             │       │
  4.2 (dataflow)          │       │
  4.3 (determinism)       │       │
                          │       │
Phase 5A (TraceForge)     │       │      Phase 5B (DesCartes)
  5A.1 (adapter) ◄────────┘       │       5B.1 (adapter)
   │                               │        │
  5A.2 (monitors)                  │       5B.2 (explore)
   │                               │        │
  5A.3 (correspondence)            │       5B.3 (prod test)
   │                               │
  5A.4 (inductiveness precheck)    │
   │                               │
   └───────────────────────────────┘
                   │
             Phase 6 (Verus, if needed)
               6.1
                   │
             Phase 7 (E2E)
               7.1
                │
               7.2 (proof loop)
                │
               7.3 (case study)
```

## Parallelism

- **Phase 1** (typestate), **Phase 2** (protocol trait),
  **Phase 3.2** (Leslie metatheorem): no dependencies.

- **Phase 4** (static analysis) and **Phase 5A/5B** (exploration):
  independent, both consume Phase 2.

- **5A** (TraceForge) and **5B** (DesCartes): independent.

- Protocol implementations: independent of each other within
  each phase.

## Estimated Scope

| Phase | Steps | New code | Difficulty |
|-------|-------|----------|------------|
| 1. Typestate | 3 | ~300 lines Rust | Low |
| 2. Protocol trait | 3 | ~400 lines Rust | Low |
| 3. Correspondence | 2 | ~200 lines Lean + Rust | Medium |
| 4. Static analysis | 3 | ~300 lines Rust | Medium |
| 5A. TraceForge | 4 | ~600 lines Rust | Medium |
| 5B. DesCartes | 3 | ~400 lines Rust | Medium |
| 6. Verus (if needed) | 1 | ~200 lines annotations | High |
| 7. E2E | 3 | ~100 lines + docs | Low |
| **Total** | **22** | **~2500 lines** | |

## Open Questions

1. **Random state generation for inductiveness pre-check**:
   For protocols with rich state (multiple fields, Option types,
   ballot numbers), generating random states that satisfy a
   multi-conjunct invariant is non-trivial. Approaches:
   (a) constraint-based generation via SMT,
   (b) forward simulation + perturbation,
   (c) domain-specific generators (protocol-aware).
   Which approach scales best across protocols?

2. **TraceForge DPOR effectiveness for HO model**: TraceForge's
   DPOR is designed for message-passing interleavings. In the HO
   model, nondeterminism is in message *loss* (modeled as
   `<bool>::nondet()` per message). DPOR's reads-from equivalence
   should help (processes receiving the same set of messages are
   equivalent), but the reduction factor needs empirical evaluation.

3. **DesCartes ↔ RoundProtocol gap**: DesCartes tests real async
   code, but `RoundProtocol` is synchronous. The adapter must
   faithfully bridge: simulated async communication wrapping
   synchronous `send`/`update`. More importantly, for production
   code that doesn't conform to the `RoundProtocol` interface,
   DesCartes tests the code as-is — but how do we connect those
   test results back to the Leslie model?

4. **Symbolic inductiveness checking**: Could we build a
   symbolic checker (IC3/PDR-style) that works with the
   `RoundProtocol` trait? This would be more powerful than random
   sampling (Approach A) but less heavyweight than Verus. The
   protocol structure (round-based, message-passing) may admit
   specialized symbolic reasoning.

5. **Multi-phase communication closure**: For protocols with
   complex round structures (same ballot AND same phase), the
   dataflow check (Step 4.2) and the TraceForge adapter need to
   model the phase structure correctly. The typestate API (Phase 1)
   handles this structurally, but the static analysis needs to
   verify code that may bypass the typestate layer.

6. **Proof agent integration**: The feedback loop (Step 7.2)
   assumes a proof agent (human or AI) that can interpret
   counterexample traces and propose invariant strengthenings.
   For AI agents, the question is: given a counterexample state
   and the failing transition, can an LLM reliably identify the
   missing conjunct? This is a research question.
