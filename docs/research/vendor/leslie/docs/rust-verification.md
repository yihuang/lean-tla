# Verifying Rust Implementations of Round-Based Protocols

## Goal

Given a round-based protocol proved safe in Leslie and a Rust
implementation using the `Communication`/`InboxExt` API, establish
that the Rust code correctly implements the Leslie model — and
therefore inherits the Leslie safety proof.

## Architecture

```
┌─────────────────────────────────┐
│  Leslie (Lean 4)                │
│  ┌───────────┐  ┌────────────┐ │
│  │ RoundAlg  │  │ Safety     │ │
│  │ Protocol  │──│ Proof      │ │
│  │ Model     │  │ (□ Inv)    │ │
│  └───────────┘  └────────────┘ │
│        │                       │
│        │ Correspondence        │
│        │ Conditions            │
│        ▼                       │
│  ┌───────────────────────────┐ │
│  │ RustCorrespondence.lean   │ │
│  │ encode, send_corr,       │ │
│  │ update_corr, transfer_thm│ │
│  └───────────────────────────┘ │
└─────────────────────────────────┘
         │
         │ Generates verification
         │ conditions (VCs)
         ▼
┌─────────────────────────────────┐
│  Rust + Verus annotations       │
│  ┌───────────────────────────┐ │
│  │ Protocol implementation   │ │
│  │ with ghost state,         │ │
│  │ pre/post conditions,      │ │
│  │ typestate phases          │ │
│  └───────────────────────────┘ │
│  ┌───────────────────────────┐ │
│  │ Concurrent test harness   │ │
│  │ (N processes, simulated   │ │
│  │  transport, cutoff N≤K)   │ │
│  └───────────────────────────┘ │
└─────────────────────────────────┘
```

## Assumptions

1. **Transport correctness assumed.** The `Transport` trait implementation
   satisfies: messages are not fabricated, duplicated, or corrupted.
   Messages may be lost or reordered. This matches the HO model's
   nondeterministic delivery. We do not verify the transport.

2. **Verus annotations for sequential checks.** We annotate the Rust
   protocol code with Verus-style pre/post conditions and ghost state.
   The annotations express the correspondence between Rust state and
   Leslie state. We defer the question of how to discharge them (Verus
   solver, manual audit, or testing).

3. **Nondeterministic updates.** For randomized protocols (like Ben-Or),
   the update function is not deterministic — it depends on a coin flip
   or other nondeterministic choice. We handle this by enumerating all
   possible program paths through the update, and checking that EACH
   path corresponds to a valid Leslie transition.

## The Three Layers

### Layer 1: Structural well-formedness

The Rust code correctly uses the round/inbox API. This is about the
SHAPE of the code, not the algorithm.

#### 1a. Round monotonicity

**Property**: `tick()` always advances the round.

**Already enforced** by the `Round::tick()` implementation with
`debug_assert!(*self > old)`. For static verification, add a Verus
postcondition:

```rust
#[ensures(result > *old(self))]
fn tick(&mut self) { ... }
```

#### 1b. Communication closure

**Property**: The protocol only processes same-round messages.
Concretely, every `inbox` call uses a `round_pred` that accepts
only messages from the current round (for single-phase protocols)
or the current (ballot, phase) pair (for multi-phase).

**Check**: For each call to `inbox` or `recv_filtered`, verify that
the predicate implies `remote_round == local_round` (or the
appropriate multi-phase variant).

For single-phase protocols:
```rust
// The predicate MUST be equivalent to equality on the relevant round component
#[requires(forall |local: &R, remote: &R| round_pred(local, remote) ==> *local == *remote)]
fn inbox<RP, DONE>(&mut self, round_pred: RP, done: DONE) -> ...
```

For multi-phase protocols where the round is `(ballot, phase)`:
```rust
// Accept messages from the same ballot and phase
let inbox = self.inbox(
    |local, remote| local.ballot == remote.ballot && local.phase == remote.phase,
    done_pred,
)?;
```

**Verification approach**: A dataflow lint that inspects `round_pred`
arguments. For simple predicates (equality, field comparisons), this
is syntactic. For complex predicates, fall back to Verus annotation.

#### 1c. Phase discipline

**Property**: Each round follows the sequence: send → inbox → update → tick.
No sends after inbox, no inbox after update, no update before inbox.

**Enforcement**: Typestate pattern.

```rust
/// A round in progress. The type parameter tracks the current phase.
pub struct RoundCtx<P, R, T, Phase> {
    process: Process<P, R, T>,
    _phase: PhantomData<Phase>,
}

pub struct Ready;    // can send
pub struct Sent;     // can collect inbox
pub struct Received; // can update and tick

impl<P, R, T> RoundCtx<P, R, T, Ready> {
    /// Send the round's message. Transitions to Sent phase.
    pub fn send(self, msg: M) -> Result<RoundCtx<P, R, T, Sent>, Error> { ... }
}

impl<P, R, T> RoundCtx<P, R, T, Sent> {
    /// Collect the inbox. Transitions to Received phase.
    pub fn inbox(self, pred: RP, done: DONE)
        -> Result<(RoundCtx<P, R, T, Received>, BTreeMap<P, M>), Error> { ... }
}

impl<P, R, T> RoundCtx<P, R, T, Received> {
    /// Advance to the next round. Transitions back to Ready.
    pub fn tick(self) -> RoundCtx<P, R, T, Ready> { ... }
}
```

With this API, phase violations are compile errors. The protocol
code is forced to follow the send → inbox → tick sequence.

**For multi-phase rounds** (e.g., Paxos with 4 phases per ballot):
the typestate can encode the phase within the round:

```rust
pub struct Phase1a;
pub struct Phase1b;
pub struct Phase2a;
pub struct Phase2b;

impl RoundCtx<..., Phase1a> {
    fn send_prepare(self, ...) -> RoundCtx<..., Phase1b> { ... }
}
impl RoundCtx<..., Phase1b> {
    fn collect_promises(self, ...) -> (RoundCtx<..., Phase2a>, Inbox) { ... }
}
// etc.
```

#### 1d. Send depends only on local state

**Property**: The message sent in `send()` is determined by the
process's local state at the start of the round. It does not depend
on the inbox (which hasn't been collected yet, thanks to typestate)
or on external input.

**Check**: In the typestate API, `send` takes `&self` (read-only
access to state) and the outgoing message is computed from it.
The Verus annotation:

```rust
#[ensures(result == encode_send(self.state))]
fn send(&self) -> M { ... }
```

where `encode_send` is the ghost function corresponding to Leslie's
`RoundAlg.send`.

#### 1e. Update depends only on state + inbox

**Property**: The new local state depends only on the old state and
the inbox contents. No other inputs (except nondeterministic choices,
handled separately — see Section on nondeterminism below).

**Check**: The update function takes `(state, inbox)` and returns
`new_state`. The Verus annotation:

```rust
#[ensures(encode(result) == leslie_update(encode(old_state), encode_inbox(inbox)))]
fn update(state: &State, inbox: &BTreeMap<Peer, M>) -> State { ... }
```

### Layer 2: Algorithm correspondence

The Rust protocol's logic matches the Leslie model. This is the
refinement check.

#### The encoding function

Define a ghost function `encode : RustState → LeslieState` that
maps the Rust state representation to the Leslie state type.

```rust
#[ghost]
fn encode(s: &OTRState) -> leslie::LState {
    leslie::LState {
        val: s.val,
        decided: s.decided,
    }
}
```

For protocols with richer Rust state (e.g., message buffers, counters,
timers), `encode` projects out the Leslie-relevant fields.

#### The inbox encoding

The Leslie model represents received messages as `P → Option M`.
The Rust `BTreeMap<Peer, M>` naturally encodes as:

```rust
#[ghost]
fn encode_inbox(inbox: &BTreeMap<Peer, M>) -> impl Fn(Peer) -> Option<M> {
    move |p| inbox.get(&p).cloned()
}
```

This maps directly to Leslie's `delivered` function, with the BTreeMap
acting as the partial function from peers to messages.

#### Correspondence conditions

Three conditions to verify:

**(2a) Initial state correspondence:**
```
∀ rust_init, leslie_init(encode(rust_init))
```
The encoded initial Rust state satisfies the Leslie init predicate.

**(2b) Send correspondence:**
```
∀ state, encode_msg(rust_send(state)) == leslie_send(encode(state))
```
The Rust send function, when encoded, matches the Leslie send function.

**(2c) Update correspondence:**
```
∀ state inbox,
  encode(rust_update(state, inbox)) == leslie_update(encode(state), encode_inbox(inbox))
```
The Rust update function, when encoded, matches the Leslie update
function. For nondeterministic updates, this generalizes — see below.

#### Verus annotations

```rust
impl OTRState {
    #[ensures(encode(&result) == leslie::otr_alg_send(encode(self)))]
    fn make_message(&self) -> NatMsg {
        NatMsg(self.val)
    }

    #[ensures(encode(&result) == leslie::otr_alg_update(encode(self), encode_inbox(inbox)))]
    fn update(&self, inbox: &BTreeMap<PeerId, NatMsg>) -> OTRState {
        let received: Vec<Nat> = inbox.values().map(|m| m.0).collect();
        if let Some(v) = find_super_majority(&received, N) {
            OTRState { val: v, decided: Some(v) }
        } else {
            self.clone()
        }
    }
}
```

### Layer 3: Concurrent safety (derived)

**This layer requires no new verification** if Layers 1 and 2 pass.

The argument:
1. By Layer 1: each Rust process is a well-formed round-based process
   (correct API usage, communication closure, phase discipline).
2. By Layer 2: each process's behavior (send/update) matches the
   Leslie model via the encoding.
3. By the transport assumption: message delivery is nondeterministic
   but integral (no fabrication/corruption), matching the HO model.
4. By 1+2+3: the concurrent Rust execution, when encoded, is a valid
   execution of the Leslie `Spec` with some HO collection (determined
   by the transport's delivery choices).
5. By the Leslie safety proof: the safety property holds for all
   valid executions.
6. Therefore: the safety property holds for the Rust system.

**The compositional payoff**: concurrent reasoning is done once in
Leslie (abstract, clean). Rust verification is entirely sequential
(per-process, concrete). No concurrent Rust verification needed.

### Concurrent testing (optional, for confidence)

Even though Layer 3 is derived, a test harness provides confidence
that the correspondence is correct:

```rust
#[test]
fn test_otr_agreement() {
    // Instantiate K processes with a simulated transport
    let mut processes = create_processes(K);
    let mut transport = SimulatedTransport::new();

    // Run for R rounds with nondeterministic delivery
    for round in 0..R {
        // Each process sends
        for p in &mut processes {
            p.send(p.state.make_message());
        }
        // Nondeterministic delivery (enumerate subsets for model checking)
        transport.deliver_nondeterministic();
        // Each process collects inbox and updates
        for p in &mut processes {
            let inbox = p.collect_inbox();
            p.state = p.state.update(&inbox);
            p.tick();
        }
        // Check safety invariant
        assert!(check_agreement(&processes));
    }
}
```

By the **cutoff theorem**: testing at K ≤ 7 (for OneThirdRule with
binary values) covers all N. The test systematically explores all
HO collections (message delivery subsets) at each round.

## Handling Nondeterministic Updates

### The problem

For deterministic protocols (OneThirdRule), the update function is a
pure function of `(state, inbox)`. The correspondence condition is:
```
encode(rust_update(state, inbox)) == leslie_update(encode(state), encode_inbox(inbox))
```

For randomized protocols (Ben-Or), the update depends on a coin flip:
```rust
fn update(&self, inbox: &BTreeMap<PeerId, Msg>, coin: bool) -> State {
    if let Some(v) = find_witness_majority(inbox) {
        State { val: v, decided: Some(v) }
    } else {
        State { val: if coin { 1 } else { 0 }, decided: None }
    }
}
```

The coin flip creates multiple possible program paths through the
update function. The Leslie model handles this by existentially
quantifying over the oracle in the transition relation.

### The solution: path enumeration

For a Rust update function with K nondeterministic choices (each
binary: coin flips, random selections from a finite set), there are
at most 2^K possible program paths. The correspondence condition
becomes:

```
∀ state inbox,
  ∀ path ∈ paths(rust_update, state, inbox),
    ∃ oracle, encode(path.result) == leslie_update(encode(state), encode_inbox(inbox), oracle)
```

**"Every possible Rust execution path corresponds to some valid
Leslie transition."**

This is checkable by:

1. **Enumerating paths**: For each nondeterministic choice point in
   the Rust code (coin flip, random selection), enumerate the
   possible values. This is finite for bounded nondeterminism.

2. **Checking each path**: For each concrete path, verify the
   correspondence condition. Since the path is now deterministic,
   this reduces to the deterministic case.

3. **Bounding the nondeterminism**: The number of choice points per
   update must be bounded. For Ben-Or, there's exactly 1 coin flip
   per process per round (K=1, 2 paths). For protocols with
   nondeterministic leader election (BallotLeader), there's 1 bid
   choice per process (K=1, 2 paths).

### Verus annotations for nondeterministic updates

```rust
/// The update function takes an explicit `oracle` parameter for each
/// nondeterministic choice. The Verus annotation checks that every
/// oracle value produces a valid Leslie transition.
#[ensures(forall |oracle: bool|
    exists |leslie_oracle: LeslieOracle|
        encode(&result(oracle)) == leslie_update(
            encode(self),
            encode_inbox(inbox),
            leslie_oracle
        )
)]
fn update(&self, inbox: &BTreeMap<PeerId, Msg>) -> impl Fn(bool) -> State {
    move |coin| {
        if let Some(v) = find_witness_majority(inbox) {
            State { val: v, decided: Some(v) }
        } else {
            State { val: if coin { 1 } else { 0 }, decided: None }
        }
    }
}
```

In practice, the nondeterministic choice is made at runtime (e.g.,
by a random number generator). The verification obligation is that
ALL possible choices lead to valid Leslie transitions.

### Structured nondeterminism via the API

An alternative: make the nondeterminism explicit in the API.

```rust
pub trait RoundProtocol {
    type State;
    type Msg;
    type Oracle;  // NEW: the type of nondeterministic choices

    fn send(state: &Self::State) -> Self::Msg;
    fn update(state: &Self::State, inbox: &Inbox<Self::Msg>, oracle: Self::Oracle) -> Self::State;
    fn oracle_values() -> Vec<Self::Oracle>;  // enumerate all possible choices
}
```

For deterministic protocols: `type Oracle = ();` (one path).
For Ben-Or: `type Oracle = bool;` (two paths: coin flip).
For BallotLeader: `type Oracle = bool;` (two paths: bid or not).

The verification then explicitly enumerates `oracle_values()` and
checks each path.

## The Correspondence Theorem (in Leslie)

The Leslie side of the argument is a theorem in Lean:

```lean
/-- If the Rust implementation satisfies the correspondence conditions,
    then the concurrent Rust system satisfies the Leslie safety property.

    Hypotheses:
    - encode : RustState → LeslieState (the refinement mapping)
    - send_corr : Rust send corresponds to Leslie send
    - update_corr : Rust update corresponds to Leslie update (for all oracle values)
    - comm_closure : the inbox predicate enforces communication closure
    - transport_ok : the transport satisfies integrity (assumed)

    Conclusion:
    - The global Rust execution, when encoded, satisfies the Leslie safety property. -/
theorem rust_correctness
    (encode : RustState → LeslieState)
    (h_init : ∀ rs, rust_init rs → leslie_init (encode rs))
    (h_send : ∀ rs, encode_msg (rust_send rs) = leslie_send (encode rs))
    (h_update : ∀ rs inbox oracle,
      encode (rust_update rs inbox oracle) = leslie_update (encode rs) (encode_inbox inbox) oracle)
    (h_closure : ∀ p r, inbox_pred p r → r = p.round)
    : ... -- the Rust system satisfies the Leslie safety property
```

This theorem is proved ONCE in Leslie (generically), and instantiated
for each protocol. The protocol-specific work is defining `encode`
and verifying `h_send`/`h_update` (done in Verus on the Rust side).

## Case Study: OneThirdRule

### Leslie model (already proved)

```
Algorithm:  otr_alg (RoundAlg (Fin n) LState Nat)
Safety:     agreement (all decided processes agree)
Proof:      lock_inv is inductive → agreement (OneThirdRule.lean)
```

### Rust implementation

```rust
struct OTRState {
    val: u64,
    decided: Option<u64>,
}

impl RoundProtocol for OTR {
    type State = OTRState;
    type Msg = u64;            // broadcast current value
    type Oracle = ();          // deterministic

    fn send(state: &OTRState) -> u64 {
        state.val
    }

    fn update(state: &OTRState, inbox: &Inbox<u64>, _: ()) -> OTRState {
        let counts = count_values(inbox);
        if let Some(v) = find_super_majority(&counts, N) {
            OTRState { val: v, decided: Some(v) }
        } else {
            state.clone()
        }
    }

    fn oracle_values() -> Vec<()> { vec![()] }
}
```

### Verification conditions (Verus)

```rust
// Ghost encoding
#[ghost]
fn encode(s: &OTRState) -> leslie::LState {
    leslie::LState { val: s.val, decided: s.decided }
}

// VC1: Initial state correspondence
#[requires(s.decided == None)]
#[ensures(leslie::otr_alg_init(encode(&s)))]

// VC2: Send correspondence
#[ensures(result == encode(&s).val)]
fn send(s: &OTRState) -> u64 { s.val }

// VC3: Update correspondence
#[ensures(encode(&result) == leslie::otr_update(encode(s), encode_inbox(inbox)))]
fn update(s: &OTRState, inbox: &Inbox<u64>) -> OTRState { ... }
```

### What's checked where

| Check | What | How | Where |
|-------|------|-----|-------|
| Round monotonicity | tick advances | debug_assert + Verus | Rust (compile time) |
| Communication closure | inbox uses same-round pred | Verus / lint | Rust (compile time) |
| Phase discipline | send → inbox → tick | Typestate | Rust (compile time) |
| Send correspondence | rust_send = leslie_send | Verus VC | Rust (verify time) |
| Update correspondence | rust_update = leslie_update | Verus VC | Rust (verify time) |
| Safety proof | □ agreement | Machine-checked | Leslie (proved) |
| Concurrent safety | derived from above | Compositional | Automatic |

## Summary

The verification decomposes into:

1. **Leslie (done)**: Prove safety of the abstract protocol model.
   This is the hard mathematical work (lock invariants, pigeonhole,
   cutoff theorems). Done once per protocol.

2. **Rust structural checks (compile time)**: Typestate API enforces
   phase discipline. Communication closure checked by lint/Verus.
   These are protocol-independent — they come from the API design.

3. **Rust correspondence checks (verify time)**: Verus annotations
   verify that `encode ∘ rust_fn = leslie_fn ∘ encode` for send and
   update. For nondeterministic updates, enumerate oracle values and
   check each path. These are protocol-specific but mechanical.

4. **Concurrent safety (free)**: Follows from 1+2+3 by the
   compositional argument. No concurrent Rust verification needed.

The transport is assumed correct (Assumption 1). The Verus annotations
are the verification obligations (Assumption 2 — discharge later).
Nondeterminism is handled by path enumeration (Decision 3).

## Files

- `docs/rust-verification.md` — this document
- `Leslie/RustCorrespondence.lean` (future) — the generic correspondence theorem
- `rust-examples/otr/` (future) — OneThirdRule Rust implementation with Verus annotations
- `rust-examples/benor/` (future) — Ben-Or with nondeterministic oracle
