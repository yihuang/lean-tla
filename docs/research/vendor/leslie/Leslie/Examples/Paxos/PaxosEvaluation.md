# Single-Decree Paxos: Two Models and Their Refinement

## Overview

We present a mechanized development in Lean 4 of single-decree Paxos at
two levels of abstraction, together with a formal forward simulation
connecting them.  The **atomic model** (`Paxos.lean`) treats each
protocol phase as a single synchronous step; the **message-passing
model** (`MessagePaxos.lean`) decomposes phases into send/receive pairs
with an explicit asynchronous network.  Both models independently refine
a common Consensus specification, and a forward simulation
(`PaxosRefinement.lean`) bridges the two directly.

All proofs are machine-checked and sorry-free.  The development totals
4584 lines of Lean 4 across four files.

| File | Lines | Theorems | Sorry |
|------|------:|:--------:|:-----:|
| `Paxos.lean` | 727 | agreement, consensus refinement | 0 |
| `MessagePaxos.lean` | 2244 | cross-ballot agreement, invariant | 0 |
| `MsgPaxosConsensus.lean` | 306 | consensus refinement | 0 |
| `PaxosRefinement.lean` | 1307 | forward simulation | 0 |
| **Total** | **4584** | | **0** |

---

## 1  The Atomic Model

### 1.1  State and Actions

The atomic model is parameterized by `n` acceptors, `m` proposers, and
an injective ballot assignment `ballot : Fin m -> Nat`.

```
PaxosState (n m : Nat) :=
  prom   : Fin n -> Nat                        -- acceptor promise
  acc    : Fin n -> Option (Nat * Value)        -- acceptor accepted value
  got1b  : Fin m -> Fin n -> Bool               -- phase 1b received?
  rep    : Fin m -> Fin n -> Option (Nat * Value) -- phase 1b reply
  prop   : Fin m -> Option Value                -- proposer's chosen value
  did2b  : Fin m -> Fin n -> Bool               -- phase 2b sent?
```

Three actions correspond to the three phases of single-decree Paxos:

| Action | Gate | Effect |
|--------|------|--------|
| `p1b(p,i)` | `got1b[p][i] = false`, `prom[i] <= ballot[p]` | Set `prom[i] := ballot[p]`, `got1b[p][i] := true`, `rep[p][i] := acc[i]` |
| `p2a(p)` | `prop[p] = none`, `majority(got1b[p])` | Choose `v` with `safeAt(v, ballot[p])`, set `prop[p] := some v` |
| `p2b(p,i)` | `did2b[p][i] = false`, `prom[i] <= ballot[p]` | Read `v` from `prop[p]`, set `prom[i] := ballot[p]`, `acc[i] := (ballot[p], v)`, `did2b[p][i] := true` |

**Design choice: safeAt as the p2a constraint.**  An earlier version of
the model required p2a to adopt the value from the highest-ballot report
in the got1b quorum (the "max-vote rule").  We replaced this with
Lamport's `safeAt` predicate:
```
safeAt(v, b)  :=  forall c < b, exists majority Q,
  forall a in Q, votedFor(a, c, v) or wontVoteAt(a, c)
```
where `votedFor(a, c, v)` means an acceptor voted `v` at ballot `c`,
and `wontVoteAt(a, c)` means the acceptor's promise exceeds `c`.

The max-vote rule is one *implementation* of safeAt: it can be shown
that if the proposer adopts the highest-ballot report, the resulting
value satisfies safeAt.  By relaxing to safeAt directly, the atomic
model becomes a *specification* of what values are permissible, rather
than prescribing a particular selection algorithm.  This relaxation was
essential for the forward simulation (Section 4).

### 1.2  Invariant and Safety

The protocol invariant `PaxosInv` is a 10-field structure whose key
field is:
```
hSafe : forall q v, prop[q] = some v -> safeAt(v, ballot[q])
```

**Agreement** follows from safeAt and majority overlap: if two proposers
each have a majority of phase-2b votes, their values agree.

**Consensus refinement.**  A refinement mapping `paxos_ref` extracts the
first majority-decided value (if any) and maps to a two-action Consensus
specification (`choose1 | choose2`).  The refinement is proved via
`refinement_mapping_stutter_with_invariant`.

---

## 2  The Message-Passing Model

### 2.1  State

```
MsgPaxosState (n m : Nat) :=
  acceptors    : Fin n -> AcceptorState     -- prom, acc
  proposers    : Fin m -> ProposerState n   -- promisesReceived, proposed
  network      : List (Msg * Target)
  sentAccept   : Fin n -> Nat -> Option Value  -- ghost (acceptor-side)
  everProposed : Fin m -> Option Value         -- ghost (proposer-side)
```

The model has four message types (`prepare`, `promise`, `accept`,
`accepted`) and nine actions.

### 2.2  Locality

Every action's gate and transition reference only **local state** of
the acting node plus the incoming message:

| Action | Actor | Gate reads |
|--------|-------|-----------|
| `sendPrepare(p)` | proposer | (none) |
| `recvPrepare(a,p,b)` | acceptor | `prom[a]`, incoming `prepare` |
| `recvPromise(p,a,b,prior)` | proposer | incoming `promise` |
| `decidePropose(p,v)` | proposer | `promisesReceived[p]`, `proposed[p]`, `everProposed[p]` |
| `sendAccept(p,b,v)` | proposer | `ballot[p]`, `proposed[p]` |
| `recvAccept(a,p,b,v)` | acceptor | `prom[a]`, incoming `accept` |
| `dropMsg(idx)` | network | (none) |
| `crashProposer(p)` | proposer | (none) |
| `crashAcceptor(a)` | acceptor | (none) |

**No action reads another node's state or any global predicate.**  This
strict locality is a deliberate design goal, distinguishing this model
from earlier versions (see Section 5).

### 2.3  Ghost Fields

Two ghost fields record monotonic properties for the invariant:

- **`sentAccept : Fin n -> Nat -> Option Value`** records whether acceptor
  `a` has ever sent an `accepted` message at ballot `b` with value `v`.
  Updated by `recvAccept`; never cleared.  This is the acceptor-side
  analogue of `did2b` in the atomic model.

- **`everProposed : Fin m -> Option Value`** records whether proposer `p`
  has ever called `decidePropose` with value `v`.  Updated by
  `decidePropose`; never cleared, even by crash.  This ensures that
  all accept messages at a given ballot carry the same value, even
  across crash-recovery cycles.

### 2.4  The decidePropose Gate

The `decidePropose` action implements the standard Paxos phase 2a
value-selection rule, with four gate conditions:

1. **Majority:** `majority(promisesReceived[p] != none)` -- the
   proposer has collected a majority of phase 1 responses.

2. **Once-only:** `proposed[p] = none` -- the proposer has not yet
   decided in this crash-recovery cycle.

3. **Max-vote:** For any received promise with prior `(c, w)` that has
   the maximum ballot among all priors, `v = w`.  If no prior exists,
   `v` is unconstrained.

4. **Stable consistency:** `everProposed[p] = none` or
   `everProposed[p] = some v` -- if the proposer decided in a previous
   crash-recovery cycle, it must choose the same value.

The transition sets `proposed[p] := some v` and
`everProposed[p] := some v`.

### 2.5  Why the Network Gate Was Needed and Then Removed

An earlier iteration of the model included **non-local gates** on
`sendAccept`:

- `safeAt(s, v, b)` -- a global predicate over all acceptors
- `majority(fun j => prom[j] >= b)` -- reads all acceptors' promises
- `forall a v', sentAccept[a][b] = some v' -> v = v'` -- reads ghost state
- `forall p' v' tgt, (accept p' b v', tgt) in network -> v = v'` -- reads network

These were introduced because the original `decidePropose` was
unconditional (no gates), so `sendAccept` bore the entire safety burden.
This made `sendAccept` non-local: a proposer action reading the global
state of all acceptors.

**The fix** was to move the safety logic to `decidePropose` (where the
proposer actually makes the value choice) and reduce `sendAccept` to two
purely local gates: `ballot[p] = b` and `proposed[p] = some v`.  The
removed global conditions are now *derived* from the invariant:

- `safeAt` is derived from `decidePropose`'s max-vote gate via
  `sendAccept_gate_safeAt` (a 50-line theorem using `PromiseInv`).
- Network/sentAccept consistency follows from `everProposed` stability.
- The majority condition follows from `decidePropose`'s majority gate
  plus `PromiseInv` linking promises to acceptor state.

An intermediate version used network-reading gates (checking the
proposer's "outbox" for conflicting accept messages).  While defensible
as a model of the proposer's own sent-message history, this still reads
`s.network` which models messages in transit, not a local log.  The
`everProposed` ghost field replaces this cleanly: it is a stable,
proposer-local log of the proposer's commitment.

### 2.6  Invariant

`MsgPaxosInv` is a 19-field structure.  The fields divide into:

- **Acceptor-sentAccept links (5):** `hAccSent`, `hAccProm`,
  `hSentProm`, `hSentBallot`, `hAccMax`.
- **Network-ballot links (4):** `hNetPrepare`, `hNetAccept`,
  `hNetAccepted`, `hNetPromise`.
- **Value agreement (3):** `hSentUnique` (within a ballot, all
  sentAccept entries agree), `hAcceptValFun`, `hSentAcceptNet`.
- **Safety (2):** `hSentSafe`, `hNetSafe`.
- **Promise prior links (2):** `hNetPromisePrior`,
  `hNetPromiseNoVoteAbove`.
- **Ghost consistency (3):** `hNetAcceptProm`, `hEverProposedNet`,
  `hEverProposedSent`.

A separate `PromiseInv` (3 fields) links the volatile
`promisesReceived` to stable state.  A `ProposedSafeInv` (4 fields)
tracks properties that hold when `proposed[p] != none`.  All three
invariants are proved jointly by induction on `Reachable`.

### 2.7  Cross-Ballot Agreement and Consensus Refinement

`cross_ballot_agreement` establishes that at most one value can be
majority-accepted across different ballots.  `msg_paxos_refines_consensus`
maps the message-passing model to the same Consensus specification as
the atomic model, using a refinement mapping based on sentAccept
majorities.

---

## 3  The Forward Simulation

### 3.1  Direction and Framework

The simulation proves:

> Every execution of the message-passing model can be simulated by an
> execution of the atomic model (with stuttering).

Formally, this is a `SimulationRelInv` from `Leslie/Refinement.lean`:

```
SimulationRelInv :=
  concrete : Spec MsgPaxosState
  abstract : Spec PaxosState
  R        : MsgPaxosState -> PaxosState -> Prop
  inv      : MsgPaxosState -> Prop
  inv_init, inv_next, init_sim, step_sim
```

The concrete invariant is `Reachable ballot` (the full message-passing
reachability predicate, giving access to `MsgPaxosInv`, `PromiseInv`,
and `ProposedSafeInv`).

### 3.2  Simulation Relation

`SimRel` has 10 fields relating the two state spaces:

| Field | Type | Meaning |
|-------|------|---------|
| `prom_eq` | `prom[i] = ms.acceptors[i].prom` | Promises match directly |
| `acc_eq` | `acc[i] = vmapPair(ms.acceptors[i].acc)` | Acceptances match (modulo value mapping) |
| `did2b_eq` | `did2b[p][i] = isSome(sentAccept[i][ballot[p]])` | Phase 2b tracks the ghost log |
| `prop_none` | `all sentAccept = none -> prop[p] = none` | No votes implies no proposal |
| `prop_some` | `sentAccept[a][ballot[p]] = some v -> prop[p] = some(vmap v)` | Votes determine proposal |
| `got1b_iff` | `got1b[p][i] = true <-> prom[i] >= ballot[p]` | Phase 1b tracks promises (biconditional) |
| `rep_none` | `got1b = false -> rep = none` | No p1b implies no report |
| `rep_dom` | `got1b -> rep = (b,v) -> acc = (b',v') -> b <= b'` | Report dominated by current acceptance |
| `rep_acc` | `got1b -> acc = none -> rep = none` | No acceptance implies no report |
| `rep_sent` | `got1b -> rep = (bw,w) -> exists w', sentAccept[i][bw] = some w'` | Reports correspond to votes |

### 3.3  Action Mapping

| Message action | Abstract action(s) | Pattern |
|---|---|---|
| `sendPrepare` | (none) | stutter |
| `recvPrepare(a,p,b)` | `p1b(p',a)` for all `p'` with `ballot[p'] in (old_prom, b]` | multi-step Star |
| `recvPromise` | (none) | stutter |
| `decidePropose` | (none) | stutter |
| `sendAccept` | (none) | stutter |
| `recvAccept(a,p,b,v)` | multi-p1b + p2a (if first vote) + p2b | multi-step Star |
| `dropMsg` | (none) | stutter |
| `crashProposer` | (none) | stutter |
| `crashAcceptor` | (none) | stutter |

Seven of nine actions are stutter steps.  The non-trivial cases are
`recvPrepare` (which fires one or more atomic `p1b` steps to maintain
the `got1b_iff` biconditional) and `recvAccept` (which may fire `p2a`
and `p2b`).

### 3.4  The Multi-p1b Star Construction

When `recvPrepare(a, p, b)` raises `prom[a]` from some value below `b`
to `b`, the `got1b_iff` invariant demands that `got1b[p'][a] = true`
for every proposer `p'` with `ballot[p'] <= b`.  Some of these entries
may be newly required.  The `multi_p1b_star` theorem constructs a `Star`
(reflexive-transitive closure) of atomic p1b steps that fires one step
per newly-required entry, in increasing ballot order.

The proof uses strong induction on the count of "pending" proposers
(those needing `got1b` set to true).  At each step, the proposer with
the minimum pending ballot is fired, strictly decreasing the count.

### 3.5  The safeAt Translation

The final piece: when `recvAccept` fires for the first vote at a ballot
(the "B2" subcase), the abstract `p2a` requires `safeAt(v, ballot[p])`.
The message-level `MsgPaxosInv.hNetSafe` provides message-level safeAt
for the accept message.  We translate between the two models' safeAt
definitions via the SimRel:

- **votedFor translation:** `sentAccept[j][c] = some v` implies
  (via `hSentBallot`) existence of a proposer `r` with `ballot[r] = c`,
  and (via `did2b_eq`) `did2b[r][j] = true`, and (via `prop_some`)
  `prop[r] = some(vmap v)`.

- **wontVoteAt translation:** `sentAccept[j][c] = none` with `prom > c`
  maps directly via `prom_eq` and the contrapositive of `did2b_eq`.

The same quorum witness `Q` works for both levels.

---

## 4  Design Choices and Failed Alternatives

### 4.1  Max-Vote Rule vs. safeAt in p2a

The atomic model originally constrained p2a with the max-vote rule:
the proposer must adopt the value from the highest-ballot report in
its got1b quorum.  This is what a real Paxos implementation does.

**Problem:** The message-passing model's proposer may not see all
reports that the abstract model sees.  Specifically, `got1b_iff` sets
`got1b[p'][a] = true` whenever `prom[a] >= ballot[p']`, even if
proposer `p'` never received a promise from `a`.  The abstract `rep`
captures `acc[a]` at `recvPrepare` time, which may include votes the
concrete proposer never learned about.

**Counterexample (3 acceptors, ballots [1, 2]):**
1. All acceptors promise at ballot 1.  Proposer p0 sends accept(1, "red").
   Acceptor a0 votes "red".
2. Acceptors a1, a2 promise at ballot 2.  Proposer p1 collects promises
   from a1, a2 (no prior votes) and picks "blue".
3. Acceptor a0 also promises at ballot 2.  The abstract fires
   `p1b(p1, a0)`, setting `rep[p1][a0] = (1, "red")`.
4. When `recvAccept` fires for "blue", the abstract p2a sees a0's report
   ("red" at ballot 1) as the max-vote, but the concrete value is "blue".

**Resolution:** Replace the max-vote constraint with `safeAt`, which is
a weaker (more permissive) condition.  Since both the concrete and
abstract models enforce safeAt, the translation goes through.  The
max-vote rule *implies* safeAt, so the relaxed atomic model admits
strictly more behaviors while preserving safety.

### 4.2  Biconditional vs. One-Directional got1b

We considered a one-directional SimRel field:
```
got1b_prom : got1b[p][i] = true -> prom[i] >= ballot[p]
```
(without the reverse implication).  This avoids eager p1b firing but
creates a majority gap: at `recvAccept` time, the abstract may not have
enough `got1b` entries for `p2a`'s majority gate.  The biconditional
`got1b_iff` guarantees majority by construction (every acceptor with
high enough promise is included).

### 4.3  Firing p1b at recvPromise vs. recvPrepare

We considered firing p1b when the proposer *receives* the promise
(`recvPromise`) rather than when the acceptor *sends* it (`recvPrepare`).
This would make `got1b` track exactly what the proposer knows.

**Problem:** Between `recvPrepare` and `recvPromise`, the concrete
acceptor's `prom` changes but the abstract `prom` doesn't (no p1b
fired).  This breaks `prom_eq`.  Using `prom_le` (abstract <= concrete)
introduces ordering issues: if a higher-ballot `recvPromise` arrives
before a lower-ballot one, the higher p1b fires first, raising abstract
`prom` past the lower ballot, blocking the lower p1b's gate.

### 4.4  Non-Local Gates on sendAccept

The message-passing model evolved through three designs for `sendAccept`:

1. **Global gates (original):** `safeAt`, `majority(prom >= b)`,
   network consistency, sentAccept consistency.  Six gates, all
   reading global state.  *Rejected:* a proposer cannot observe all
   acceptors' promises or the network's contents.

2. **Outbox gates (intermediate):** Network consistency
   (`accept messages at b agree`) and ghost consistency
   (`sentAccept entries at b agree`).  *Rejected:* the network models
   messages in transit, which the proposer cannot observe.  The ghost
   log `sentAccept` is acceptor-side state, also non-local.

3. **Local gates (final):** `ballot[p] = b` and `proposed[p] = some v`.
   All safety conditions are derived from the invariant.  The
   `everProposed` ghost field ensures value stability across crash
   cycles without reading the network.

### 4.5  The Role of everProposed

Without `everProposed`, a proposer that crashes and re-proposes could
choose a different value if its old accept messages were dropped from
the network.  The network consistency gate (design 2) would prevent
this but requires reading in-transit messages.  The `everProposed`
field solves this locally: it is a stable record of the proposer's
commitment, never cleared by crash, analogous to `sentAccept` for
acceptors.

---

## 5  Proof Architecture

### 5.1  Invariant Decomposition

The message-passing invariant is split into three structures:

- **`MsgPaxosInv` (19 fields):** Over stable state only (acceptors,
  network, sentAccept, everProposed).  Proposer volatile state is never
  mentioned.  This makes `crashProposer` trivially safe.

- **`PromiseInv` (3 fields):** Links `promisesReceived` to stable state.
  Crash-vacuous (cleared promisesReceived has nothing to constrain).

- **`ProposedSafeInv` (4 fields):** Properties of `proposed`: network
  consistency, sentAccept consistency, safeAt, and majority.  Derived
  from `decidePropose`'s local gates.

All three are proved jointly by induction on `Reachable`, breaking a
mutual dependency cycle.

### 5.2  The multi_p1b_star Proof

The core technical lemma: given `prom[a] <= b`, construct a `Star` of
p1b steps raising `prom[a]` to `b`.  The proof uses:

1. A `pendingCount` function counting proposers with `ballot[p'] <= b`
   and `got1b[p'][a] = false`.
2. `Nat.strongRecOn` on the pending count.
3. An `exists_min_pending` lemma extracting the minimum-ballot pending
   proposer.
4. Fire p1b for the minimum, verify the recursive preconditions (the
   `got1b` biconditional and `rep_none` are maintained at the
   intermediate state), and show strict decrease of pending count.

### 5.3  The Refinement Chain

The complete formal chain:

```
MsgPaxos --[SimulationRelInv]--> AtomicPaxos --[refinement_mapping]--> Consensus
MsgPaxos --[refinement_mapping]--> Consensus
```

Both paths from MsgPaxos to Consensus are formally verified.  The
direct simulation (MsgPaxos -> AtomicPaxos) additionally validates the
structural correspondence between the two Paxos models.

---

## 6  Comparison with Related Work

To our knowledge, this is the first mechanized forward simulation
between an asynchronous message-passing Paxos model and a synchronous
atomic Paxos model in Lean 4, with all actions having strictly local
gates and all proofs sorry-free.  The key enabling insight is the
relaxation of p2a's value-choice constraint from the max-vote rule to
Lamport's safeAt predicate: the atomic model specifies *what* values
are safe, not *how* to select them.  This decoupling allows the
simulation to translate safety across the information-timing gap between
synchronous and asynchronous models.
