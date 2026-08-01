# Tutorial: Round-Based Algorithms in Leslie

## What this document covers

This tutorial explains how to model and verify distributed algorithms
using Leslie's round-based framework. It covers:

1. The Heard-Of model and communication closure
2. How to specify a round-based algorithm
3. How to state and prove safety properties
4. The cutoff theorem for automatic verification
5. A worked example: OneThirdRule consensus

No Lean syntax is required to follow the tutorial — we focus on the
concepts, proof strategies, and intuitions. The Lean formalization
is in the `Leslie/Round.lean`, `Leslie/Cutoff.lean`, and
`Leslie/Examples/` files.

---

## 1. The Heard-Of Model

### The problem with asynchronous reasoning

Distributed protocols are hard to verify because of asynchrony:
messages can be delayed, reordered, or lost. In a fully asynchronous
model, a process might receive a message from 100 rounds ago mixed
with fresh messages. Reasoning about what a process "knows" requires
tracking the entire message history — an unbounded state space.

### Communication-closed rounds

The **Heard-Of (HO) model** (Charron-Bost & Schiper, 2009) simplifies
this by structuring computation into **rounds**. Each round has three
phases:

1. **Send**: every process broadcasts a message (determined by its
   current state).
2. **Receive**: every process receives a subset of the messages sent
   in this round.
3. **Update**: every process updates its state based on the received
   messages.

The key property is **communication closure**: messages from round r
are either delivered in round r or lost forever. A process never
receives stale messages from earlier rounds.

### Heard-Of sets

For each round r and process p, the **Heard-Of set** HO(p, r) is the
set of processes whose round-r messages were delivered to p. Different
processes may have different HO sets (modeling unreliable communication),
but the communication closure guarantee holds for all.

### Communication predicates

The fault model is captured by a **communication predicate** — a
constraint on which HO sets are valid. Examples:

- **Reliable**: HO(p, r) = all processes, for every p and r.
  (All messages delivered — synchronous, fault-free.)

- **Two-thirds**: |HO(p, r)| > 2n/3 for every p and r.
  (Each process receives "enough" messages, but possibly different
  subsets. Models partial synchrony with f < n/3 faults.)

- **Lossy**: No constraint. (Any HO set is valid — models fully
  unreliable communication.)

### Why communication closure helps

Communication closure gives us a crucial property:

> **Received messages reflect the current state.**
>
> If process p receives value v from process q in round r, then q
> held value v at the start of round r.

This means received vote counts are bounded by actual current holder
counts. If 10 processes hold value 0 at the start of the round, then
no process can receive more than 10 votes for value 0 — regardless
of its HO set. There are no stale messages inflating the count.

Without communication closure (e.g., in asynchronous protocols), a
process might receive old messages carrying value 0 from processes
that have since switched to value 1. The received count for value 0
would overestimate the current holder count, breaking the reasoning.

---

## 2. Specifying a Round-Based Algorithm

### The RoundAlg structure

A round-based algorithm is specified by three components:

- **init(p, s)**: the initial state predicate for process p.
- **send(p, s)**: the message that process p broadcasts given its
  current state s. (In the basic HO model, every process sends the
  same message to everyone.)
- **update(p, s, msgs)**: how process p updates its state given its
  current state s and the received messages msgs. The messages are a
  function `msgs : Process → Option Message` — for each potential
  sender q, either `some m` (the message from q was delivered) or
  `none` (not delivered, i.e., q ∉ HO(p)).

### The global state

The global state tracks:
- **round**: the current round number (0 = initial, before any round).
- **locals**: a function mapping each process to its local state.

### The transition relation

One round step from state s to state s':
- s'.round = s.round + 1
- For each process p:
  s'.locals(p) = update(p, s.locals(p), delivered(s, ho, p))

where `delivered(s, ho, p)(q) = if ho(p, q) then some(send(q, s.locals(q))) else none`.

The HO collection `ho` is existentially quantified — the environment
chooses it, subject to the communication predicate.

### Example: OneThirdRule

The OneThirdRule is the simplest consensus algorithm in the HO model:

- **State**: each process holds a natural number value and optionally
  a decision.
- **Send**: broadcast your current value.
- **Update**: collect received values. If more than 2n/3 carry the
  same value v, adopt v and decide v. Otherwise, keep your current value.
- **Communication predicate**: every process hears from > 2n/3 senders.

---

## 3. Proving Safety Properties

### The round invariant rule

The main proof rule for round-based algorithms is the **round invariant
rule**: to prove that a property holds at all times, show:

1. **Init**: the property holds in the initial state.
2. **Step**: if the property holds before a round, it holds after the
   round — for ANY valid HO collection.

This reduces temporal reasoning ("the property holds forever") to
single-round reasoning ("the property is preserved by one step").

### Example: OneThirdRule agreement

**Property**: if process p decided v and process q decided w, then v = w.

**Proof strategy**: we don't prove agreement directly. Instead, we
prove a stronger **lock invariant** and derive agreement from it.

#### The lock invariant

> If any process has decided value v, then more than 2n/3 of all n
> processes currently hold value v.

This says: a decision "locks in" a super-majority. The lock invariant
implies agreement by **pigeonhole**: if two values v ≠ w are both
decided, then each needs > 2n/3 holders. But the holder sets are
disjoint (a process holds exactly one value), and two disjoint sets
of size > 2n/3 would need > 4n/3 > n elements total. Contradiction.

#### Proving the lock is inductive

The lock invariant holds initially (no decisions → vacuously true).
The inductive step has three parts:

**(a) Establishing the lock in the pre-state.**

If some process p has `decided = some v` in the post-state, either
p already had the decision (use the inductive hypothesis) or p newly
decided in this round. If p newly decided v, then `findSuperMajority`
returned v for p's received messages, meaning > 2n/3 of p's received
messages carried v. Each such message came from a distinct sender who
held v. So > 2n/3 processes held v at the start of the round.

Here, **communication closure** is essential: we conclude that the
senders held v at the START of this round (not at some earlier time),
because messages from past rounds don't exist.

**(b) The lock persists: no competing value can emerge.**

We show that every process q that held v before the round still holds
v after. The argument: `findSuperMajority` on q's received messages
can't return w ≠ v, because:

- Votes for w in q's received messages ≤ total w-holders
  (by communication closure: received votes reflect current state).
- Total w-holders ≤ n - (> 2n/3) < n/3 (since v has > 2n/3 holders
  and v-holders and w-holders are disjoint).
- So votes for w < n/3 < 2n/3 — NOT a super-majority.

Therefore `findSuperMajority` returns either `some v` (q adopts v)
or `none` (q keeps its current value v). Either way, q still holds v.

Again, **communication closure** is the key: the bound "votes ≤ holders"
holds because there are no stale messages from past rounds.

**(c) Counting.**

Since every v-holder in the pre-state is still a v-holder in the
post-state, the count of v-holders doesn't decrease:

  countHolding(v, s') ≥ countHolding(v, s) > 2n/3. ✓

#### Validity: decided values are initial values

A separate property: any decided value was the initial value of some
process. The proof: in each round, the update function either keeps
the current value or adopts a value from received messages (which came
from senders' current values). So values only propagate — no new values
are created. By induction on time, every value traces back to an
initial value.

---

## 4. The Cutoff Theorem

### Motivation

The lock invariant proof above works for **all n** simultaneously.
But for more complex protocols, the inductive step might be too
tedious to prove by hand. Can we instead verify safety for a few
small values of n and conclude it holds for all n?

### When cutoffs work: three conditions

A cutoff reduction requires three conditions on the protocol:

**1. Process symmetry.** The algorithm treats all processes identically.
The send and update functions don't depend on the process ID. This
means the global state can be abstracted to a **configuration**: a
count of how many processes hold each value, rather than tracking
which specific process holds what.

**2. Threshold-based decisions.** The update function depends on
received messages only through **threshold comparisons**: "did value v
appear more than α·n times?" It does NOT depend on exact counts or
on which processes sent which messages. This means the update factors
through a finite **threshold view** — a Boolean vector indicating
which values crossed the threshold.

**3. Communication closure.** Messages from round r are delivered in
round r or lost forever. This ensures that threshold views computed
from received messages are consistent with the global configuration.
Without communication closure, received vote counts could be inflated
by stale messages, and the threshold view would not reflect reality.

### The threshold view abstraction

Under these conditions, the protocol's behavior is determined by the
**threshold view** — which values have counts exceeding α·n. For
binary values (k=2), there are only 3 realizable threshold views:

- **(T, F)**: value 0 has super-majority, value 1 doesn't.
- **(F, T)**: value 1 has super-majority, value 0 doesn't.
- **(F, F)**: neither has super-majority.
- **(T, T)**: impossible by pigeonhole (would need > 2α·n > n total).

The update function maps each (current_value, threshold_view) pair to
a new value. This is a finite table — independent of n.

### The cutoff bound

The **cutoff bound** K depends on the number of distinct values k
and the threshold fraction α = α_num/α_den:

    K = ⌈k · α_den / (α_den - α_num)⌉ + 1

For OneThirdRule (k=2, α=2/3): K = 7.

### The theorem

> If a threshold-determined invariant holds for all configurations
> at all n ≤ K, then it holds for all configurations at all n.

**Proof sketch**: For any configuration c at any n, its threshold
view is some pattern tv. By the **scaling lemma**, there exists a
configuration c' at some n' ≤ K with the same threshold view. Since
the invariant is threshold-determined (depends only on the threshold
view), the invariant agrees on c and c'. Since n' ≤ K, the small-n
verification covers c'. Therefore the invariant holds for c.

The scaling lemma is where **communication closure** is used: the
threshold view captures all relevant information about the round
transition because received messages reflect the current configuration
(no stale messages). Without this, the transition would depend on
message history, the threshold view wouldn't suffice, and the scaling
argument would fail.

### Unreliable communication

The cutoff works even under unreliable communication (different
processes see different HO sets), as long as the communication
predicate constrains the HO sets enough. The key property:

> No process can see a competing value above threshold.

Under the 2/3-communication predicate, if value v has > 2n/3 holders,
then the non-v holders number < n/3. Since votes ≤ holders
(communication closure!), no process can receive > 2n/3 votes for
any non-v value, regardless of its HO set.

This means the nondeterminism from HO sets affects WHICH processes
adopt the dominant value, but NOT whether the invariant is preserved.

### Using the cutoff for verification

The cutoff theorem reduces infinite verification to finite checking:

1. **Define** the protocol as a symmetric threshold algorithm.
2. **Define** the invariant as a configuration-level property.
3. **Verify** the invariant for all configurations at n ≤ K.
   (This is a finite check — can be done by `native_decide` in Lean,
   or by an external model checker like TLC.)
4. **Apply** the cutoff theorem to get the result for all n.

Step 3 is the "model checking" step. For OneThirdRule with k=2 and
K=7, there are about 330 configurations to check. For larger protocols,
the cutoff may be larger but still finite.

---

## 5. Worked Example: OneThirdRule End-to-End

### Step 1: Specify the algorithm

```
Algorithm OneThirdRule:
  State:   (val : Nat, decided : Option Nat)
  Send:    broadcast val
  Update:  let received = [messages from HO set]
           if some value v appears > 2n/3 times in received:
             val := v; decided := some v
           else:
             keep current state
  CommPred: every process hears from > 2n/3 senders
```

### Step 2: Identify the invariant

The **lock invariant**:

    ∀ v, (∃ p, p.decided = some v) → countHolding(v) > 2n/3

"If anyone decided v, then more than 2n/3 of all processes hold v."

### Step 3: Prove the invariant is inductive

**Init**: No decisions → antecedent is false → vacuously true. ✓

**Step**: Given the lock holds in state s, show it holds in s'.

The proof decomposes into:

- **Establishing the lock in s**: trace a new decision back to > 2n/3
  holders via the counting bound (votes ≤ holders, by communication
  closure).
- **Lock persists**: no competing value can reach a super-majority
  (pigeonhole: w-holders < n/3 < 2n/3, so w-votes < 2n/3 in any
  HO set).
- **Count doesn't decrease**: v-holders keep v (can't be lured to
  a competing value), so the count is monotone.

### Step 4: Derive agreement

From the lock invariant, agreement follows by pigeonhole:

- If v decided and w decided, both have > 2n/3 holders.
- Disjoint sets of size > 2n/3 would need > 4n/3 > n elements.
- Contradiction. So v = w. ✓

### Step 5 (optional): Apply the cutoff

For a model-checking approach:

1. Encode the state as Fin 4 (val × decided for binary values).
2. Define the lock invariant at the configuration level.
3. Verify for n ≤ 7 by exhaustive enumeration (330 configs).
4. Apply the cutoff theorem: lock holds for all n.

The cutoff argument uses the same three-condition check:
- Process symmetry ✓ (update doesn't depend on process ID)
- Threshold-based ✓ (only checks > 2n/3 counts)
- Communication closure ✓ (by the HO model)

### Step 6: Derive validity

Any decided value was an initial value.

Proof by induction on time: the update function either keeps the
current value or adopts a value from received messages. Received
values are current sender values (communication closure!). So values
only propagate, never appear from nothing. By induction, every value
traces back to some process's initial value.

---

## 6. Summary: Why Round-Based Reasoning Helps

### What the round structure gives you

1. **No message buffers.** Communication closure eliminates the need
   to track pending messages. The state is just the local states of
   the processes — no message queues, no delivery ordering.

2. **Received = current.** The `countOcc_le_countHolding` bound —
   votes for v in received messages ≤ total current v-holders — is
   the workhorse of every safety proof. It holds because of
   communication closure.

3. **Round induction.** The round invariant rule reduces temporal
   reasoning to single-step reasoning. You prove one round step,
   and the framework gives you "always."

4. **Finite threshold views.** For symmetric threshold protocols,
   the behavior is determined by a finite Boolean vector (which values
   cross the threshold). This enables cutoff arguments: check finitely
   many cases, conclude for all n.

### What communication closure gives you specifically

Without communication closure, NONE of the following work:

- **Counting bounds** (votes ≤ current holders): stale messages
  could inflate vote counts beyond the current holder count.
- **Pigeonhole arguments** (two super-majorities can't coexist):
  the pigeonhole uses the counting bound, which depends on
  communication closure.
- **Cutoff scaling** (same threshold view at different n implies
  same behavior): the threshold view must reflect the current
  configuration, not message history.
- **Lock persistence** (v-holders can't be lured away): a process
  holding v keeps v because no competing value can reach a
  super-majority in its received messages. This uses the counting
  bound, which uses communication closure.

### The proof architecture

```
Safety Property (e.g., agreement)
│
├── Derived from an inductive invariant (e.g., lock invariant)
│   │
│   ├── Init: trivial (no decisions)
│   │
│   └── Step: preserved by one round
│       │
│       ├── Counting bound (votes ≤ holders)
│       │   └── Uses: communication closure
│       │
│       ├── Pigeonhole (no competing super-majority)
│       │   └── Uses: counting bound + disjoint sets
│       │
│       └── Monotonicity (dominant value count doesn't decrease)
│           └── Uses: pigeonhole (no one switches away)
│
└── (Optional) Cutoff: reduce to finite checking
    │
    ├── Threshold view abstraction (finite Boolean vector)
    │   └── Uses: communication closure (views reflect current state)
    │
    ├── Scaling lemma (same view realizable at small n)
    │
    └── Model checking at n ≤ K
```

---

## Files in the project

| File | What it contains |
|------|-----------------|
| `Leslie/Round.lean` | RoundAlg, RoundSpec, round_invariant, utility lemmas |
| `Leslie/Cutoff.lean` | Config, ThreshView, SymThreshAlg, cutoff_reliable |
| `Leslie/Examples/OneThirdRule.lean` | Full direct proof: agreement + validity |
| `Leslie/Examples/OneThirdRuleCutoff.lean` | Cutoff-based proof: lock invariant at config level |
| `Leslie/Examples/BallotLeader.lean` | Leader election with majority pigeonhole |
| `Leslie/Examples/FloodMin.lean` | Flood-min consensus with refinement |
| `Leslie/Examples/VRViewChange.lean` | VR view change safety (quorum intersection) |
| `docs/mc-tactic-plan.md` | Plan for model-checking tactic |
| `docs/zero-one-rule.md` | Plan for zero-one reduction |
