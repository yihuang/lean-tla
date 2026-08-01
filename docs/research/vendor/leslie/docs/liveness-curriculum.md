# Liveness Proof Curriculum for Leslie

A progression from trivial to advanced liveness proofs, building proof
infrastructure and experience before tackling TileLink.

## Background: What We Have

- **TLA core**: `always`, `eventually`, `leads_to`, `weak_fairness`
- **Rules**: `wf1` (WF1 rule), `leads_to_trans`, `leads_to_conseq`,
  `leads_to_combine`, `leads_to_strengthen_lhs`, `leads_to_exists`
- **Safety proofs**: complete for several examples (DirectoryMSI,
  GermanMessages, TileLink Atomic/Messages, Peterson, TwoPhaseCommit, etc.)
- **No completed liveness proofs**: TileLink Messages/Liveness is scaffolded
  but all theorems use `sorry`

## The Curriculum

### Level 1: Single WF1 Application (One Step)

**Goal**: Learn to apply WF1 in the simplest possible setting. No chains,
no well-founded induction, no auxiliary invariants.

#### 1a. CounterRefinement — "counter eventually reaches N"

**Spec**: The concrete counter increments by 1 with a phase bit.
**Property**: Under weak fairness of the increment action, the counter
eventually exceeds any bound.
**Why first**: Single action, single state variable, no process indices.
Pure mechanics of WF1 without any protocol reasoning.

**Proof sketch**:
- `p = (counter < N)`, `q = (counter ≥ N)`
- Fair action: the increment step
- Safety: increment preserves `counter < N` or advances to `≥ N`
- Progress: increment always advances
- Enablement: always enabled (unconditional action)

**Infrastructure built**: Basic pattern for writing `Spec.fair`, applying
`wf1`, and closing the four premises.

#### 1b. LeaderBroadcast — "follower eventually agrees with leader"

**Spec**: Round-based; reliable communication.
**Property**: The follower eventually holds the leader's value (within
one round).
**Why here**: Still a single WF1 step, but introduces indexed processes
and the round abstraction.

**Proof sketch**:
- `p = (follower ≠ leader)`, `q = (follower = leader)`
- Fair action: the round step
- After one fair round with reliable comm, the follower adopts the
  leader's value
- Relies on the existing safety proof of agreement after round ≥ 1

**Infrastructure built**: Fairness for round-based specs, interaction
between safety invariants and liveness.

---

### Level 2: Two-Step Chain (leads_to_trans)

**Goal**: Learn to compose `↝` links via `leads_to_trans`.

#### 2a. Peterson — "starvation freedom"

**Spec**: Peterson's mutual exclusion for 2 processes.
**Property**: Under weak fairness of all actions, if process 0 is in
`waiting` state, it eventually enters `cs`.

**Why here**: Two-step chain (`waiting ↝ cs_or_idle_other ↝ cs`), introduces
the pattern where progress depends on _another_ process's action. Classic
liveness example from the TLA literature.

**Proof sketch**:
- Link 1: If process 0 is waiting and process 1 is not in cs, then process
  0 can enter (from the safety invariant: `turn = 0 ∨ flag1 = false`).
- Link 2: If process 1 is in cs, weak fairness of exit1 means process 1
  eventually leaves cs.
- Compose via `leads_to_trans`.

**Key technique**: Using safety invariants (`mutual_exclusion`) as
hypotheses in liveness reasoning. This is the first example where
`leads_to_strengthen_lhs` is needed.

**Infrastructure built**: The `chain2` pattern, `leads_to_strengthen_lhs`
with safety invariants.

#### 2b. TwoPhaseCommit — "if all RMs are prepared, coordinator eventually decides"

**Spec**: Two-phase commit with coordinator and 2 RMs.
**Property**: Under weak fairness of the coordinator's commit action,
once all RMs have voted "prepared", the coordinator eventually commits.

**Proof sketch**:
- Link 1: `allPrepared ↝ tmCommitted` (WF1 on coordinator commit)
- Link 2: `tmCommitted ↝ allCommitted` (WF1 on RM commit notification)
- Compose via `leads_to_trans`.

**Infrastructure built**: Fairness for `ActionSpec` (not just `Spec`),
multi-action weak fairness lists.

---

### Level 3: Well-Founded Induction (Ranked Leads-To)

**Goal**: Handle the case where a single WF1 doesn't suffice because
progress requires multiple steps of a decreasing measure.

#### 3a. AllGather — "all processes eventually have all values"

**Spec**: Each process broadcasts its value; processes collect all values.
**Property**: Under weak fairness, every process eventually has all n values.

**Why here**: The "remaining values to collect" count decreases with each
round but we need multiple rounds. Natural well-founded argument on
`|{values not yet collected}|`.

**Proof sketch**:
- Define measure: `m(s, i) = |{j | val_j ∉ collected_i(s)}|`
- WF1 per round: each fair round reduces m by at least 1 (under reliable comm)
- Induction on m: `m = k ↝ m < k` for each k, compose to `m = 0`

**Key technique**: `leads_to_exists` to handle the quantified measure,
well-founded induction on `Nat`.

**Infrastructure built**: The ranked leads-to pattern, which is exactly
what TileLink needs for `probing_leads_to_grantReady` (induction on
remaining probes).

#### 3b. FloodMin — "all processes eventually agree on the minimum"

**Spec**: Each process floods its minimum-seen value.
**Property**: After `diam` rounds, all processes hold the global minimum.

**Why here**: Similar to AllGather but with a convergence argument (the
minimum propagates hop-by-hop). Introduces the idea of a _progress measure
that depends on network topology_.

---

### Level 4: Multiple Interleaved Chains

**Goal**: Handle protocols where multiple entities must coordinate, and
liveness depends on the interleaving.

#### 4a. TicketLock — "every acquire eventually enters CS"

**Spec**: Ticket lock with 2 threads.
**Property**: Under weak fairness of all thread actions, every acquire
eventually enters the critical section.

**Why here**: The waiting thread's progress depends on _all threads ahead
of it_ finishing. This is a multi-step chain where the length depends on
runtime state.

**Proof sketch**:
- Define `dist(t) = (serving - ticket_t) mod n` (tickets ahead)
- Each time a thread leaves CS, serving increments, reducing dist for all
  waiting threads
- WF1 per leave action, induction on dist

**Key technique**: Combining `leads_to_exists` with `leads_to_trans` over
a state-dependent chain length. Also exercises fairness for specs with
both internal and external actions.

#### 4b. KVStore — "every operation eventually returns"

**Spec**: Key-value store with linearizable operations.
**Property**: Under weak fairness, every invoked operation eventually
returns a response.

**Why here**: Multiple concurrent operations, progress depends on
serialization order. Intermediate complexity before TileLink.

---

### Level 5: Protocol-Specific Liveness (Cache Coherence)

**Goal**: Apply everything to cache coherence, first in simpler models.

#### 5a. MESI — "every cache request eventually completes"

**Spec**: MESI protocol (4 states, no messages, bus-based).
**Property**: Under weak fairness, a read/write request eventually completes.

**Why here**: Cache coherence concepts (invalidation, exclusive access) but
with a simpler state machine than TileLink. No channels, no transactions,
no probing waves.

**Proof sketch**:
- Read request: `Invalid ↝ Shared/Exclusive` (WF1 on bus read)
- Write request: `Shared ↝ Exclusive` (WF1 on bus invalidate)
- Other caches downgrade: guaranteed by weak fairness of their snoop actions

#### 5b. DirectoryMSI — "every upgrade eventually completes"

**Spec**: Directory-based MSI with messages.
**Property**: Under weak fairness of all message receive/send actions,
a cache requesting M permission eventually gets it.

**Why here**: Has the probe/invalidation wave pattern that TileLink uses,
but in a simpler protocol (3 states vs TileLink's 5 permission levels,
fewer channels).

**Proof sketch**:
- Request arrives at directory → invalidations sent to sharers
- Each invalidation acknowledged (WF1 per sharer)
- All acks received → grant sent (well-founded induction on sharer count)
- Grant received → upgrade complete

This is essentially a dress rehearsal for TileLink's acquire wave.

---

### Level 6: TileLink (the Target)

With Levels 1-5 complete, the TileLink liveness proof becomes a matter of
assembling known techniques:

| TileLink phase | Technique from curriculum |
|----------------|--------------------------|
| chanA consumed (recvAcquire) | Single WF1 (Level 1) |
| probing terminates | Well-founded induction on probe count (Level 3) |
| grant sent (sendGrant) | Single WF1 (Level 1) |
| grant received (recvGrant) | Single WF1 (Level 1) |
| grantAck received (recvGrantAck) | Single WF1 (Level 1) |
| Full chain composition | leads_to_trans (Level 2) |
| Auxiliary invariants | Safety + liveness interaction (Level 2a) |

## Implementation Priority

For maximum ROI, implement in this order:

1. **1a (CounterRefinement)** — minimal overhead, establishes the basic WF1
   pattern and the `Spec.fair` / liveness proof file structure
2. **2a (Peterson)** — classic example, introduces `leads_to_trans` and
   safety-liveness interaction
3. **3a (AllGather)** — the well-founded induction pattern, directly needed
   for TileLink's probe termination
4. **5b (DirectoryMSI)** — full dress rehearsal for TileLink in a simpler
   protocol

Levels 1b, 2b, 3b, 4a, 4b, 5a are valuable for completeness but can be
deferred. The path 1a → 2a → 3a → 5b → TileLink is the critical path.

## Infrastructure to Build Along the Way

Each level should contribute reusable infrastructure:

| Level | Infrastructure |
|-------|---------------|
| 1a | `ActionSpec.withFairness` helper, basic WF1 proof template |
| 1b | `RoundSpec.withFairness`, round-based liveness lemmas |
| 2a | `chain2`/`chain3` helpers, `leads_to_strengthen_lhs` usage patterns |
| 3a | Ranked leads-to macro/helper, well-founded induction on `Finset.card` |
| 4a | State-dependent chain composition |
| 5b | Message-passing liveness patterns, channel emptiness as enablement |

## What Could Go Wrong

Based on the TileLink safety experience:

1. **Missing rules**: We may need `SF1` (strong fairness), `WF2`, or lattice
   rules not yet in `Leslie/Rules/`. Build them when needed, not speculatively.

2. **Enablement proofs are harder than expected**: Showing `p ⇒ Enabled a`
   requires constructing a witness state `s'` such that `a s s'`. For complex
   actions this can be tedious. Consider a tactic that constructs witnesses.

3. **Auxiliary invariants for liveness**: TileLink already needed 2 new
   invariants (`pendingSinkInv`, `pendingSinkTxnInv`). Each requires a full
   inductive proof over all actions. Budget for this in every level.

4. **Interference between processes**: In multi-process liveness, showing
   that other processes' actions don't break the current process's progress
   requires careful safety reasoning. The `leads_to_strengthen_lhs` rule
   is the key tool here.
