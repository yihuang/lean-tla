# Streamlet case study (Chan & Shi, 2020)

This directory formalizes Textbook Streamlined Blockchains (Streamlet) as
five layered Lean modules: from the most abstract consistency core, through
the partially synchronous network and the protocol layer, the state-level
liveness core, to the final temporal wrapper. Each file's header contains
more detailed design notes.

## Module structure

```
Core (Core.lean)             Abstract "message soup" model: consistency (safety)
  ↑
Net (Net.lean)               Partially synchronous transport: GST/Δ delivery bound (Fact 1)
  ↑
Proto (Proto.lean)           Protocol layer: propose/vote/Byzantine, invariant, Fact 2/3
  ↑
Liveness (Liveness.lean)     State-level liveness core: Lemma 5 and Theorem 6
  ↑
Temporal (Temporal.lean)     Temporal wrapper: per-epoch progress ⇒ Theorem 13
```

- `Core` is a standalone small model (a set of votes + a global clock) that
  proves consistency only; it has no proposals or leaders — they are
  irrelevant to consistency.
- `Net` introduces message-level transport (`inflight`/`seen`, a round
  clock, the GST/Δ delivery bound) and is the state-machine substrate of
  `Proto`.
- `Proto` layers the protocol actions (`Propose`/`VoteH`/`SendB`) on top of
  `Net`'s state, defines the cast history variables and the invariant
  bundle `Inv`, and proves Fact 2 and Fact 3.
- `Liveness` contains pure state-level theorems: Lemma 5 and the core of
  Theorem 6, derived from `Inv`.
- `Temporal` states the per-epoch honest-timing assumptions (clock
  advances, honest leaders propose, votes + delivery notarize in time) as
  leads-to predicates and composes them into the final liveness theorem.

Namespace layout: `Core` declares directly in `Bft.Examples.Streamlet`
(the shared vocabulary — `Blk`, `ValidChain`, `quorum`, `Consecutive`, the
abstract `VoteLog` state, `SafetyInv`, …); the other four nest one level
deeper (`Bft.Examples.Streamlet.{Net,Proto,Liveness,Temporal}`). The few
name clashes with the shared vocabulary were resolved by renaming inside
`Core` (`St` → `VoteLog`, `Tick` → `EpochTick`, `Inv` → `SafetyInv`). The
generic `Init`/`Next`/`vars` names are `private` in `Core`, `Net`, and
`Proto` (the latter's `PNext`): outside those modules they are reachable
only through the `Spec` bundles' fields — `(StreamletSpec n f Byz).Init`,
`(NetSpec n Byz Δ GST).vars`, `(ProtoSpec n Byz Δ GST f L).Next`, etc.;
`ProtoSpec` is the global spec and re-uses `NetSpec`'s `Init` and `vars`.
In `Proto` and `Temporal`, `local notation "S" => ProtoSpec n Byz Δ GST f L`
shortens the applied spec to `(S).Next` / `(S).vars`.
The umbrella module `Bft/Examples/Streamlet.lean` imports all five.

## Spec behavior (TLA+ pseudocode)

### Core: the message-soup model

State: `epoch ∈ Nat`, `msgs ⊆ Node × Blk` (`Blk = List Nat`; a block *is*
its prefix chain, epochs strictly decreasing, anchored at genesis).

```tla
VoteH(i, b) ≜                          \* honest vote
  ∧ i ∉ Byz
  ∧ ValidChain(b) ∧ head(b) = epoch    \* a block of the current epoch
  ∧ ∀ b' : (i,b') ∈ msgs → head(b') ≠ epoch   \* first vote this epoch
  ∧ NotarizedChain(tail(b))            \* parent chain notarized
  ∧ ∀ c : NotarizedChain(c) → Len(c) ≤ Len(tail(b))  \* ... and longest
  ∧ msgs' = msgs ∪ {(i,b)} ∧ epoch' = epoch

VoteB(i, b) ≜                          \* Byzantine vote: any well-formed block, any time
  ∧ i ∈ Byz ∧ ValidChain(b)
  ∧ msgs' = msgs ∪ {(i,b)} ∧ epoch' = epoch

Tick ≜ epoch' = epoch + 1 ∧ msgs' = msgs

Init ≜ epoch = 0 ∧ msgs = {}
Next ≜ Tick ∨ ∃ i,b : VoteH(i,b) ∨ VoteB(i,b)
```

where `Notarized(b) ≜ b = [0] ∨ |voters(b)| ≥ 2f+1` (`voters(b)` is the set
of distinct nodes that voted for `b`), and `NotarizedChain(c)` requires
every nonempty suffix block of `c` to be notarized.

### Net: the partially synchronous transport

State: `now` (round), `inflight`, `seen` (message sets), plus the history
variables `castVotes`/`castProps` (monotone accumulators of what was sent).
A message `m` carries `src`, `round`, and `body` (`.prop(e,b)` or
`.vote(b)`). The deadline is `max(GST, m.round + Δ)`.

```tla
Send(m) ≜ m.round = now ∧ m ∉ inflight ∪ seen
  ∧ inflight' = inflight ∪ {m} ∧ seen' = seen
  ∧ castVotes'/castProps' append the record corresponding to m.body

Deliver(m) ≜ m ∈ inflight
  ∧ (m.src ∉ Byz → now ≤ deadline(m))    \* no late delivery
  ∧ inflight' = inflight \ {m} ∧ seen' = seen ∪ {m}

Tick ≜ now' = now + 1 ∧ everything else unchanged
  ∧ ∀ m ∈ inflight : m.src ∉ Byz → now' ≤ deadline(m)  \* never cross a deadline

Next ≜ Tick ∨ ∃ m : Send(m) ∨ Deliver(m)
```

### Proto: the protocol layer (state = Net's state)

Epochs have length `2Δ`: `curEpoch(now) = now / (2Δ)`, with a leader table
`L : Nat → Node`.

```tla
Propose(e, b) ≜                        \* the honest leader's first proposal of the epoch
  ∧ ¬∃ b' : propCast(e, b')            \* no proposal yet this epoch
  ∧ L(e) ∉ Byz ∧ ValidChain(b) ∧ head(b) = e ∧ curEpoch(now) = e
  ∧ LongestNotarized(tail(b), e-1)     \* parent chain seen-notarized, cast-notarized by e-1, and longest
  ∧ Send(⟨L(e), now, .prop(e, b)⟩)

VoteH(i, b) ≜                          \* honest node's first vote of the epoch, on the leader's proposal
  ∧ i ∉ Byz ∧ ValidChain(b) ∧ 0 < head(b) ∧ head(b) = curEpoch(now)
  ∧ ¬∃ b' : voteCast(i, b') ∧ head(b') = head(b)   \* first vote this epoch
  ∧ propCast(head(b), b)               \* votes for the leader's proposal of that epoch
  ∧ LongestNotarized(tail(b), head(b)-1)
  ∧ Send(⟨i, now, .vote(b)⟩)

SendB(m) ≜ m.src ∈ Byz ∧ ValidBody(m) ∧ Send(m)   \* Byzantine: any well-formed message, any time (equivocation included)

Deliver and Tick as in Net.
PNext ≜ Tick ∨ ∃ e,b : Propose ∨ ∃ i,b : VoteH ∨ ∃ m : SendB ∨ ∃ m : Deliver
```

Key definitions: `voteCast i b ≜ (i,b) ∈ castVotes`;
`propCast e b ≜ (L(e), e, b) ∈ castProps` (proposals are accounted by
sender — a Byzantine stray `.prop` does not speak for the leader).
`NotarizedSeen b` (delivery side: counts all delivered votes) and
`NotarizedCast b` (cast side: counts honest votes only) both require
`2f+1`; `NotarizedBy b e ≜ NotarizedCast b ∧ b.epoch ≤ e`.

### Liveness / Temporal: temporal assumptions

`Temporal`'s spec `H` = `PSpec ∧ clock advances ∧ honest leaders propose ∧
votes notarize in time` (all per-epoch leads-to predicates); the liveness
conclusion is that after any window of 5 consecutive honest-leader epochs,
some block is final.

## Theorems and their dependencies (natural language)

Notation: `n = 3f+1`, `|Byz| ≤ f`, quorum = `2f+1`.

### Core (consistency)

| Theorem | Statement | Depends on |
|---|---|---|
| `safety` | `Inv` (the five-field invariant bundle IV/I0/I1/I2/I5) holds at every reachable state. | `init_inv`, `step_inv` (induction) |
| `unique_notarized` (paper Lemma 1) | At most one block per epoch is notarized: two quorums intersect in an honest node (`exists_honest_voter_of_two_quorums`, whose core is `Minimmit.exists_honest_inter`), and that node votes at most once per epoch (I1). | `safety`, quorum intersection, `honestUniq` |
| `consistency_of_inv` / `consistency` (paper theorem) | If a notarized chain ends in three adjacent blocks with consecutive epochs, no other block of the middle one's length can ever be notarized (consistency of the finalization rule). Three-way epoch analysis: equal-epoch cases fall to Lemma 1; earlier/later cases derive a length contradiction from I5 (`lengthMono`: an honest node's later votes have longer parents). | `safety`, `unique_notarized`, I5 |

### Net (Fact 1: Δ-bounded delivery)

| Theorem | Statement | Depends on |
|---|---|---|
| `delivery_safety` | The invariant `NoOverdue` (no honest in-flight message is past its deadline) holds — the safety half of delivery. | `init_inv`, `step_inv` (induction) |
| `delivered_by_deadline` (Fact 1, safety half) | An honest message past its deadline is necessarily in `seen`. | `delivery_safety` |
| `fact1_liveness` (Fact 1, liveness half) | Under `WF(Deliver m)`, an in-flight message is eventually delivered (via `wf1`, with the one-bit "still in flight" rank). | `pending_step/aq/enable`, `wf1` |

### Proto (protocol layer)

| Theorem | Statement | Depends on |
|---|---|---|
| `spec_entails_inv` | The protocol invariant bundle `Inv` (13 fields, including the one-directional bridge `sentMem`: every in-flight/delivered message is recorded in the cast histories) is preserved inductively by `PNext` — including arbitrary Byzantine sends. | `step_inv_tick/propose/voteh/sendb/deliver`, the vote-stability lemma `notarizedBy_stable_cast_vote` |
| `fact2` (paper Fact 2) | If `B` is notarized (delivery-side quorum), then every block of `B`'s parent chain is notarized in `seen`. Reason: the quorum contains an honest node (`honest_in_quorum`), which saw the parent chain notarized before voting (`voteParentSeen`), and `seen` is monotone. | `spec_entails_inv`, `honest_in_quorum`, `voteParentSeen` |
| `proposal_growth` / `proposal_growth_chain` (core of paper Fact 3) | The honest leader `L(e+1)`'s proposal `b₁` is strictly longer than any `b₀` chain-notarized by epoch `e`. Reason: `b₁` extends a longest chain notarized by epoch `e` (`propLongest`). | `spec_entails_inv`, `propLongest`, `propValid` |

### Liveness (state-level core)

| Theorem | Statement | Depends on |
|---|---|---|
| `voted_eq_proposal_of_epoch` | An honest node's vote in epoch `e₀` equals that epoch's honest-leader proposal (`voteOnLeaderProposal` + `propUniq`: at most one proposal per epoch). | `Inv.voteOnLeaderProposal`, `propUniq` |
| `voted_le_proposal_of_earlier_epoch` / `proposal_le_voted_of_later_epoch` | The two I5-style length monotonicity directions: an honest vote from an earlier epoch is no longer than the `e+1` proposal; a vote from a later epoch (`> e+2`) has tail at least as long as `b₂`. | `voteParentNotarizedBy`, `propLongest`, `votedLongest` |
| `longest_chain_by` | Given three consecutive honest proposals with growing lengths, any block notarized by epoch `e+2` is no longer than `b₂`. | `vote_case_of_proposals` (the five-way split), the two length lemmas above, `honest_in_quorum` |
| `main_liveness_lemma` (paper Lemma 5) | Three consecutive honest proposals with growing lengths, the third chain-notarized on time ⇒ no block other than `b₂` of `b₂`'s length is ever notarized. | `longest_chain_by`, `voted_eq_proposal_of_epoch`, the length lemmas |
| `next_proposal_extends` | Four consecutive honest proposals (growing lengths, last two notarized on time) ⇒ `b₃` directly extends `b₂` (`b₃ = (e+3) :: b₂`): the tail has the same length (squeezed by `longest_chain_by` + `propLongest`), and a different same-length block would contradict Lemma 5. | `main_liveness_lemma`, `longest_chain_by`, `proposal_parent_notarized` |
| `liveness_finality` (paper Theorem 6) | Five consecutive honest proposals with growing lengths, each chain-notarized on time ⇒ `b₃` is finalized (`b₂,b₃,b₄` form a `Consecutive` triple on a fully notarized chain). | `next_proposal_extends` ×2, `proposedEpoch` |

### Temporal (Theorem 13, abstracted to epoch granularity)

| Theorem | Statement | Depends on |
|---|---|---|
| `inv_all_of_pspec` | `Inv` holds at every point of a `PSpec` behavior. | `spec_entails_inv` |
| `epoch_step` | One epoch completes: from `curEpoch = e'`, the clock/propose/vote leads-to assumptions reach `curEpoch = e'+1` with that epoch's proposal chain-notarized. | `H`'s three assumptions, `propCast_persist_along` / `chainNotarizedBy_persist_along` |
| `window_progress` | By induction, from "k epochs remaining in the window" the window completes all 5 epochs. | `epoch_step`, `windowDone_advance` |
| `window_finality` | A completed window of 5 consecutive honest-leader epochs ⇒ some block is final. | `liveness_finality`, `proposal_growth_chain` (Fact 3 supplies the growing lengths) |
| `liveness_spec` (paper Theorem 13) | Under the honest-timing spec `H`, from the start of any 5-epoch honest-leader window some block is eventually finalized. | `window_progress`, `window_finality` |

**Known boundary (declared in each file's header)**: `Temporal`'s
honest-timing assumptions are a declared trust base, *not yet* derived from
`Net`'s Fact 1 plus weak fairness of `Propose`/`VoteH`/`Tick` — that is the
remaining refinement step. `Core`'s global-clock model proves consistency
only.
