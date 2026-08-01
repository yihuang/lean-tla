# Directory-Based MSI Cache Coherence Protocol

Mechanically verified proof in Lean 4 that a directory-based MSI cache coherence protocol
satisfies SWMR (Single Writer / Multiple Reader) and data integrity for any number of
cache nodes.

## The Protocol

A central directory manages N cache nodes communicating via point-to-point message channels.

**Cache states**: Modified (M), Shared (S), Invalid (I)

**Directory states**: Uncached, Shared, Exclusive

**Channels** (per node):
- `reqChan`: cache-to-directory request channel (getS, getM)
- `d2cChan`: directory-to-cache channel (gntS, gntE, inv, fetch)
- `c2dChan`: cache-to-directory response channel (ack with data)

**19 actions**:

| Action | Description |
|--------|-------------|
| SendGetS | Cache requests shared access |
| SendGetM | Cache requests exclusive access |
| RecvGetS_Uncached | Directory grants shared (was Uncached) |
| RecvGetS_Shared | Directory grants shared (was Shared) |
| RecvGetS_Exclusive | Directory sends fetch to M-holder (was Exclusive) |
| RecvGetM_Uncached | Directory grants exclusive (was Uncached) |
| RecvGetM_Shared | Directory begins invalidation (was Shared) |
| RecvGetM_Exclusive | Directory sends inv to M-holder (was Exclusive) |
| SendInv | Directory sends invalidation to a sharer |
| SendGntE_AfterShared | Directory grants exclusive after all acks received |
| SendGntE_AfterExclusive | Directory grants exclusive after writeback received |
| SendGntS_AfterFetch | Directory grants shared after fetch writeback |
| RecvGntS | Cache receives shared grant |
| RecvGntE | Cache receives exclusive grant |
| RecvInv | Cache receives invalidation, sends ack |
| RecvFetch | Cache receives fetch, sends ack with data |
| RecvAck_GetM_Shared | Directory processes invalidation ack |
| RecvAck_GetM_Exclusive | Directory processes writeback ack (getM flow) |
| RecvAck_GetS | Directory processes writeback ack (getS flow) |

The model is parameterized over N (number of nodes) using `Fin n` indexing.

## Properties Proved

**SWMR (`ctrlProp`)**: For any two distinct cache nodes i and j:
- If cache[i] is Modified, then cache[j] is Invalid
- If cache[i] is Shared, then cache[j] is not Modified

**Data integrity (`dataProp`)**:
- When the directory is not in Exclusive mode, main memory holds the true value
- Every non-Invalid cache holds the true value

```lean
theorem directoryMSI_invariant (n : Nat) :
    forall s, Reachable n s -> invariant n s
```

## Proof Structure

The proof uses an inductive invariant with **35 conjuncts** (`fullStrongInvariant`) that
strengthens the 2 public safety properties with 33 auxiliary invariants. The auxiliary
invariants fall into five categories:

**Directory-cache consistency** (6):
exclusiveConsistent, mImpliesExclusive, sImpliesShrSet,
exclusiveExcludesShared, uncachedMeansAllInvalid, curNodeNotInInvSet

**Data flow** (3):
gntSDataProp, gntEDataProp, ackDataProp

**Channel discipline** (7):
invAckExclusive, ackImpliesD2cEmpty, ackImpliesCurCmdNotEmpty,
getSAckProp, ackImpliesInvalid, ackImpliesInvSetFalse, invImpliesInvSetFalse

**Invalidation tracking** (5):
invSetSubsetShrSet, invSetImpliesCurCmdGetM, invSetImpliesDirShared,
invMsgImpliesShrSet, ackSharedImpliesShrSet

**Grant consistency** (8):
gntEImpliesExclusive, gntSImpliesDirShared, exclusiveNoDuplicateGrant,
sharedNoGntE, fetchImpliesCurCmdGetS, invImpliesCurCmd,
invExclOnlyAtExNode, ackExclOnlyAtExNode

**Uncached/Exclusive guards** (4):
ackImpliesDirNotUncached, invImpliesDirNotUncached,
ackExclOnlyAtExNode, gntSProp

## File Layout

| File | Lines | Description |
|------|-------|-------------|
| Model.lean | 695 | State, actions as named pure functions, simp lemmas, transition relation |
| Invariant.lean | 229 | All 35 invariant definitions and compound invariants |
| FrameLemmas.lean | 324 | Per-component frame lemmas + compound frame for trivial actions |
| InitProof.lean | 280 | Proof that initial states satisfy fullStrongInvariant |
| StepTier1.lean | 524 | RecvGetS_Shared, RecvGetM_Shared, RecvAck_GetM_Shared, SendGntS_AfterFetch |
| StepTier2.lean | 976 | SendInv, RecvGetS_Exclusive, RecvGetM_Exclusive, RecvGetM_Uncached, SendGntE (x2) |
| StepTier3A.lean | 322 | RecvAck_GetS, RecvAck_GetM_Exclusive |
| StepTier3B.lean | 412 | RecvGntS, RecvGntE |
| StepTier3C.lean | 512 | RecvInv, RecvFetch |
| StepProof.lean | 178 | SendGetS, SendGetM, RecvGetS_Uncached + dispatch hub |
| Theorem.lean | 24 | Reachable inductive, main theorem |
| **Total** | **4,476** | |

## Retrospective

### What Worked Well

**Frame lemma strategy**: Per-component frame lemmas eliminated ~80% of proof obligations.
For actions that don't modify the relevant state fields, preservation is a one-line application
of the frame lemma. The compound `fullStrongInvariant_preserved_of_reqChan_only` handled
SendGetS/SendGetM completely.

**Named state transformers**: Each action is a pure function (`recvInvState`, etc.) with a
separate guard predicate. This made simp lemmas predictable and proofs readable.

**Tiered proof split**: Ordering proofs by action complexity (directory-side first, then
cache-side, then ack processing) built a library of patterns that later tiers followed.
Each file stays under 1K lines, fitting in an LLM context window.

**`@[simp]` lemmas on the model**: The `_self`/`_ne` pattern for indexed fields made the
`by_cases k = i` dispatch mechanical and uniform.

**`subst hs'` early**: Substituting the state equation immediately after obtaining the
action guard keeps goals concrete and avoids reasoning about abstract `s'`.

### What Should Improve

**Boilerplate simp lemmas**: 249 `@[simp]` lemmas (~60% of Model.lean) are mechanically
derived from `{ s with ... }` expressions. A deriving handler or metaprogram that
auto-generates `_self`, `_ne`, and non-indexed field lemmas from the state transformer
definition would save significant effort.

**Fragile obtain patterns**: The 35-variable obtain pattern for `fullStrongInvariant`
(defined as nested `And`) had to be updated in every proof file each time a conjunct was
added. This was the single biggest source of bugs and wasted time. **Fix**: Define
`fullStrongInvariant` as a Lean 4 `structure` with named fields. Access by `h.fieldName`
instead of positional destructuring.

**`simp + refine` counting**: The exact number of `?_` placeholders in `refine` depends
on what `simp` resolves, which varies per action. Adding a definition to the simp list
changes the `?_` count unpredictably. **Fix**: Don't mix unfolding and construction in one
step. Either use structure-based construction (field-by-field) or handle new conjuncts
outside the simp+refine block using `unfold; intro` or frame lemma application.

**287 `by_cases k = i` blocks**: The dominant proof pattern for indexed fields. Nearly
identical structure each time. A custom `indexed_cases` elab tactic (not `macro_rules` --
Lean 4's typed syntax quotations can't splice idents into `simp [...]` positions) would
cut proof text by ~50%.

**Invariant discovery loop**: Growing from 12 to 35 conjuncts over multiple sessions consumed
~40% of total time. Starting with known invariant templates for cache coherence (directory
consistency, data flow, channel discipline, grant uniqueness) and batching additions would
reduce the overhead.

### Key Metrics

| Metric | Value |
|--------|-------|
| Total proof lines | 4,476 |
| Actions | 19 |
| Invariant conjuncts | 35 (2 public + 33 auxiliary) |
| `@[simp]` lemmas | 249 |
| `by_cases` blocks | 287 |
| Frame lemmas | 26 per-component + 1 compound |
| Proof obligations eliminated by frames | ~80% |
| Time to complete | ~8 hours across 3 sessions |

### Recommendations for the Next Protocol

1. **Use a structure for the invariant**, not nested `And`
2. **Auto-derive simp lemmas** from state transformer definitions
3. **Build an `indexed_cases` tactic** for the `by_cases k = i` + `_self`/`_ne` dispatch
4. **Start with invariant templates** from known categories before writing any proofs
5. **Batch invariant additions** (3-5 at a time) to minimize cross-file obtain pattern updates
6. **Prove init + 2 simplest actions first** to validate the invariant structure
7. **Test frame lemma coverage early** to determine the proof effort budget

With these improvements, the next protocol of similar complexity should take ~3 hours
instead of ~8.
