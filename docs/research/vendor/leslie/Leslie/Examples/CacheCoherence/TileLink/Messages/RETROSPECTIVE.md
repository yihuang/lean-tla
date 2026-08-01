# Retrospective: TileLink Message-Level Refinement with Dirty Data

## Summary

The TileLink message-level model was extended from a clean-only refinement
(`noDirtyInv`) to full dirty data support (store, dirty-source acquires,
probeAck memory writeback, dirty releases). The forward-simulation theorem
`messages_refines_atomic` is sorry-free with the complete refinement chain:
Messages -> Atomic -> Sequential Memory.

This document captures lessons learned, proof strategies, and recommendations
for future protocol verification work in Leslie.

## Effort Breakdown

| Phase | Effort | Sorry trajectory | Notes |
|-------|--------|-----------------|-------|
| Model changes | Low | 0 -> 19 | Mechanical: add action, change guards |
| Cascade repair | Medium | 19 -> 2 | Fix downstream `rcases` patterns |
| Invariant replacement | **High** | 2 -> 22 -> 13 | Most time lost here |
| Protocol reasoning | Medium | 13 -> 6 | SWMR, probe masks |
| Dirty data flow | High | 6 -> 0 | Invariant weakening/strengthening |

**~60% of effort was on invariant restructuring** -- changing definitions,
fixing cascading breakage, reverting when changes made things worse.

## What Went Wrong

### 1. Invariant definitions were changed mid-proof

Every modification to `noDirtyInv`, `cleanDataInv`, `cleanChanCInv`,
`preLinesCleanInv`, or `txnDataInv` broke dozens of downstream proofs.
Destructuring patterns like `⟨hfull, hnoDirty, htxnData, hcleanRel, hrelUniq⟩`
broke whenever a component was added or removed. Multiple attempts made things
worse (13 -> 23 sorry), requiring reverts.

### 2. Tightly coupled invariant hierarchy

`refinementInv` -> `forwardSimInv` -> `strongRefinementInv` created a chain
where any definition change propagated through 5+ files. Positional
destructuring was the main failure mode.

### 3. Missing invariants discovered late

The need for `permSwmrInv`, `releaseUniqueInv`, `cleanChanCInv` data tracking,
and the `txnDataInv` phase-aware conjunct were all discovered when a sorry
couldn't be closed. Each discovery triggered a new round of definition changes.

### 4. Guards added incrementally

We added `currentTxn = none`, then `releaseInFlight = false`, then
`forall j, releaseInFlight j = false` to various invariants and action guards
over multiple sessions. Each addition was a separate round of cascading fixes.

## What Worked Well

### 1. Adding guards to action predicates

Adding `forall j, chanC j = none` to `Store` and `forall j, releaseInFlight j = false`
to `RecvAcquire*` closed sorry stubs immediately without cascading. Existing
proofs absorbed extra conjuncts via wildcards in `rcases`.

### 2. The `preLines` snapshot architecture

Capturing pre-wave local state in `ManagerTxn.preLines` was the key design
decision that made dirty writeback reasoning possible.

### 3. Strengthening invariants (adding conjuncts)

Strengthening is safe: removing a hypothesis from an invariant makes it harder
to violate but easier to use. Adding the phase-aware `txnDataInv` conjunct
`(grantReady | grantPendingAck) -> transferVal = mem` closed the last sorry
cleanly. Contrast with weakening (adding guards like `currentTxn = none ->`),
which makes the invariant easier to preserve but harder to use.

### 4. Parallel agents for independent files

When proof obligations were in different files (StepRelease, SimAcquire,
SimOther), parallel agents were effective.

## Generalizable Proof Strategy Hints

These principles apply to any protocol refinement proof in Leslie, not just
TileLink.

### Hint 1: Design invariants before starting proofs

For each new feature (e.g., "add dirty data support"):

1. List all state transitions that involve the new feature
2. Trace data flow through the complete lifecycle
3. Design invariants with the RIGHT guards from the start
4. Include phase-awareness from the beginning
5. Review the design before writing any Lean code

A 30-minute design session saves days of trial-and-error.

### Hint 2: Prefer action guard strengthening over invariant weakening

When a proof needs a fact that isn't available:

- **First choice**: Add the fact as a guard to the action predicate.
  This is the least disruptive change -- existing proofs absorb extra
  conjuncts via wildcards in `rcases`.
- **Second choice**: Add a conjunct to an existing invariant (strengthening).
  This is also safe -- removing a hypothesis makes the invariant stronger.
- **Last resort**: Add a guard/condition to an invariant (weakening).
  This changes the invariant's usability and cascades to all callers.

### Hint 3: Separate "easy to preserve" from "easy to use"

An invariant that's easy to preserve (has many guards) is hard to use (callers
must satisfy all guards). An invariant that's easy to use (unconditional) is
hard to preserve (every action must maintain it).

The sweet spot: unconditional invariants for stable properties (SWMR, dirty
exclusivity), phase-guarded invariants for transient properties (data coherence
during transactions).

### Hint 4: Use structures for invariant composition

Instead of flat conjunctions:
```lean
def refinementInv := A ∧ B ∧ C ∧ D ∧ E ∧ F
```

Use structures:
```lean
structure RefinementInv (n : Nat) (s : State n) where
  full : fullInv n s
  dirtyEx : dirtyExclusiveInv n s
  swmr : permSwmrInv n s
  ...
```

Adding a field to a structure does NOT break existing field accesses. This
eliminates the positional destructuring breakage that was the #1 time sink.

### Hint 5: Frame lemmas eliminate most preservation cases

~70% of preservation proof cases are "this action doesn't touch the relevant
fields, so the invariant is preserved." Invest in:

1. `#gen_frame_lemmas` for state transformers (already done)
2. A `frame_inv` tactic that closes goals by showing fields unchanged
3. Template preservation proofs that handle all "frame" cases automatically

### Hint 6: Trace the dirty data lifecycle explicitly

For any protocol with dirty/exclusive ownership, trace the complete lifecycle:

```
store -> dirty line -> probe -> probeAckData -> writeback to mem ->
  grant (with data) -> clean line at requester
```

At each step, note which invariants hold and which are temporarily violated.
This identifies the "gaps" (like the probe-probeAck gap for dataCoherenceInv)
that need phase-guarded invariants.

### Hint 7: The refinement map should not depend on mutable shared state during transactions

If `refMapShared.mem = s.shared.mem` and `s.shared.mem` changes during a
transaction (e.g., probeAck writeback), the refMap changes too, breaking
stuttering proofs. Instead, use transaction-local values:

```lean
let mem := match currentTxn with
  | some tx => if tx.usedDirtySource then tx.transferVal else s.shared.mem
  | none => ...
```

This makes the refMap invariant across mid-transaction state changes.

### Hint 8: Action-independent proof structure

Every preservation theorem follows the same pattern:

```lean
simp only [SymSharedSpec.toSpec, tlMessages] at hnext
obtain ⟨i, a, hstep⟩ := hnext
match a with
| .action1 => ...
| .action2 => ...
```

An `action_cases` macro would save ~5 lines per theorem x ~15 theorems x
~8 invariants = 600 lines of boilerplate.

### Hint 9: The "vacuous during transaction" pattern

Many invariants are only meaningful when `currentTxn = none`. During
transactions, they should be vacuously true. Adding `currentTxn = none ->`
as a guard is the cleanest way to achieve this. Actions that have
`currentTxn = some` (recvProbe, recvProbeAck, sendGrant, recvGrant)
then get their preservation cases closed by `exact absurd hcur htxn'`.

### Hint 10: Unique-owner arguments use SWMR + lineWF

The pattern "node j is dirty, therefore j is the unique T-holder, therefore
all others have perm .N" recurs throughout the proof. The chain:

1. `dirty j` -> `perm j = .T` (from lineWF: dirty implies T and valid)
2. `perm j = .T` -> `forall k != j, perm k = .N` (from permSwmrInv)

Having `permSwmrInv` as a first-class invariant (not derived from fullInv)
was essential. Derive it early and use it everywhere.

## Metrics

- **Total lines**: ~10,000 across Messages/ directory
- **Invariants**: 12 (fullInv components + refinement-specific)
- **Actions**: 13 (12 protocol + store)
- **Preservation theorems**: ~15 (one per invariant that needs separate proof)
- **Simulation theorems**: 13 (one per action in forwardSim_step)
- **Helper lemmas**: ~40 (probe mask equivalence, snapshot reasoning, etc.)

## Recommended Tooling Before Next Stage

1. **Structure-based invariants**: Refactor `refinementInv`/`forwardSimInv` to
   use Lean structures instead of flat conjunctions.

2. **`action_cases` tactic**: Macro that expands `action_cases hnext` into the
   standard `simp + obtain + match` boilerplate.

3. **`frame_inv` tactic**: Given a list of frame lemmas, automatically close
   preservation goals where the action doesn't touch the invariant's fields.

4. **Invariant design template**: A markdown template for designing invariants
   before writing proofs, with sections for: lifecycle trace, phase analysis,
   guard requirements, preservation sketch.
