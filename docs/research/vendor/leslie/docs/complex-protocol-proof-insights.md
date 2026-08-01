# Insights for Proving Complex Protocols in Leslie

Distilled from the TileLink cache coherence verification effort (April 2026),
covering safety proofs, refinement, and the beginning of liveness work across
~10,000 lines of Lean in `Leslie/Examples/CacheCoherence/TileLink/Messages/`.

## 1. Invariant Design Is the Bottleneck

**~60% of total effort was spent on invariant restructuring** — changing
definitions, fixing cascading breakage, reverting when changes made things
worse. The proof _reasoning_ is often straightforward; the engineering cost
of managing invariant definitions dominates.

### Use structures, never flat conjunctions

```lean
-- BAD: adding a conjunct breaks all ⟨h1, h2, h3⟩ patterns
def inv := A ∧ B ∧ C

-- GOOD: adding a field only requires updating uses of the new field
structure Inv (s : State) : Prop where
  a : A s
  b : B s
  c : C s
```

This was the single highest-impact lesson. Every time a `∧`-based invariant
was modified, 5+ files broke via positional `rcases` patterns.

### Design invariants before writing proofs

For each protocol feature:
1. List all state transitions involving the feature
2. Trace data flow through the complete lifecycle
3. Identify which invariants are temporarily violated during transactions
4. Design with the right guards from the start

A 30-minute design session saves days of trial-and-error.

### Categorize invariants by stability

| Category | Guard | Example | Preservation |
|----------|-------|---------|-------------|
| Stable unconditional | none | SWMR, dirty exclusivity | Must hold across ALL actions |
| Phase-guarded | `currentTxn = none →` | data coherence | Vacuously true during transactions |
| Transient | phase-specific | `grantReady → transferVal = mem` | Only relevant in one phase |

The "vacuous during transaction" pattern (`currentTxn = none →`) is extremely
useful: actions that have `currentTxn = some` get their preservation cases
closed by `exact absurd hcur htxn'`.

## 2. Change Strategies: Strengthen Before Weakening

When a proof needs a fact that isn't available:

1. **First choice: strengthen action guards.** Add the needed fact as a
   guard/precondition to the action predicate. Existing proofs absorb extra
   conjuncts via wildcards in `rcases`. Least disruptive.

2. **Second choice: add a conjunct to an existing invariant.** Strengthening
   an invariant (more conjuncts, same guards) makes it harder to violate but
   easier to use. Safe because it never invalidates existing uses.

3. **Last resort: weaken an invariant (add guards).** This makes the invariant
   easier to preserve but harder to use, and cascades to all call sites.

### Avoid incremental guard additions

Adding `currentTxn = none`, then `releaseInFlight = false`, then
`∀ j, releaseInFlight j = false` over multiple sessions causes triple cascading
repairs. Batch guard additions: design them all upfront and apply once.

## 3. Frame Lemmas Eliminate Most Proof Obligations

~70% of preservation cases follow the pattern "this action doesn't touch the
relevant fields, so the invariant is preserved." The proof infrastructure
should make these trivial:

- **`#gen_frame_lemmas`** for every `*Local` state transformer helper
- Frame lemma + `simp` closes the goal immediately for non-interfering actions
- For a protocol with 13 actions and 12 invariants, ~60% of the 156 cases
  are pure frame

### Hierarchical decomposition

Organize step proofs in tiers:

| Tier | Purpose | Typical content |
|------|---------|-----------------|
| Tier 1 | Per-action, per-invariant | Individual `sorry`-closing lemmas |
| Tier 2 | Per-invariant grouping | Combines tier 1 lemmas with `match a` |
| Tier 3 | Per-action grouping | Transposes to per-action view if needed |
| StepProof | Top level | Final assembly `∀ actions, inv preserved` |

This prevents any single file from exceeding ~2000 lines and allows parallel
work on independent actions or invariants.

## 4. Refinement Proof Pitfalls

### The refinement map must be stable during transactions

If `refMapShared.mem = s.shared.mem` and `s.shared.mem` changes mid-transaction
(e.g., probeAck writeback), the refMap changes too, breaking stuttering proofs.
Use transaction-local values:

```lean
let mem := match currentTxn with
  | some tx => if tx.usedDirtySource then tx.transferVal else s.shared.mem
  | none => s.shared.mem
```

### The unique-owner argument chain

Recurs in almost every non-trivial case:
1. `dirty j` → `perm j = .T` (from lineWF)
2. `perm j = .T` → `∀ k ≠ j, perm k = .N` (from permSwmrInv)

Establish `permSwmrInv` as a first-class invariant early. Don't derive it
from `fullInv` each time — the derivation adds noise to every proof.

## 5. Liveness Proof Architecture

### WF1 is the workhorse

The `wf1` rule proves `p ↝ q` given:
- **Safety**: `p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q`
- **Progress**: `p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q`
- **Enablement**: `p ⇒ Enabled a ∨ q`
- **Fairness**: `□⟨next⟩ ∧ WF(a)`

For each phase transition in the protocol, you need a separate WF1 application.
The per-step leads-to lemmas then compose via `leads_to_trans`.

### Phase chain structure

A liveness proof is a chain of `↝` links:

```
acquirePending ↝ txnActive ↝ grantReady ↝ grantPendingAck ↝ txnDone
```

Each link is one WF1 application. The most complex link
(`probing ↝ grantReady`) requires well-founded induction on the number of
remaining probes — this is where WF1 alone may not suffice and lattice
rules or ranked predicates become necessary.

### Liveness needs auxiliary invariants beyond safety

TileLink liveness required `pendingSinkInv` and `pendingSinkTxnInv` — neither
was part of the safety proof. Each requires its own inductive proof over all
protocol actions. Budget for this: liveness proofs typically discover 2-5
new auxiliary invariants.

## 6. Engineering Practices

### Parallel agents for independent files

When proof obligations are in different files (e.g., StepRelease vs
SimAcquire vs SimOther), they can be worked on in parallel. Structure the
proof directory to maximize independence.

### Keep files under 2000 lines

Large files (the 72K Steps.lean) become unwieldy. Split by:
- Per-invariant files for step proofs
- Per-action files for simulation proofs
- Separate auxiliary invariant files for liveness

### Test locally before changing shared definitions

Before modifying a shared invariant definition, check:
1. How many files import it? (`grep -r "invariantName"`)
2. How many `rcases` patterns destructure it?
3. Can you add what you need as a new field in a structure instead?

### The sorry trajectory matters

Track `sorry` counts across sessions. The trajectory reveals whether you're
making progress or digging deeper:
- Monotonically decreasing: good, systematic closure
- Oscillating: invariant definition is unstable, step back and redesign
- Increasing after a change: revert immediately, don't cascade

## 7. Protocol-Specific Patterns

### Cache coherence protocols

- SWMR (Single Writer / Multiple Reader) is the backbone invariant
- Dirty exclusivity follows from SWMR + lineWF
- Probe mask equivalence (`writableProbeMask = singleProbeMask j`) follows
  from SWMR when j is the unique T-holder
- Data coherence is phase-guarded: only meaningful at quiescent states

### Message-passing protocols

- Channel invariants (serialization: at most one message per channel) are
  critical for enablement proofs in liveness
- "Channel empty → action disabled" closes many WF1 enablement cases
- Message consumption is the natural unit for WF1 steps

### Refinement protocols

- Stuttering is the common case: most concrete steps don't change abstract state
- Linearization points are the interesting cases: identify them early
- The refinement map should be cheap to compute and stable across stuttering steps
