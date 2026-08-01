# Zero-One Rule for Round-Based Threshold Protocols

## The problem

The cutoff theorem in `Cutoff.lean` works with **finite value domains**
(`Fin k`). But many protocols, including OneThirdRule, use **unbounded
values** (`Nat`). The concrete `OneThirdRule.lean` proves agreement for
`Nat` values directly. The `OneThirdRuleCutoff.lean` proves the lock
invariant on binary configurations (`Fin 2` values, `Config 4 n`).

These are two independent proofs of the same safety property. To
formally derive the concrete result FROM the cutoff result — making
the cutoff the engine of the proof — we need a **zero-one rule**: a
reduction from the unbounded-value protocol to the binary-value
configuration.

## What the zero-one rule says

> To prove that the lock invariant holds for all executions of the
> OneThirdRule with arbitrary `Nat` values, it suffices to prove it
> for executions with only values 0 and 1.

## Why it's true

The OneThirdRule is **value-oblivious**: the update function doesn't
inspect actual values — it only counts how many copies of each value
it received. If 47 processes hold value 17 and 3 hold value 42, the
protocol behaves identically to 47 holding 0 and 3 holding 1.

More precisely: in any reachable state, at most one value can have
a super-majority (>2n/3 holders), by pigeonhole. The protocol's
behavior is determined by the partition:
- Processes holding the dominant value (if any)
- Processes holding non-dominant values

This is a binary partition. Relabeling the dominant value as 0 and
all others as 1 preserves the protocol's counting behavior, threshold
comparisons, and decision logic.

## When it's needed

The zero-one rule is NOT needed if:
- You prove safety directly on the concrete protocol (as we did in
  `OneThirdRule.lean` — the lock invariant proof works for `Nat` values
  and general n without the cutoff).

The zero-one rule IS needed if:
- You want the cutoff to be the primary proof engine — verify at the
  binary configuration level for small n, then lift to the concrete
  protocol with `Nat` values at all n.
- The direct proof is too complex and you rely on model checking.

## Formal structure

### The binary projection

Given a concrete round state with `Nat` values, project to a binary
configuration (`Config 4 n`) by:
1. Identify the "dominant value" (the value with the most holders,
   or an arbitrary choice if no super-majority exists).
2. Map each process: if it holds the dominant value, encode as
   `Fin 2 = 0`; otherwise, encode as `Fin 2 = 1`.
3. Track the decided/undecided status for the extended encoding.

```lean
def binaryProjection (s : RoundState (Fin n) LState) : Config 4 n :=
  let dominant := findDominantValue s  -- the value with most holders
  RoundState.toConfig (fun ls =>
    if ls.val = dominant then
      if ls.decided.isSome then 1  -- (val=0, decided) in Fin 4
      else 0                        -- (val=0, undecided)
    else
      if ls.decided.isSome then 3  -- (val=1, decided)
      else 2) s                     -- (val=1, undecided)
```

### The simulation theorem

The binary projection commutes with the round step: if the concrete
protocol takes a step, the projected configuration takes a
corresponding step (or stutters if the dominant value doesn't change).

```lean
theorem zero_one_simulation :
    ∀ s ho s', round_step (otr_alg n) ho s s' →
    extSucc n (binaryProjection s) = binaryProjection s' ∨
    binaryProjection s = binaryProjection s'
```

The key insight: the concrete protocol's threshold check ("does value
v have >2n/3 received copies?") corresponds exactly to the binary
configuration's threshold check ("does Fin 2 = 0 have >2n/3 holders?")
after projection, because the projection maps the dominant value to 0
and preserves counts.

### The transfer theorem

Once the simulation is established, safety transfers:

```lean
theorem agreement_transfer :
    (∀ n c, extLockInv n c → extLockInv n (extSucc n c)) →
    pred_implies (otr_spec n).toSpec.safety [tlafml| □ ⌜agreement n⌝]
```

This chains:
1. The lock invariant holds on all binary configurations (by cutoff or
   direct proof in `OneThirdRuleCutoff.lean`).
2. The binary projection is a simulation of the concrete protocol.
3. Therefore the lock invariant holds on all concrete states (via
   the simulation and projection).
4. The lock invariant implies agreement (by pigeonhole).

## Generalization

The zero-one rule generalizes to other value-oblivious threshold
protocols. The conditions are:

1. **Value-obliviousness**: the update function depends on received
   values only through their counts (multiset), not through
   arithmetic operations or comparisons on the values themselves.

2. **Threshold-based decisions**: decisions depend on whether counts
   cross a threshold, not on exact counts.

3. **Binary safety property**: the safety property is about at most
   two "groups" of processes (e.g., decided-v vs. decided-w).

Under these conditions, any execution with m distinct values can be
projected to a binary execution (dominant vs. non-dominant) without
affecting the safety argument. The value domain collapses from
arbitrary to {0, 1}.

For protocols that ARE value-sensitive (e.g., FloodMin which takes
the minimum, or protocols with value ordering), the zero-one rule
does not apply directly. A different reduction or a larger finite
value domain may be needed.

## Relationship to the literature

The zero-one rule is analogous to results in:

- **Emerson & Namjoshi (1995)**: symmetry reduction for model checking
  symmetric concurrent systems. Process symmetry allows quotienting
  by permutation groups.

- **German & Sistla (1992)**: cutoff results for cache coherence
  protocols, where the "data independence" property (similar to
  value-obliviousness) allows reducing the data domain.

- **Lazic (2000)**: data independence and finite-state abstractions
  for protocols with unbounded data. The key insight: if the protocol
  treats data values as "tokens" (never inspects their content beyond
  equality), the data domain can be collapsed.

- **Dragoi, Henzinger, Veith (2014)**: communication-closed layers
  with cutoffs for threshold-guarded protocols. Their framework is
  closest to ours and implicitly uses data independence.

The formal zero-one rule in Leslie would make this reduction explicit
and mechanically verified, rather than relying on informal arguments
about "relabeling."

## Implementation plan

### Phase 1: Define the binary projection

- Define `findDominantValue` (the value with the most holders)
- Define `binaryProjection : RoundState → Config 4 n`
- Handle the edge case: no dominant value (all below threshold)

### Phase 2: Prove the simulation

- Show that the concrete OTR round step on projected states matches
  `extSucc` on the projected configuration
- Handle the subtlety: the dominant value may change across rounds
  (but only from "none" to "some v" — once established, the dominant
  value is locked by the super-majority)

### Phase 3: Prove the transfer

- Chain simulation + cutoff lock invariant → concrete agreement
- This is the payoff: the concrete safety property follows from
  the binary configuration verification

### Phase 4: Generalize

- Extract the zero-one rule as a reusable theorem for value-oblivious
  threshold protocols
- State conditions (value-obliviousness, threshold-based) formally
- Apply to other protocols (BallotLeader, etc.)

## Files

- `Leslie/ZeroOne.lean` (future) — the formal zero-one rule
- `Leslie/Examples/OneThirdRuleTransfer.lean` (future) — application
  connecting OneThirdRuleCutoff to the concrete OneThirdRule
- `docs/zero-one-rule.md` — this document
