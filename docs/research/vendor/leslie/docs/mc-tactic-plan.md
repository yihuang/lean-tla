# Plan: Model-Checking Tactic for Round-Based Protocols

## Goal

Build a Lean tactic `mc_verify K` that automatically discharges the
"small-n verification" step in cutoff-based proofs. Given:

- A symmetric threshold protocol (extended state, update function)
- A configuration-level invariant
- A cutoff bound K

The tactic verifies that the invariant is inductive for all
configurations at n ≤ K, producing a kernel-trusted proof.

## Background

The cutoff theorem (`Cutoff.lean:cutoff_reliable`) reduces "invariant
holds for all n" to "invariant holds for all n ≤ K." The small-n step
is a finite check — there are at most C(n+k-1, k-1) configurations
of n processes among k states. For OneThirdRule (k=4, K=7), that's
about 500 configurations total. For more complex protocols (k=8, K=13),
it could be millions.

## Approach: `native_decide` with decidable encoding

### Architecture

```
User writes:                    Tactic generates:

  theorem step_small :          1. Bool-valued checker
    ∀ n ≤ K, ∀ c,              2. Equivalence proof (Bool ↔ Prop)
    inv c → inv (succ c)        3. native_decide on the Bool checker
      := by mc_verify K
```

### Step 1: Decidable encoding

Define a `Bool`-valued function that checks the inductive step
on raw `Nat` tuples, avoiding the dependent `Config` type:

```lean
/-- Check the inductive step for a single raw configuration. -/
def checkStep (k n : Nat) (inv : (Fin k → Nat) → Bool)
    (succ : (Fin k → Nat) → (Fin k → Nat))
    (counts : Fin k → Nat) : Bool :=
  if ((List.finRange k).map counts).sum != n then true  -- invalid config, skip
  else if !inv counts then true                          -- antecedent false, skip
  else inv (succ counts)                                 -- check preservation

/-- Check all configurations at a given n. -/
def checkAllAtN (k n : Nat) (inv : (Fin k → Nat) → Bool)
    (succ : (Fin k → Nat) → (Fin k → Nat)) : Bool :=
  -- Enumerate all (c₀, ..., c_{k-1}) with each cᵢ ≤ n
  -- Filter to those with sum = n
  -- Check each with checkStep
  ...

/-- Check all n ≤ K. -/
def checkAllUpToK (k K : Nat) (...) : Bool :=
  (List.range (K + 1)).all (checkAllAtN k · ...)
```

### Step 2: Equivalence proof

Prove that `checkAllUpToK = true` implies the `Prop`-valued statement:

```lean
theorem checkAllUpToK_correct :
    checkAllUpToK k K inv succ = true →
    ∀ n ≤ K, ∀ c : Config k n, invProp n c → invProp n (succConfig c)
```

This is boilerplate: unfold the `Bool` checker, connect raw tuples
to `Config` via the `sum_eq` constraint, connect the `Bool` invariant
to the `Prop` invariant.

### Step 3: Apply `native_decide`

```lean
theorem step_small : ∀ n ≤ K, ... := by
  apply checkAllUpToK_correct
  native_decide  -- evaluates the Bool checker to true
```

### The tactic

The `mc_verify` tactic automates steps 1-3:

```lean
elab "mc_verify" K:num : tactic => do
  -- 1. Extract the invariant and successor from the goal
  -- 2. Generate the Bool-valued checker definitions
  -- 3. Generate the equivalence proof
  -- 4. Apply native_decide
  ...
```

## Enumeration strategy

For k states and n processes, the valid configurations are solutions
to c₀ + c₁ + ... + c_{k-1} = n with cᵢ ≥ 0. The number of solutions
is C(n+k-1, k-1) (stars and bars).

For the OneThirdRule cutoff:
- k = 4 (extended states), K = 7
- Configs per n: C(n+3, 3). Total for n ≤ 7: sum C(i+3,3) for i=0..7
  = 1 + 4 + 10 + 20 + 35 + 56 + 84 + 120 = 330
- Very fast for `native_decide`.

For larger protocols:
- k = 6, K = 13: up to C(18, 5) = 8568 per n, ~60K total. Still fast.
- k = 8, K = 20: up to C(27, 7) = 888030 per n. May need optimization.

### Optimization: threshold-view pruning

The invariant and successor depend only on the **threshold view**
(which groups of states exceed the threshold). For k_val = 2 binary
values, there are only 3 realizable threshold views: (F,F), (T,F),
(F,T). So instead of checking all 330 configs, we check 3 threshold
view cases. Each case constrains the configs to a specific region
(e.g., value-0 count > 2n/3), and within that region the successor
is uniform (all → decidedState v).

This reduces the check to O(1) regardless of K. The tactic could:
1. Enumerate the 2^k_val realizable threshold views
2. For each view, verify the invariant step symbolically
3. Combine into a proof for all configs

This is essentially what the direct proof in `lock_inv_step` does.
The tactic would automate the case analysis.

## Alternative: External model checker

For protocols where `native_decide` is too slow:

### TLC (TLA+ model checker)

1. Generate a TLA+ spec from the `SymThreshAlg` and invariant
2. Run TLC externally
3. If TLC finds no counterexample, add a trusted axiom

**Pros:** Handles millions of states efficiently.
**Cons:** Not kernel-trusted. Requires Lean → TLA+ translation.

### Integration sketch

```lean
-- Lean side: generate TLA+ spec
#eval generateTLASpec otrExtAlg extLockInv 7

-- Run TLC externally (user does this)
-- $ tlc OneThirdRule.tla -config check.cfg

-- Import result as axiom
axiom tlc_verified : checkAllUpToK 4 7 ... = true

-- Use in proof
theorem step_small : ... := checkAllUpToK_correct tlc_verified
```

The axiom `tlc_verified` is the trust boundary. Everything else
(the cutoff theorem, the equivalence proof, the final agreement
theorem) is kernel-checked.

## Implementation plan

### Phase 1: Bool encoding (estimated: 1 session)

- Define `checkStep`, `checkAllAtN`, `checkAllUpToK` in a new file
  `Leslie/MCVerify.lean`
- Prove `checkAllUpToK_correct`
- Demonstrate on OneThirdRule with `native_decide`

### Phase 2: Tactic wrapper (estimated: 1 session)

- Write the `mc_verify` tactic that extracts the goal structure
  and applies the encoding + `native_decide` automatically
- Test on OneThirdRule and BallotLeader

### Phase 3: Threshold-view optimization (estimated: 1 session)

- Add pruning by threshold view (enumerate views, not configs)
- This makes the check O(2^k_val) instead of O(C(n+k-1,k-1))
- Essential for larger protocols

### Phase 4: External model checker integration (future)

- TLA+ spec generation from `SymThreshAlg`
- TLC runner integration
- Trust management (axiom vs kernel-checked)

## Files

- `Leslie/MCVerify.lean` — Bool encoding, equivalence proof, tactic
- `Leslie/Examples/OneThirdRuleMC.lean` — demonstration on OneThirdRule
- `docs/mc-tactic-plan.md` — this document
