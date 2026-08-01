# Leslie User Manual

This guide covers how to write specifications, prove invariants, and establish
refinement using Leslie. It assumes familiarity with TLA+ or TLA concepts and
basic Lean 4 proficiency.

---

## Table of Contents

1. [Core Concepts](#1-core-concepts)
2. [Writing a Specification](#2-writing-a-specification)
3. [Random Simulation](#3-random-simulation)
4. [Proving Invariants](#4-proving-invariants)
5. [Refinement](#5-refinement)
6. [Layered Refinement (CIVL)](#6-layered-refinement-civl)
7. [TLA Formula Syntax](#7-tla-formula-syntax)
8. [Proof Tactics Reference](#8-proof-tactics-reference)
9. [Theorem Reference](#9-theorem-reference)
10. [Proof Patterns Cookbook](#10-proof-patterns-cookbook)

### Round-Based Algorithms and Cutoff Reasoning

For a tutorial on modeling and verifying round-based distributed algorithms
using the Heard-Of model, communication closure, and cutoff theorems, see:

**[Round-Based Algorithms Tutorial](docs/round-based-tutorial.md)**

This tutorial covers:
- The Heard-Of model and why communication closure simplifies verification
- How to specify round-based algorithms (`RoundAlg`, `RoundSpec`)
- Proving safety via lock invariants and pigeonhole arguments
- The cutoff theorem: reducing verification for all n to finite model checking
- A worked example with the OneThirdRule consensus algorithm

Related design documents:
- [Model-Checking Tactic Plan](docs/mc-tactic-plan.md) — automating the
  small-n verification step via `native_decide`
- [Zero-One Rule](docs/zero-one-rule.md) — reducing unbounded value domains
  to binary for value-oblivious threshold protocols

---

## 1. Core Concepts

Leslie uses a **shallow embedding** of TLA in Lean 4. The fundamental types are:

| Type | Definition | Meaning |
|------|-----------|---------|
| `exec σ` | `Nat → σ` | Infinite execution (sequence of states) |
| `pred σ` | `exec σ → Prop` | TLA formula (predicate over executions) |
| `action σ` | `σ → σ → Prop` | Two-state relation (transition) |

A **state predicate** `f : σ → Prop` is lifted to a TLA predicate via
`state_pred f`, which checks `f` on the first state of an execution.

An **action predicate** `a : action σ` is lifted via `action_pred a`, which
checks `a` on the first two states.

### Temporal Operators

| Operator | Notation | Definition |
|----------|----------|------------|
| Always | `□ p` | `∀ k, p (e.drop k)` |
| Eventually | `◇ p` | `∃ k, p (e.drop k)` |
| Next | `◯ p` | `p (e.drop 1)` |
| Until | `p 𝑈 q` | Standard until |
| Leads-to | `p ↝ q` | `□(p → ◇q)` |
| Weak fairness | `𝒲ℱ a` | `□(□ Enabled a → ◇ ⟨a⟩)` |

### Judgment Forms

| Notation | Meaning |
|----------|---------|
| `\|‑tla‑ p` | `p` is valid (holds for all executions) |
| `p \|‑tla‑ q` | `p` implies `q` (for all executions) |
| `e \|=tla= p` | Execution `e` satisfies `p` |

---

## 2. Writing a Specification

The recommended way to write a specification is using `ActionSpec`, which
separates a protocol into named actions with explicit gates (preconditions).

### Step 1: Define State and Action Types

```lean
import Leslie.Action

open TLA
namespace MyProtocol

-- State type: use a structure with all protocol state
structure MyState where
  counter : Nat
  flag : Bool

-- Action index: enumerate all actions
inductive MyAction where
  | increment | reset
```

### Step 2: Define the ActionSpec

```lean
def mySpec : ActionSpec MyState MyAction where
  init := fun s => s.counter = 0 ∧ s.flag = false
  actions := fun
    | .increment => {
        gate := fun s => s.flag = false        -- precondition
        transition := fun s s' =>              -- effect
          s' = { s with counter := s.counter + 1 }
      }
    | .reset => {
        gate := fun s => s.counter > 0
        transition := fun s s' =>
          s' = { counter := 0, flag := true }
      }
```

### Key Design Patterns

**Deterministic transitions**: Use `s' = { s with field := value }` for
updates that modify specific fields. The `{ s with ... }` notation preserves
all fields not explicitly listed.

**Non-deterministic transitions**: Use existentials:
```lean
transition := fun s s' => ∃ v, s' = { s with value := v }
```

**Constrained non-determinism** (e.g., Paxos phase-2a):
```lean
transition := fun s s' => ∃ v, s' = { s with prop := some v } ∧
  (∀ w, someCondition s w → v = w)
```

**Boolean message flags**: For message-passing protocols, model messages as
Boolean flags (`sent : Bool`) rather than message sets. This avoids `Finset`
reasoning and is sufficient for fixed-size instances.

**Fixed instances**: Use concrete enumerations (e.g., `ThreadId` with `t1 | t2`)
rather than parameterizing over `N`. This makes proofs tractable via case
analysis.

### Step 3: Convert to a Spec

`ActionSpec` converts to a `Spec` automatically:

```lean
-- These are available:
mySpec.toSpec         -- Spec with next = ∃ i, (actions i).fires s s'
mySpec.toSpec.safety  -- ⌜init⌝ ∧ □⟨next⟩
mySpec.toSpec.safety_stutter  -- ⌜init⌝ ∧ □⟨next ∨ id⟩
```

---

## 3. Random Simulation

Before investing in formal proofs, you can test your protocol with random
simulation. The simulator performs random walks through the state space,
checking an invariant at every step, and reports a counterexample trace if a
violation is found.

### Overview

`ActionSpec` definitions use `Prop`-valued predicates (gates, transitions),
which are not directly executable. To simulate, you provide a `Simulable`
instance — an executable mirror of your `ActionSpec` with `Bool`-valued gates
and concrete transition functions.

```
import Leslie.Simulate
```

### Step 1: Define a Simulable Instance

The `Simulable` typeclass has four fields, each mirroring a component of
`ActionSpec`:

| `Simulable` field | Mirrors | Type |
|--------------------|---------|------|
| `init` | `ActionSpec.init` | `IO σ` — generate a concrete initial state |
| `actions` | enumeration of `ι` | `List ι` — all action indices |
| `enabled` | `GatedAction.gate` | `ι → σ → Bool` — executable gate check |
| `step` | `GatedAction.transition` | `ι → σ → IO σ` — executable transition |

The `step` field uses `IO` so that nondeterministic transitions (e.g., choosing
a value to write) can make random choices via `IO.rand`.

```lean
-- Derive Repr for state/action types so traces can be printed
deriving instance Repr for MyState
deriving instance Repr for MyAction

instance : TLA.Sim.Simulable MyState MyAction where
  init := pure { counter := 0, flag := false }
  actions := [.increment, .reset]
  enabled := fun act s => match act with
    | .increment => s.flag == false
    | .reset     => s.counter > 0
  step := fun act s => pure (match act with
    | .increment => { s with counter := s.counter + 1 }
    | .reset     => { counter := 0, flag := true })
```

For **nondeterministic transitions**, use `IO.rand` inside `step`:

```lean
  step := fun act s => match act with
    | .writeOk r => do
      -- Choose a random value (mirrors ∃ v, s' = { s with ... })
      let v ← if (← IO.rand 0 1) == 0 then pure Value.v0 else pure Value.v1
      pure { s with journal := s.journal ++ [v], ... }
    | ...
```

### Step 2: Define Executable Invariants

Write your invariant as a `Bool`-valued function:

```lean
def myInv (s : MyState) : Bool :=
  s.counter ≤ 10
```

This should be the executable version of the `Prop`-valued invariant you
intend to verify later.

### Step 3: Run the Simulator

```lean
-- Check invariant across 1000 random traces of up to 100 steps each
#eval TLA.Sim.simulate (ι := MyAction) myInv
  { numTraces := 1000, maxSteps := 100 }
```

On success:
```
OK: 1000 traces × ≤100 steps, 0 deadlocks, avg length 101
```

On violation, the full counterexample trace is printed:
```
VIOLATION in trace 42 at step 7!
Counterexample:
  init
    → { counter := 0, flag := false }
  MyAction.increment
    → { counter := 1, flag := false }
  ...
```

### Simulator API Reference

| Function | Signature | Purpose |
|----------|-----------|---------|
| `simulate` | `[Simulable σ ι] [Repr σ] [Repr ι] → (σ → Bool) → Config → IO Bool` | Run traces, print results, return `true` if no violation |
| `randomWalk` | `[Simulable σ ι] [Repr σ] [Repr ι] → Nat → IO Unit` | Print a single random trace (for protocol exploration) |
| `quickCheck` | `[Simulable σ ι] → (σ → Bool) → Nat → Nat → IO Bool` | Silent check, returns `Bool` only |
| `runTrace` | `[Simulable σ ι] → Config → (σ → Bool) → IO (TraceOutcome σ ι)` | Single trace returning structured result |

The `Config` structure has two fields:

| Field | Default | Meaning |
|-------|---------|---------|
| `maxSteps` | 10000 | Maximum steps per trace |
| `numTraces` | 100 | Number of random traces |

### Exploring Protocol Behavior

Use `randomWalk` to generate a single trace and see how the protocol evolves:

```lean
#eval TLA.Sim.randomWalk (σ := MyState) (ι := MyAction) (steps := 20)
```

This prints each action and resulting state, which is useful for understanding
the protocol before writing invariants. If the protocol reaches a state with
no enabled actions, it reports a deadlock.

### Recommended Workflow

1. **Write the `ActionSpec`** — define your state, actions, and spec.
2. **Write a `Simulable` instance** — mirror gates and transitions as
   executable code. Keep this right next to the spec so they stay in sync.
3. **Explore with `randomWalk`** — sanity-check that the protocol behaves
   as expected.
4. **Test invariants with `simulate`** — run thousands of traces to build
   confidence before attempting proofs.
5. **Prove the invariant formally** — use `init_invariant` and the patterns
   in sections below.

If simulation finds a bug, fix the spec and re-run. This fast feedback loop
avoids spending time on proofs for broken protocols.

### Tips

- **Deadlocks**: If many traces deadlock, your protocol may have liveness
  issues (states with no enabled actions). Inspect the trace with `randomWalk`
  to understand why.
- **Coverage**: Random simulation cannot replace verification — it may miss
  rare corner cases. But it catches most common bugs quickly.
- **Nondeterminism**: For protocols with existential transitions, the `step`
  function picks one random successor. Run many traces to cover different
  choices.
- **Performance**: The simulator runs in `IO` and is quite fast. 10,000 traces
  of 10,000 steps each (100M total steps) typically completes in seconds.
- **Separate files**: Put `#eval` statements in a separate `*Sim.lean` file
  (not imported from the root `Leslie.lean`) so simulation doesn't run during
  every `lake build`. See `Leslie/Examples/TwoPhaseCommitSim.lean` for an
  example.

---

## 4. Proving Invariants

An invariant is a state predicate that holds at every reachable state.

### The init_invariant Theorem

The primary tool for proving invariants:

```lean
theorem init_invariant :
  (∀ s, init s → inv s) →                         -- inv holds initially
  (∀ s s', next s s' → inv s → inv s') →          -- inv is preserved
  pred_implies spec.safety [tlafml| □ ⌜ inv ⌝]    -- inv holds always
```

### Standard Proof Pattern

```lean
def my_inv (s : MyState) : Prop :=
  s.counter ≤ 10

theorem my_inv_holds :
    pred_implies mySpec.toSpec.safety [tlafml| □ ⌜ my_inv ⌝] := by
  apply init_invariant
  · -- Base case: init → inv
    intro s ⟨hcounter, hflag⟩
    simp [my_inv, hcounter]
  · -- Inductive step: next ∧ inv → inv'
    intro s s' ⟨i, hfire⟩ hinv
    cases i <;> simp [mySpec, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans <;>
      simp [my_inv] at * <;> omega
```

### Proof Strategy for the Inductive Step

1. **Destructure the action**: `⟨i, hfire⟩` gives you the action index and
   firing proof.
2. **Case split on actions**: `cases i` splits into one goal per action.
3. **Unfold and simplify**: `simp [specName, GatedAction.fires] at hfire`
   exposes the gate and transition.
4. **Extract gate + transition**: `obtain ⟨hgate, htrans⟩ := hfire`
5. **Substitute the transition**: `subst htrans` replaces `s'` with the
   concrete struct update.
6. **Close the goal**: Usually `simp_all`, `omega`, or manual case analysis.

For existential transitions (e.g., `∃ v, s.prop = some v ∧ s' = ...`):
```lean
obtain ⟨hgate, v, hprop, htrans⟩ := hfire
subst htrans
```

---

## 5. Refinement

Refinement proves that a concrete system implements an abstract specification:
every behavior of the concrete system, when mapped through a state function,
is a behavior of the abstract system.

### Refinement Mapping (No Invariant)

```lean
-- Define the abstraction function
def abs_map (s : ConcreteState) : AbstractState := ...

-- Prove refinement
theorem my_refinement :
    refines_via abs_map concrete.toSpec.safety abstract.toSpec.safety_stutter := by
  apply refinement_mapping_stutter concrete.toSpec abstract.toSpec abs_map
  · -- Init: concrete init → abstract init
    intro s hinit ; ...
  · -- Step: concrete step → abstract step or stutter
    intro s s' ⟨i, hfire⟩
    cases i <;> ...
    · left ; exact ⟨abstractAction, gateProof, transitionProof⟩   -- real step
    · right ; simp [abs_map]                                       -- stutter
```

### Refinement with Invariant

When the abstraction function only works under an invariant of the concrete
system:

```lean
theorem my_refinement :
    refines_via abs_map concrete.toSpec.safety abstract.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    concrete.toSpec abstract.toSpec abs_map my_inv
  · -- inv_init: init → inv
  · -- inv_next: inv ∧ step → inv'
  · -- init_preserved: init → abstract.init (abs_map s)
  · -- step_sim: inv ∧ step → abstract step or stutter
```

### Available Refinement Theorems

| Theorem | Use Case |
|---------|----------|
| `refinement_mapping_nostutter` | Every step maps to an abstract step (no stutter) |
| `refinement_mapping_stutter` | Steps may stutter (map to identity) |
| `refinement_mapping_with_invariant` | No stutter, but need an invariant |
| `refinement_mapping_stutter_with_invariant` | Stutter + invariant (most common) |
| `refinement_mapping_stutter_stutter` | Both specs allow stutter |
| `refines_via_trans` | Compose two refinements: `(f : σ→τ, g : τ→υ) → (g∘f : σ→υ)` |

### Step Simulation Patterns

For each concrete action, you show either:

**Abstract step** (left disjunct):
```lean
left
exact ⟨abstractActionIndex, gateProof, transitionProof⟩
```

**Stutter** (right disjunct — abstract state doesn't change):
```lean
right
simp [abs_map]   -- or: rfl, or manual proof that abs_map s = abs_map s'
```

---

## 6. Layered Refinement (CIVL)

Leslie supports CIVL-style layered verification with mover types and Lipton
reduction.

### Mover Types

```lean
inductive MoverType where
  | right    -- commutes to the right of concurrent actions
  | left     -- commutes to the left
  | both     -- commutes both ways
  | nonmover -- does not commute
```

### Commutativity Conditions

**Right-commutativity**: `a` then `b` can be reordered to `b` then `a`:
```lean
def right_commutes (a b : GatedAction σ) : Prop :=
  ∀ s s₁ s₂, a.fires s s₁ → b.fires s₁ s₂ →
    ∃ s₁', b.fires s s₁' ∧ a.fires s₁' s₂
```

**Left-commutativity**: `b` then `a` can be reordered to `a` then `b`:
```lean
def left_commutes (a b : GatedAction σ) : Prop :=
  ∀ s s₁ s₂, b.fires s s₁ → a.fires s₁ s₂ →
    ∃ s₁', a.fires s s₁' ∧ b.fires s₁' s₂
```

### Proving Commutativity

The typical pattern: destructure both firings, construct the witness state.

```lean
theorem rc_action1_action2 :
    right_commutes (spec.actions .action1) (spec.actions .action2) := by
  intro s s₁ s₂ ⟨hga, htrans_a⟩ ⟨hgb, htrans_b⟩
  subst htrans_a htrans_b
  -- Construct the intermediate state (b fires first, then a)
  exact ⟨{ s with field2 := newVal },
    ⟨hgb, rfl⟩,                    -- b fires from s
    ⟨hga, by ext <;> simp⟩⟩        -- a fires from intermediate
```

**Vacuous commutativity** (contradictory gates — the two actions can never
fire in sequence):
```lean
theorem lc_leave1_enter2 :
    left_commutes (spec.actions .leave1) (spec.actions .enter2) := by
  intro s s₁ s₂ ⟨⟨_, _⟩, hs₁⟩ ⟨hga, _⟩
  subst hs₁ ; simp [specName] at hga   -- derives False from contradictory gates
```

### Per-Thread Mover Validity

Actions only need to commute with actions of **other** threads:

```lean
def Layer.movers_valid_threaded [DecidableEq θ]
    (l : Layer σ ι) (thread : ι → θ) : Prop :=
  ∀ i j, thread i ≠ thread j →
    ((l.mover i).isRight = true → right_commutes (l.spec.actions i) (l.spec.actions j)) ∧
    ((l.mover i).isLeft = true → left_commutes (l.spec.actions i) (l.spec.actions j))
```

### Lipton Reduction

The library provides proved reduction theorems:

| Theorem | What it does |
|---------|-------------|
| `right_movers_swap` | Sequence of right-movers swaps past one env step |
| `left_movers_absorb` | Sequence of left-movers absorbs preceding env step |
| `fragment_right_reduction` | Push env step before R\*;rest |
| `fragment_left_reduction` | Push env step after prefix;L\* |
| `lipton_reduction_right` | In R\*;N;L\*, push env after R\* to before fragment |
| `lipton_reduction_left` | In R\*;N;L\*, push env before L\* to after fragment |

### Non-deterministic Layers

Deterministic fetch-and-increment does **not** commute (swapping two acquires
gives different ticket values). The standard CIVL approach: introduce a layer
with non-deterministic allocation, prove it commutes, then show the
deterministic version refines it. See `TicketLock.lean` for this pattern.

---

## 7. TLA Formula Syntax

Leslie provides a `tlafml` syntax category for readable formulas:

```lean
-- State predicates
[tlafml| ⌜ fun s => s.x > 0 ⌝]          -- state_pred
[tlafml| ⌜ myPredicate ⌝]

-- Action predicates
[tlafml| ⟨ fun s s' => s'.x = s.x + 1 ⟩] -- action_pred
[tlafml| ⟨ myAction ⟩]

-- Pure (non-temporal) propositions
[tlafml| ⌞ True ⌟]                        -- pure_pred

-- Temporal operators
[tlafml| □ p]                              -- always
[tlafml| ◇ p]                              -- eventually
[tlafml| ◯ p]                              -- next/later
[tlafml| p 𝑈 q]                           -- until
[tlafml| p ↝ q]                           -- leads-to
[tlafml| p ⇒ q]                           -- always-implies
[tlafml| 𝒲ℱ a]                            -- weak fairness

-- Logical connectives
[tlafml| p ∧ q]     [tlafml| p ∨ q]
[tlafml| ¬ p]       [tlafml| p → q]
[tlafml| ∀ x, p x]  [tlafml| ∃ x, p x]

-- Big operators
[tlafml| ⋀ x ∈ l, f x]                   -- big conjunction
[tlafml| ⋁ x ∈ l, f x]                   -- big disjunction
```

---

## 8. Proof Tactics Reference

### TLA-Specific Tactics

| Tactic | Purpose |
|--------|---------|
| `tla_unfold` | Unfold core TLA definitions (`always`, `eventually`, `state_pred`, `action_pred`, etc.) |
| `tla_unfold'` | Like `tla_unfold` plus execution simplifications (`exec.drop`, `exec.map`) |
| `tla_unfold_simp` | Full unfold + `simp` |
| `tla_nontemporal_simp` | Simplify non-temporal parts, leaving temporal structure intact |
| `tla_intros` | Move hypothesis from right of `\|‑tla‑` to left (via `impl_intro`) |
| `tla_merge_always t1, t2, ... => h` | Merge multiple `□ p₁`, `□ p₂`, ... into `□(p₁ ∧ p₂ ∧ ...)` named `h` |
| `simp_finite_exec_goal` | Generalize `e k` and `e (k+1)` to fresh variables when the goal is finite-state |

### Standard Lean Tactics Used Frequently

| Tactic | When to use |
|--------|-------------|
| `cases i` | Split on action index (one goal per action) |
| `simp [specName, GatedAction.fires] at hfire` | Unfold the spec definition to expose gate + transition |
| `obtain ⟨hgate, htrans⟩ := hfire` | Destructure firing into gate and transition |
| `subst htrans` | Substitute `s' = { s with ... }` into the goal |
| `simp_all` | Aggressive simplification using all hypotheses |
| `ext <;> simp` | Prove struct equality by extensionality |
| `omega` | Solve linear arithmetic over `Nat`/`Int` |
| `decide` | Solve decidable propositions (no free variables) |
| `by_cases h : condition` | Case split on a Boolean/decidable condition |
| `rcases h with ⟨a, b⟩ \| ⟨c, d⟩` | Recursive case split on disjunctions/existentials |
| `nofun` | Close impossible goals (e.g., `none = some _`) |

### Simp Attributes

| Attribute | Collected lemmas for |
|-----------|---------------------|
| `@[tlasimp_def]` | TLA definition unfolding |
| `@[execsimp]` | Execution operations (`drop`, `map`) |
| `@[tla_nontemporal_def]` | Non-temporal simplification |
| `@[tlasimp]` | General TLA simplification |

---

## 9. Theorem Reference

### Invariants

```
init_invariant
  (hinit : ∀ s, init s → inv s)
  (hstep : ∀ s s', next s s' → inv s → inv s')
  : pred_implies (⌜init⌝ ∧ □⟨next⟩) (□⌜inv⌝)
```

### Always (□)

| Theorem | Statement |
|---------|-----------|
| `always_intro` | `valid p ↔ valid (□ p)` |
| `always_weaken` | `□ p \|‑tla‑ p` |
| `always_monotone` | `(p \|‑tla‑ q) → (□ p \|‑tla‑ □ q)` |
| `always_and` | `□(p ∧ q) ⟺ □p ∧ □q` |
| `always_idem` | `□□p ⟺ □p` |
| `always_forall` | `□(∀x. p x) ⟺ ∀x. □(p x)` |
| `always_unroll` | `□p ⟺ p ∧ ◯□p` |
| `always_induction` | `□p ⟺ p ∧ □(p → ◯p)` |

### Eventually (◇)

| Theorem | Statement |
|---------|-----------|
| `eventually_idem` | `◇◇p ⟺ ◇p` |
| `eventually_monotone` | `(p \|‑tla‑ q) → (◇p \|‑tla‑ ◇q)` |
| `not_always` | `¬□p ⟺ ◇¬p` |
| `not_eventually` | `¬◇p ⟺ □¬p` |
| `always_eventually_always` | `□◇□p ⟺ ◇□p` |
| `eventually_always_eventually` | `◇□◇p ⟺ □◇p` |

### Leads-To (↝)

| Theorem | Statement |
|---------|-----------|
| `leads_to_trans` | `(p ↝ q) ∧ (q ↝ r) \|‑tla‑ (p ↝ r)` |
| `leads_to_conseq` | Weaken lhs, strengthen rhs |
| `leads_to_combine` | Combine two leads-to with invariant |
| `leads_to_strengthen_lhs` | `□inv → (p ∧ inv ↝ q) \|‑tla‑ (p ↝ q)` |

### Weak Fairness

```
wf1 : (p ∧ ⟨next⟩ ⇒ ◯(p∨q))        -- next preserves p or achieves q
     ∧ (p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q)      -- action a achieves q
     ∧ (p ⇒ Enabled a ∨ q)           -- p implies a is enabled (or q)
     ∧ (□⟨next⟩ ∧ 𝒲ℱ a)
     ⊢ (p ↝ q)
```

### Refinement

| Theorem | Signature |
|---------|-----------|
| `refinement_mapping_nostutter` | `(init→init') → (step→step') → refines_via` |
| `refinement_mapping_stutter` | `(init→init') → (step→step'∨stutter) → refines_via` |
| `refinement_mapping_with_invariant` | `inv_init → inv_step → init' → step' → refines_via` |
| `refinement_mapping_stutter_with_invariant` | Above + stuttering (most common) |
| `refines_via_trans` | `refines_via f p q → refines_via g q r → refines_via (g∘f) p r` |
| `safety_implies_safety_stutter` | `spec.safety \|‑tla‑ spec.safety_stutter` |

### Layer Refinement

| Theorem | Signature |
|---------|-----------|
| `LayerRefinement.to_refines_via` | Layer refinement → spec refinement |
| `LayerRefinementInv.to_refines_via` | With invariant |
| `LayerRefinement.compose` | Chain two layer refinements |
| `LayerRefinement.compose3` | Chain three layer refinements |

### Lipton Reduction

| Theorem | Signature |
|---------|-----------|
| `right_movers_swap` | `seq_run rs s s₁ → env s₁ s₂ → ∃ s₁', env s s₁' ∧ seq_run rs s₁' s₂` |
| `left_movers_absorb` | `env s s₁ → seq_run ls s₁ s₂ → ∃ s₁', seq_run ls s s₁' ∧ env s₁' s₂` |

---

## 10. Proof Patterns Cookbook

### Pattern: Invariant for an ActionSpec

```lean
theorem my_invariant :
    pred_implies mySpec.toSpec.safety [tlafml| □ ⌜ inv ⌝] := by
  apply init_invariant
  · intro s ⟨h1, h2, ...⟩         -- destructure init
    simp [inv, *]                   -- or: constructor <;> intro <;> simp_all
  · intro s s' ⟨i, hfire⟩ hinv     -- i : action index, hfire : fires
    cases i <;>                     -- one goal per action
      simp [mySpec, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;>
      subst htrans <;>
      simp [inv] at * <;>
      simp_all
```

### Pattern: Refinement with Stutter and Invariant

```lean
theorem refines :
    refines_via abs concrete.toSpec.safety abstract.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    concrete.toSpec abstract.toSpec abs inv
  · intro s hinit ; ...                      -- inv_init
  · intro s s' hinv ⟨i, hfire⟩ ; ...        -- inv_next
  · intro s hinit ; ...                      -- init_preserved
  · intro s s' hinv ⟨i, hfire⟩              -- step_simulation
    cases i <;> simp [concrete, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans
    · right ; simp [abs]                     -- stutter case
    · left ; exact ⟨.someAction, gate, trans⟩ -- real step
```

### Pattern: Right-Commute Proof (Independent Fields)

When two actions modify independent struct fields:

```lean
theorem rc_a_b : right_commutes (spec.actions .a) (spec.actions .b) := by
  intro s s₁ s₂ ⟨hga, htrans_a⟩ ⟨hgb, htrans_b⟩
  subst htrans_a htrans_b
  exact ⟨{ s with fieldB := newB },
    ⟨hgb, rfl⟩,
    ⟨hga, by ext <;> simp⟩⟩
```

### Pattern: Right-Commute with Existential Transitions

```lean
theorem rc_acquire_other :
    right_commutes (spec.actions .acquire1) (spec.actions .acquire2) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨hgb, t₂, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with ticket2 := some t₂ },
    ⟨hgb, t₂, rfl⟩,
    ⟨hga, t₁, by ext <;> simp⟩⟩
```

### Pattern: Vacuous Commutativity

When the two actions can never fire consecutively (contradictory gates):

```lean
theorem lc_leave_enter :
    left_commutes (spec.actions .leave1) (spec.actions .enter2) := by
  intro s s₁ s₂ ⟨⟨_, _⟩, hs₁⟩ ⟨hga, _⟩
  subst hs₁
  simp [specName] at hga    -- gate becomes contradictory after subst
```

### Pattern: Combined Mover Validity (Per-Thread)

```lean
theorem movers_valid : layer.movers_valid_threaded threadAssign := by
  intro i j hij ; constructor
  · intro hr                           -- right-mover case
    cases i <;> cases j <;>
      simp [movers, MoverType.isRight, layer] at hr <;>
      simp [threadAssign] at hij       -- filter same-thread pairs
    · exact rc_lemma1
    · exact rc_lemma2
    ...
  · intro hl                           -- left-mover case
    cases i <;> cases j <;>
      simp [movers, MoverType.isLeft, layer] at hl <;>
      simp [threadAssign] at hij
    · exact lc_lemma1
    ...
```

### Pattern: Handling `by_cases` on Majority

When a phase-2b action might create a quorum:

```lean
by_cases hmaj : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
· -- majority already existed → stutter (abstract state unchanged)
  right ; simp [paxos_ref, hmaj, ...]
· -- no majority yet
  by_cases hmaj' : majority3 true s.did2b_1_2 s.did2b_1_3 = true
  · -- new majority just formed → abstract choose action
    left ; exact ⟨.choose, gateProof, transProof⟩
  · -- still no majority → stutter
    right ; simp [paxos_ref, majority3, ...] at *
```

### Tips

- Add `@[ext]` to structures you need extensionality on (for `ext <;> simp`).
- Use `set_option maxHeartbeats N` if proofs time out (default 200000).
- `simp [specName]` unfolds the spec; add it when gate predicates aren't reducing.
- After `subst`, struct field access is already reduced — don't add redundant `simp`.
- `List.mem_cons_self` takes no explicit arguments in Lean 4 v4.27.
- For `decide` to work, the goal must have no free variables.
- Use `nofun` to close goals like `some x = none → ...` or `False → ...`.

---

## Appendix: Adding a New Example

1. Create `Leslie/Examples/MyExample.lean` with `import Leslie.Action` (or
   `import Leslie.Layers` if using layers).

2. Define your types, specs, and invariants inside a `namespace`.

3. Add `import «Leslie».Examples.MyExample` to `Leslie.lean`.

4. Run `lake build` to verify everything type-checks.

5. Follow the recommended workflow:
   - Define the `ActionSpec` and a `Simulable` instance.
   - Create a separate `Leslie/Examples/MyExampleSim.lean` with `#eval`
     statements to run the simulator (do **not** import this from `Leslie.lean`).
   - Explore with `randomWalk`, then test invariants with `simulate`.
   - Once simulation passes, prove the invariant formally.
   - Use `sorry` for hard proof obligations and fill them in incrementally.
