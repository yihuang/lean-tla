# Leslie: TLA in Lean 4

> TLA+ is considered to be exhaustively-testable pseudocode, and its use likened
> to drawing blueprints for software systems; _TLA_ is an acronym for Temporal
> Logic of Actions.
>
> (from [TLA+ - Wikipedia](https://en.wikipedia.org/wiki/TLA%2B))

Leslie is a shallow embedding of the Temporal Logic of Actions (TLA) in Lean 4.
It provides a framework for specifying and verifying concurrent and distributed
systems with machine-checked proofs.

The library includes:

- **Refinement mappings** (Abadi-Lamport) with stuttering and invariants
- **Multi-action specifications** (`ActionSpec`) with gated atomic actions
- **CIVL-style layered refinement** with mover types and Lipton reduction
- **Round-based distributed algorithms** using the Heard-Of (HO) model,
  with proof rules for round invariants, process-local invariants, and
  round refinement
- **Cutoff theorems** for symmetric threshold protocols, reducing
  parameterized verification (all n) to finite model checking (n ≤ K)
- **Random simulation** for testing invariants before formal verification

## Building

Requires [elan](https://github.com/leanprover/elan) with Lean 4 v4.27.0.

```
lake build
```

## Usage

Add this project into your `lakefile.lean` and then:

```lean
import Leslie
```

See [MANUAL.md](MANUAL.md) for a complete user guide covering specifications,
invariants, refinement, and layered verification.

See [docs/round-based-tutorial.md](docs/round-based-tutorial.md) for a tutorial
on round-based algorithms, the Heard-Of model, and cutoff reasoning.

## Project Structure

```
Leslie/
├── Basic.lean              Core TLA definitions, syntax, and operators
├── Refinement.lean         Spec structure and refinement mapping theorems
├── Action.lean             GatedAction, ActionSpec (multi-action specs)
├── Layers.lean             CIVL-style layers, mover types, Lipton reduction
├── Round.lean              Round-based algorithms (HO model), proof rules
├── Cutoff.lean             Cutoff theorems for symmetric threshold protocols
├── Simulate.lean           Random trace simulation for testing
├── Rust/
│   ├── CoreSemantics.lean  Lean-side semantics for the Rust protocol core
│   └── RuntimeSemantics.lean Lean-side semantics for the Rust runtime contract
├── Rules/
│   ├── Basic.lean          Core TLA rules (always, eventually, until, etc.)
│   ├── StatePred.lean      State predicate rules, init_invariant
│   ├── LeadsTo.lean        Leads-to reasoning (transitivity, consequence)
│   ├── BigOp.lean          Big conjunction/disjunction operators
│   └── WF.lean             Weak fairness (WF1 rule)
├── Tactics/
│   ├── Basic.lean          tla_unfold, tla_merge_always, etc.
│   ├── Modality.lean       Modal operator tactics
│   ├── Structural.lean     tla_intros
│   └── StateFinite.lean    simp_finite_exec_goal
├── Gadgets/
│   ├── TheoremLifting.lean #tla_lift command
│   └── TheoremDeriving.lean @[tla_derive] attribute
├── Examples/
│   ├── CounterRefinement.lean      Simple refinement with stuttering
│   ├── TwoPhaseCommit.lean         2PC with refinement proof
│   ├── TicketLock.lean             Layered refinement + mover proofs
│   ├── KVStore.lean                Key-value store, 3 safety properties
│   ├── Paxos.lean                  Single-decree Paxos (14 actions)
│   ├── LeaderBroadcast.lean        Round-based leader broadcast
│   ├── FloodMin.lean               Flood-min consensus with refinement
│   ├── BallotLeader.lean           Leader election (general n, pigeonhole)
│   ├── OneThirdRule.lean           OTR consensus (agreement + validity)
│   ├── OneThirdRuleCutoff.lean     OTR via cutoff (config-level lock inv)
│   └── VRViewChange.lean           VR view change safety
├── rust/
│   ├── Cargo.toml                  Rust crate for communication, protocol, and driver code
│   └── src/
│       ├── comm.rs                 Round-based communication abstractions
│       ├── protocol.rs             Pure protocol trait
│       └── driver.rs               Runs a protocol over a communication object
└── docs/
    ├── round-based-tutorial.md     Tutorial: HO model and cutoff reasoning
    ├── mc-tactic-plan.md           Plan: model-checking tactic
    ├── zero-one-rule.md            Plan: value domain reduction
    ├── communication-contract.md   Runtime contract for tag-based inbox collection
    ├── rust-verification-v2.md     Revised Rust verification architecture
    └── rust-verification-plan-v2.md Revised implementation plan
```

## Examples at a Glance

### Interleaving protocols (ActionSpec)

| Example | What it demonstrates | Status |
|---------|---------------------|--------|
| CounterRefinement | Basic refinement with stuttering | Complete |
| TwoPhaseCommit | Refinement with invariant (10 actions) | Complete |
| TicketLock | Layered refinement, mover types | Complete |
| KVStore | Key-value store, 3 safety properties | Complete |
| Paxos | Quorum intersection, 14 actions | Spec complete, 2 sorry |

### Round-based protocols (HO model)

| Example | What it demonstrates | Status |
|---------|---------------------|--------|
| LeaderBroadcast | Leader-follower agreement (2 processes) | Complete |
| FloodMin | Flood-min consensus + refinement to consensus spec | Complete |
| BallotLeader | Leader election for general n (majority pigeonhole) | Complete |
| OneThirdRule | Agreement (lock invariant) + validity, general n | Complete |
| OneThirdRuleCutoff | Lock invariant via cutoff, reliable + unreliable comm | Complete |
| VRViewChange | Viewstamped Replication view change safety | 1 sorry |

### Key results

- **Agreement for OneThirdRule** (`OneThirdRule.lean`): Fully machine-checked
  proof that the OneThirdRule consensus algorithm satisfies agreement for
  any number of processes n, under the 2/3-communication predicate. The proof
  uses a lock invariant (super-majorities persist once established) and
  pigeonhole (two super-majorities can't coexist). Also proves validity:
  any decided value was an initial value.

- **Cutoff theorem** (`Cutoff.lean`): For symmetric threshold protocols with
  communication closure, safety at all n reduces to checking n ≤ K where
  K = ⌈k·α_den/(α_den−α_num)⌉+1. Fully proved including the scaling lemma,
  partition sum, and weighted partition sum.

- **Unreliable communication** (`OneThirdRuleCutoff.lean`): The lock invariant
  is preserved under any valid nondeterministic successor constrained by the
  HO communication predicate — not just the deterministic reliable case.

## Documentation

- [MANUAL.md](MANUAL.md) — Complete user manual: specifications, proofs,
  refinement, CIVL layers, tactic reference
- [docs/round-based-tutorial.md](docs/round-based-tutorial.md) — Tutorial on
  the Heard-Of model, communication closure, and cutoff reasoning
- [docs/mc-tactic-plan.md](docs/mc-tactic-plan.md) — Design for a
  model-checking tactic using `native_decide`
- [docs/zero-one-rule.md](docs/zero-one-rule.md) — Design for reducing
  unbounded value domains to binary

## Thanks

Leslie is ported from the ['Lentil'](https://github.com/verse-lab/Lentil)
implementation, which came out of the
[`coq-tla`](https://github.com/tchajed/coq-tla) library.
