# M0.2 — Parallel composition state model

**Status.** Decision settled; minimal Lean shape verified.
**Owner.** TBD.
**Budget.** ~3 days planned; ~0.5 day actual.
**Blocked by.** M0.1 (resolved). **Blocks.** UC-style composition in M4.

---

## The question

What is the state type of `Π₁ ∥ Π₂` when the two protocols share a
network?

Design plan v2 said:

```
parallel : ProbActionSpec σ₁ ι₁ → ProbActionSpec σ₂ ι₂
         → ProbActionSpec (σ₁ × σ₂) (ι₁ ⊕ ι₂)
```

Round-2 finding 3 flagged this as fundamentally unable to model
distributed protocols, which communicate via shared message
buffers. UC composition substitutes ideal functionalities into
hybrid worlds and rewires shared interfaces — a disjoint-state
product cannot represent either.

## Decision

**State is `σ₁ × σ_net × σ₂` with the network as its own
`ProbActionSpec`.** Party actions guard on local state plus the
network; network actions guard only on the network. The composition
is action-set disjoint union (`ι₁ ⊕ ι_net ⊕ ι₂`), but the state
overlap on `σ_net` is genuine.

Concretely:

```lean
-- Sketch for M1 W1+ (ProbActionSpec is defined there).
def parallelWithNet
    (Π₁  : ProbActionSpec σ₁    ι₁)
    (Net : ProbActionSpec σ_net ι_net)
    (Π₂  : ProbActionSpec σ₂    ι₂)
    -- Each party's actions are lifted to read+write the full state.
    -- The lifters specify how each side's local action footprint
    -- includes optional network updates (sends).
    (lift₁ : ι₁    → ι₁    × (σ₁    × σ_net → σ₁    × σ_net))
    (lift_net : ι_net → ι_net × (σ_net → σ_net))
    (lift₂ : ι₂    → ι₂    × (σ₂    × σ_net → σ₂    × σ_net)) :
    ProbActionSpec (σ₁ × σ_net × σ₂) (ι₁ ⊕ ι_net ⊕ ι₂)
```

This is the *shared-state product*: the cross product of the three
specs, where actions of each component are lifted to read and
write the relevant slice of the global state.

## Why a separate `Net` argument (not in-line with `Π_i`)

Three reasons:

1. **Network model is reusable.** `Net` for AVSS, common coin, and
   async BA is the same asynchronous mailbox. Pulling it out lets
   each higher-level protocol be parameterized over the network
   model rather than rebuilding delivery/drop semantics from
   scratch.
2. **Adversary scheduling is per-action.** The demonic scheduler
   chooses an action `i ∈ ι₁ ⊕ ι_net ⊕ ι₂` per step. Network
   actions (deliver, drop, reorder, duplicate) are scheduled
   alongside party actions. This matches Hirt-Maurer async UC
   semantics, where the adversary controls delivery.
3. **Fairness is per-action-set.** `FairAdversary` (design plan
   v2.1 §"Adversary, scheduler, fairness") has `fair_actions :
   Set ι` — for a composed system, fairness can target party
   actions alone (synchronous-network model) or delivery actions
   alone (eventual-delivery model) or both. The disjoint union
   makes this addressable.

## What `Net` looks like for the M3 protocols

For Bracha RBC, AVSS, common coin, async BA, the canonical network
shape is asynchronous, eventually-fair, point-to-point:

```lean
-- σ_net for asynchronous reliable broadcast / Byzantine networks
structure AsyncNet (n : ℕ) (Msg : Type) where
  /-- Multiset of in-flight messages from sender to receiver. -/
  inflight : Fin n → Fin n → Multiset Msg

-- ι_net for AsyncNet
inductive AsyncNetAction (n : ℕ) (Msg : Type)
  | deliver (sender receiver : Fin n) (m : Msg) : AsyncNetAction n Msg
  -- (no drop / reorder / duplicate for the basic eventually-fair model;
  --  add as additional constructors if a stronger adversary is needed)
```

Network step semantics (sketch): `deliver i j m` is enabled when
`m ∈ inflight i j`, and removes one copy of `m` from `inflight i j`
while producing a message-arrival side effect on the receiver's
state. The adversary chooses delivery order; fairness on
`{deliver _ _ _}` ensures eventual delivery.

This shape is what Bracha RBC, AVSS, etc., all share. Designing
`AsyncNet` once and using it across protocols is the M2 W1 effort.

## Why not "shared variables a la Owicki-Gries"

A purely-shared-variable model (Owicki-Gries / IOA / TLA+) flattens
state to one big record and makes every action's footprint
explicit. This is *more* general than the shared-network model
above, but:

- It loses the guarantee that party actions only touch their own
  local state plus the network. UC composition relies on this
  separation: when substituting an ideal functionality `F` for a
  protocol `Π_F`, the surrounding protocol's actions don't touch
  `F`'s internal state.
- It complicates the adversary model: the adversary now needs to
  understand which variables belong to which party for corruption
  semantics.

The shared-network model bakes in the right separation. It is also
exactly what Hirt-Maurer async UC uses.

## What's still flexible

- **Synchronous-round protocols** (which Leslie's existing `Round`
  module handles) don't need a separate network — rounds are
  abstract message exchanges. The shared-network model doesn't
  apply to those; randomized synchronous protocols (M6, optional)
  would use a different composition shape.
- **Synchronous-but-message-passing** protocols (e.g.,
  Feldman/Pedersen synchronous VSS) might want a constrained
  `AsyncNet` where delivery is forced after each round. This is
  also expressible as an `AsyncNet` variant with stronger fairness;
  doesn't change the type signature.
- **Adversarial delivery models** (drop, reorder, duplicate) are
  added by extending `AsyncNetAction` with more constructors. The
  composition shape is unchanged.

## Type-shape sanity check (Lean)

The minimal Lean stub at `Leslie/Prob/Spike/ParallelShape.lean`
declares the shape without depending on `ProbActionSpec` (which is
M1 W1 work). It establishes that the `σ₁ × σ_net × σ₂`
disjoint-action-union pattern is expressible in Lean 4 with the
ergonomic `Sum`-coproduct for actions.

The stub builds green; the tiny "two parties exchange one message"
sanity example fits in ~30 lines. Nothing in the shape requires
Mathlib (it's pure data); the Mathlib dependency in M0 spike comes
from the trace-measure work (M0.1, M0.3), not from M0.2.

## Implications for the wider plan

- **Design plan v2.1 §"`ProbActionSpec` and trace distributions"**
  needs a new subsection on parallel composition with the
  shared-network shape (replacing the v2 disjoint-state version).
  Defer to v2.2 sweep alongside M0.1's trace-measure signature
  changes.
- **Implementation plan v2.1 §M2 W1** (Adversary, Trace, properly)
  should reference `parallelWithNet` directly, not the disjoint
  product.
- **M4 UC composition** sequence is unaffected: `compose_uc` still
  takes a `Realizes` proof and a hybrid-model proof; what changes
  is what the `parallel` arrow inside `Realizes` means. The
  shared-network shape is more permissive, so existing combinator
  signatures work without restructuring.
- **`AsyncNet`** is reusable across Bracha RBC, AVSS, common coin,
  async BA. Defining it once in `Leslie/Prob/Network.lean`
  (~100 lines) is M2 W1 work, not M0.

## Outstanding for M2 W1

1. Promote the shape sketch in this document to `Leslie/Prob/Action.lean`
   alongside `ProbActionSpec`, with the actual `parallelWithNet`
   definition (probably ~50 lines).
2. Define `AsyncNet n Msg` and `AsyncNetAction n Msg` in
   `Leslie/Prob/Network.lean` with delivery semantics and an
   eventual-delivery fairness predicate.
3. Verify `parallelWithNet Π₁ AsyncNet Π₂` produces the right
   `traceDist` shape against M0.1's `Kernel.trajMeasure` setup.
4. The "two parties exchange one message" sanity example becomes a
   non-trivial litmus test once `ProbActionSpec` and `traceDist`
   exist.

## Open questions for M3+

- **Multi-network composition.** What about `Π₁ ∥ Net₁ ∥ Π₂` and
  `Π_outer = Π_full ∥ Net₂ ∥ Π_other`? The shape extends naturally
  (state is `σ_full × σ_net₂ × σ_other`), but action labels become
  unwieldy. Likely answer: nest. M4-time decision.
- **Per-party network views.** In Byzantine settings, corrupt
  parties may see network state honest parties don't (e.g.,
  drop-when-no-honest-recipient). The shape above doesn't
  distinguish; layering corrupt-view filtering on top of `AsyncNet`
  is M2 W3+ work.

## References

- Hirt-Maurer, "Player Simulation and General Adversary Structures
  in Perfect Multiparty Computation" — the canonical async-UC
  reference for adversarial delivery.
- Lynch & Tuttle, "An Introduction to Input/Output Automata" —
  shared-state composition foundations.
- Leslie/Prob/Spike/ParallelShape.lean — minimal Lean stub
  validating the type-level shape.
