# Cutoff Theorems in Leslie

A reference for Leslie's cutoff infrastructure as it stands today: what's
proved, what turned out to be vacuous and was removed, what's on hold, and
what's actively being built.

**Status: 2026-04-15.** Substantially revised after PRs #19 and #20. The
earlier version of this document described a planned "bounded-unrolling
cutoff" for OTR and majority-rule, and a `CutoffIntegration` combinator
framework with per-protocol bounds for Raft / Multi-Paxos / VR / PBFT /
HotStuff / ThresholdConsensus / FastPaxos. Both turned out to be hollow
(see §8) and have been removed from mainline. The real cutoff content now
lives in three places: `Leslie/Cutoff.lean` (safety, mathematically sound
but also contains the termination cutoff for liveness), and
`Leslie/Examples/Combinators/PhaseCounting.lean` +
`Leslie/Examples/Paxos/Bounded*Proposer.lean` (Paxos bounded unrolling
via monotone phase counter).

---

## 1. Background and motivation

Distributed protocol verification in Leslie is parameterized by `n`, the
number of processes. A safety theorem has the shape

> For every `n : ℕ` and every reachable state of the `n`-process instance,
> the invariant holds.

This is a universal statement over an infinite family of transition systems.
A **cutoff theorem** reduces it to a finite collection of small instances:

> For every `n`, the `n`-process instance satisfies the invariant
>     iff
> every instance with `n ≤ K` satisfies a corresponding finite invariant.

The finite instances can be discharged by `decide`, `native_decide`, a
model checker, or explicit case analysis.

There are two honest cutoff results in mainline today (§2 symmetric
threshold, §3 termination), one hand-rolled inductive safety proof that
bypasses the generic framework (§4), and one bounded-unrolling framework
with real Paxos instantiations (§5). §6–§8 cover design work that is on
hold or was removed after audit.

---

## 2. Existing cutoff: symmetric threshold protocols

**Location:** `Leslie/Cutoff.lean`.

### 2.1 The target protocol class

A **symmetric threshold protocol** in the HO model satisfies:

1. **Finite state domain.** Each process holds one of `k` values
   (`Fin k`). There is no other per-process state.
2. **Communication closure.** Messages sent in round `r` are either
   delivered in round `r` or lost forever — no stale messages from previous
   rounds interfere with current counts.
3. **Role symmetry.** All processes run the same deterministic update
   function; there is no "leader" role distinguished from "follower".
4. **Threshold decision.** A process updates its value based purely on the
   *count* of each value among received messages. The decision depends only
   on whether each count is above (or below) a fixed fraction `α_num / α_den`
   of `n`.

Formally this is `SymThreshAlg k α_num α_den`. The step function maps
`(current_counts, received_counts)` to `new_counts` without consulting
individual process identities.

### 2.2 The threshold view abstraction

A `Config k n` — a tuple of `k` counts summing to `n` — is abstracted to
its `ThreshView`, which records, for each value, whether its count is
above the `α_num / α_den` fraction of `n`. Two configurations with the
same `ThreshView` are behaviorally indistinguishable to a symmetric
threshold protocol.

### 2.3 The cutoff bound

```lean
def cutoffBound (k α_num α_den : ℕ) : ℕ :=
  if α_den > α_num then
    k * α_den / (α_den - α_num) + 1
  else
    1
```

For the one-third rule (k=2, α=1/3), the bound is `K = 7`. For any `n ≥ 7`,
if the invariant holds at `n = 7`, it holds at `n`.

### 2.4 The main theorem

```lean
theorem cutoff_reliable
    (alg : SymThreshAlg k α_num α_den)
    (inv : ConfigInv k)
    (h_det : inv.threshDetermined α_num α_den) :
    (∀ n (c : Config k n), inv n c) ↔
    (∀ n ≤ cutoffBound k α_num α_den, ∀ c : Config k n, inv n c)
```

**Direction (→):** trivial, restrict the universal.

**Direction (←):** the substance. Given `n > K`, use `thresh_scaling_down`
to find a smaller `n' ≤ K` with the same `ThreshView`, apply the small-
instance result, lift back via `threshDetermined`.

The proof is sound. The theorem is a real mathematical result. The
limitation is how much of it is usable in practice — see §2.6.

### 2.5 Scope (original framing)

- **Applies in principle:** one-third rule, majority rule, absorbing
  threshold protocols.
- **Does not apply:** Paxos (role asymmetry), Ben-Or (nondeterministic
  coin oracle, invariant not purely threshold-determined), HotStuff
  (ballot-indexed state beyond `k` values), any protocol with per-process
  unbounded state.

### 2.6 The pigeonhole collapse: why `cutoff_reliable` is narrow for safety

**Finding from the PR #19 audit.** `cutoff_reliable` requires
`inv.threshDetermined α_num α_den`, meaning `inv n c` depends only on
`c.threshView α_num α_den : Fin k → Bool`. Under the theorem's hypothesis
`2 · α_num ≥ α_den` (supermajority), the threshView can have at most one
bit set at a time: two counts both above `α_num / α_den · n ≥ n/2` would
sum to more than `n`. So the space of *realizable* threshViews has exactly
`k + 1` patterns — `[false, …, false]` plus one pattern per value.

Any `threshDetermined` invariant of the form "not two values above
threshold" is therefore a **pigeonhole tautology**: it holds at every
`Config k n` regardless of reachability, because the forbidden pattern
`(true, true, …)` is unrealizable. The "reachable" quantifier in the
cutoff statement does zero work. The small-`n` check in `h_all_small`
is discharged by decidability on an empty obligation.

**Concretely, all of the following invariants collapse to tautology:**

- `noTwoSuperMaj` (one-third rule, `k = 2`, `α = 1/3`): proved by
  pigeonhole on `Config 2 n`.
- `noTwoMajorities` (majority rule, `k = 2`, `α = 1/2`): same.
- `tcLockInv` (threshold consensus, `k = 4`, `α = 2/3`): same.
- `lockedConsistent` (any `Fin 4` supermajority invariant): same.

None of these exercises the protocol's dynamics. The cutoff framework is
being used as API surface, not as proof content.

**What escapes the collapse:**

- **Non-threshold state.** Invariants referencing per-process decisions,
  phase counters, or ballot-tagged values cannot be expressed as
  predicates on `ThreshView k`. These fall outside `cutoff_reliable`'s
  domain entirely and must be proved by direct induction (§4) or by a
  different cutoff framework (§5).
- **Liveness.** Termination claims ("decides within `T` rounds") are
  about trace *trajectories*, which are dynamical and don't factor
  through the threshView at a single state. The `TLA.TerminationCutoff`
  namespace in `Leslie/Cutoff.lean` (§3) uses the same
  `thresh_scaling_down` machinery to do real work for termination,
  even though it doesn't for safety.

**Bottom line.** `cutoff_reliable` and `thresh_scaling_down` are correct
and are load-bearing infrastructure for §3 (termination). For safety,
they apply only to invariants that are already Config-level pigeonhole
facts — i.e., invariants that don't need a cutoff to prove. Any
non-trivial safety property of interest (at-most-one-decided-value,
monotone commitment, stable-storage regression freedom) lives outside
the framework and needs a different approach.

---

## 3. Termination cutoff

**Location:** `Leslie/Cutoff.lean` (namespace `TLA.TerminationCutoff`).

This is the one file in mainline where `cutoff_reliable`'s machinery
(`thresh_scaling_down`, `cutoffBound`) does substantive work. Termination
is about trace *trajectories*, not single-state invariants, and traces
don't collapse to pigeonhole even when single-state predicates do.

### 3.1 TV-determinism

A `SymThreshAlg` is **TV-deterministic** if the successor threshold view
depends only on the current threshold view, not on exact counts:

```lean
def tvDeterministic (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ n₁ n₂ (c₁ : Config k n₁) (c₂ : Config k n₂),
    c₁.threshView α_num α_den = c₂.threshView α_num α_den →
    (Config.succ alg c₁).threshView α_num α_den =
    (Config.succ alg c₂).threshView α_num α_den
```

Protocols where above-threshold values are absorbing (OTR, majority rule,
any consensus where decided states don't change) satisfy this. The file
proves OTR TV-deterministic as a concrete instance via `isCollapsing` +
`isIdentityBelowThreshold` sufficient conditions.

### 3.2 The key dynamical lemma

```lean
theorem iterSucc_tv_eq
    (h_det : tvDeterministic alg)
    (n₁ n₂ : Nat) (c₁ : Config k n₁) (c₂ : Config k n₂)
    (h_tv : c₁.threshView α_num α_den = c₂.threshView α_num α_den) :
    ∀ t, (Config.iterSucc alg t c₁).threshView α_num α_den =
         (Config.iterSucc alg t c₂).threshView α_num α_den
```

Proved by induction on `t`. At each step, TV-determinism lets us apply
the IH to the successor configurations, so their threshold views coincide
after any number of steps.

### 3.3 The cutoff

```lean
theorem bounded_termination_cutoff
    (h_det : tvDeterministic alg)
    (decided : TVDecided k)
    (T : Nat)
    (h_small : ∀ n, n ≤ cutoffBound k α_num α_den →
      ∀ c : Config k n, ∃ t, t ≤ T ∧
        decided ((Config.iterSucc alg t c).threshView α_num α_den)) :
    ∀ n (c : Config k n), ∃ t, t ≤ T ∧
      decided ((Config.iterSucc alg t c).threshView α_num α_den)
```

Combines `thresh_scaling_down` (every large-`n` config has a matching
small-`n` config with the same threshView) with `iterSucc_tv_eq` (same
initial TV implies same TV trajectory). If termination-within-`T` is
verified at all `n ≤ K`, it holds at all `n`.

**Why this is not hollow.** The conclusion quantifies over `t ≤ T` and
asserts that a dynamical object (the trace of threshViews) reaches a
decided state. This cannot be proved by pigeonhole at a single `Config k n`
because it involves the iterated step relation, not just state shape.
`thresh_scaling_down` transfers a substantive fact across process counts.

---

## 4. Hand-rolled safety cutoff: `OneThirdRuleCutoff.lean`

**Location:** `Leslie/Examples/OneThirdRuleCutoff.lean`.

This file is the model for how real safety cutoff work looks in Leslie
without going through the `cutoff_reliable` API. It was written before
the pigeonhole-collapse finding, but its approach is the right one: don't
try to express the invariant as a `threshDetermined` predicate; write it
directly with explicit per-process decision state, prove preservation
inductively, and handle lossy communication with a hand-written relational
successor.

### 4.1 Extended state

The file uses `Config 4 n` where `Fin 4` encodes `{val0, val1,
decidedState 0, decidedState 1}` — two "bare value" states and two
"decided" states per value. This embeds per-process decisions into the
symmetric `Config k n` framework.

### 4.2 The invariant

```lean
def extLockInv (n : Nat) (c : Config 4 n) : Prop :=
  ∀ v : Fin 2,
    c.counts (decidedState v) > 0 →
    valCount n c v * 3 > 2 * n
```

"If any process has decided `v`, then `v` has super-majority support."
This is **not** a pigeonhole tautology — a `Config 4 n` with
`decidedState 0 = 1, valCount 0 = 0` trivially violates it. Preservation
requires real induction over the step relation.

### 4.3 Lossy communication

`IsValidUnreliableSucc` is a hand-written relational predicate on
`Config 4 n × Config 4 n` capturing "c' is a legal successor of c under
lossy HO":

```lean
def IsValidUnreliableSucc (n : Nat) (c c' : Config 4 n) : Prop :=
  (∀ v : Fin 2, valCount n c v * 3 > 2 * n → valCount n c' v * 3 > 2 * n) ∧
  (∀ v : Fin 2, c.counts (decidedState v) ≤ c'.counts (decidedState v)) ∧
  (∀ v : Fin 2, ¬(valCount n c v * 3 > 2 * n) →
    c'.counts (decidedState v) = c.counts (decidedState v))
```

Super-majorities are preserved, decisions are monotone, no phantom
decisions. `extSucc_is_valid_unreliable` shows the deterministic
successor satisfies these constraints **under the lock invariant** —
the dependency on the IH is what makes the argument tight.

### 4.4 Agreement

`agreement_via_lock`: if the lock invariant holds and two values are
both decided, they must be equal. The proof is a clean pigeonhole on the
*consequence* of the lock (`h_v + h_w > 4n/3 > n`), not on the invariant
itself.

### 4.5 Why this file matters

It is the **only file in mainline** that proves a non-tautological safety
invariant in the symmetric-threshold setting, with real induction and
with lossy communication handled explicitly. It predates the `cutoff_reliable`
API's limitations and sidesteps them entirely. Any future non-trivial
safety work should follow this shape rather than trying to squeeze
through `ConfigInv k + threshDetermined`.

---

## 5. Bounded unrolling via monotone phase counters (PR #20)

**Location:** `Leslie/Examples/Combinators/PhaseCounting.lean`,
`Leslie/Examples/Paxos/BoundedSingleProposer.lean`,
`Leslie/Examples/Paxos/BoundedPaxos.lean`.

This is a second, structurally different cutoff framework that does not
go through `cutoff_reliable` and does not suffer from the pigeonhole
collapse. The reduction is on trace *depth*, not node count, via a
monotone progress measure built into the protocol state.

### 5.1 The abstract system

```lean
structure PhaseCountingSystem where
  State        : Type
  Action       : Type
  step         : State → State → Action → Prop
  init         : State
  phaseCounter : State → Nat
  bound        : Nat
  init_zero    : phaseCounter init = 0
  step_mono    : ∀ s s' a, step s s' a → phaseCounter s < phaseCounter s'
  step_bounded : ∀ s s' a, step s s' a → phaseCounter s' ≤ bound
```

Three side conditions: counter starts at zero, strictly increases per
step, stays within `bound`. From these the bounded-unrolling equivalence
follows:

> Safety of all reachable states equals safety of all traces of length
> `≤ bound` starting from `init`.

The proof is by induction on the counter. No threshView, no
`threshDetermined`, no `Config k n`. Arbitrary state predicates are
allowed.

### 5.2 Reachability and bounded traces

```lean
inductive Reachable : P.State → Prop
  | init : Reachable P.init
  | step : ∀ {s s'} (a), Reachable s → P.step s s' a → Reachable s'

inductive StepsFrom : P.State → List P.Action → P.State → Prop
  | nil  : ∀ s, StepsFrom s [] s
  | cons : ∀ {s s' s''} (a) (acts),
             P.step s s' a → StepsFrom s' acts s'' →
             StepsFrom s (a :: acts) s''
```

Standard definitions. `StepsFrom.snoc` (right-append) and
`stepsFrom_preserves_reachable` are the main closure lemmas.

### 5.3 Refinement for fault models

The framework also formalizes safety transfer under sub-step relations.
If `step' ⊆ step`, and `step'` is a refinement (typically modeling
message loss or fail-stop crashes), then any safety property that holds
under `step` holds under `step'`:

```lean
theorem safeAll_of_refined
    (P : PhaseCountingSystem)
    (step' : P.State → P.State → P.Action → Prop)
    (h_sub : ∀ s s' a, step' s s' a → P.step s s' a)
    (Safe : P.State → Prop)
    (h : safeAll P Safe) :
    safeAll (refined P step' h_sub) Safe
```

Plus two concrete instantiations:

- `withLossyDelivery P deliverable` — drop messages a `deliverable`
  predicate rules out.
- `withFailStop P canAct` — processes whose `canAct` is false stop
  taking steps.

And the composition `withLossyDelivery_withFailStop_safe`: safety under
the joint fault model follows from safety under atomic actions. The
proofs go through by structural recursion on `Reachable`, not by
induction, because `Reachable` takes `P` as a parameter rather than an
index.

### 5.4 Paxos instantiations

Three Paxos variants, each a concrete `PhaseCountingSystem` with a
computed bound:

| File | Protocol | Phase counter bound |
|---|---|---|
| `BoundedSingleProposer.lean` | single-proposer Paxos-lite (468 lines) | `2·n` |
| `BoundedPaxos.lean` | m-proposer real Paxos wrapping `Leslie/Examples/Paxos.lean` (436 lines) | `2·m·n + m` |

**Note on BoundedPaxos.** This file wraps the existing faithful parameterized
Paxos in `Leslie/Examples/Paxos.lean` (full state with `prom`, `acc`, `got1b`,
`rep`, `prop`, `did2b`; real quorum-gated `p1b` / `p2a` / `p2b` actions;
Lamport's `safeAt` as inductive invariant; `agreement` via quorum
intersection) in a `PhaseCountingSystem`. The safety target
`boundedPaxos_agreement` is derived directly from `PaxosTextbookN.agreement`
via `paxos_inv_next` preservation, with no modification to the underlying
Paxos file.

**Historical note.** Earlier versions of this section also listed
`BoundedTwoProposer.lean` and `BoundedMProposer.lean`. Those files used a
"defer-rule shortcut": a side condition on `propose` forced non-primary
proposers to adopt the primary proposer's value, sidestepping the quorum-based
max-vote argument. This was sound but referenced proposer volatile state in
the safety invariant, which precluded any fault-model extension (message loss,
fail-stop crashes, fail-recover). `BoundedPaxos.lean` replaces both by wrapping
the real, faithful Paxos model — no shortcut — so the phase-counting framework
composes cleanly with the refinement / fault-model machinery in
`PhaseCounting.lean`.

Each counter counts structural slots per role (phase 1b per acceptor,
phase 2b per acceptor, etc.) that can fire at most once. The bounded-
unrolling equivalence then reduces safety verification to checking all
traces up to the counter bound.

**Why this works where `cutoff_reliable` doesn't:** the invariants being
proved (safety, "no two values accepted at the same ballot", etc.)
reference per-process ballot-tagged state. They are not expressible as
`threshDetermined` predicates. But they don't need to be — the monotone
counter argument is orthogonal to threshold views, so the pigeonhole
collapse never enters.

**Zero sorries, builds clean.** See `BoundedPaxos.lean` for the faithful
m-proposer instantiation with `PaxosInv`-based agreement derivation.

---

## 6. Historical: round-based cutoff design (on hold)

An earlier design pursued cutoffs on the **number of rounds** in a
round-based algorithm: given shift-invariance, bounded advance, and
window-local transitions, reduce safety verification to bounded-depth
executions from a finite set of canonical round configurations.

Three feasibility studies (BenOr, OTR, single-decree Paxos) showed that
**no protocol in Leslie's current corpus satisfies the theorem's
non-triviality conditions**:

- All `RoundAlg`-based protocols (BenOr, OTR, LastVoting, FloodMin,
  LeaderBroadcast, BallotLeader, …) have `W = 0` trivially because
  `RoundAlg.update : P → S → (P → Option M) → S` structurally cannot
  access round history. `RoundAlg` already performs round compression
  by construction.
- Single-decree Paxos is shift-invariant under ballot renaming, but its
  ballot dimension is already finite at the model level: at most `m`
  distinct ballot values exist in any reachable state, where `m` is the
  fixed number of proposers. No unbounded round dimension to compress.

**Decision:** the design is preserved in the appendices for reference,
but the theorem is not being formalized. Revisit if Leslie gains a
multi-decree protocol (Multi-Paxos, Raft) where a meaningful unbounded
ballot×slot dimension exists.

The full design — `RoundShift`, `RoundObserver`, `RoundWindow`,
`BoundedAdvance`, `RoundLocal`, `RoundInvariant`, and the target
`round_cutoff` theorem — is reproduced in Appendix E for completeness.

---

## 7. Historical: safety-side bounded unrolling attempt (PR #17, removed)

An earlier version of this document proposed a **safety** bounded-unrolling
cutoff for OTR and majority-rule: via explicit phase observations
(adoption requires super-majority, phase 1 absorbing, phase 2
absorbing-and-monotone), bound the safety diameter at `D ≤ ⌈n/3⌉ - 1`
and verify via bounded-depth simulation from canonical initial
configurations.

**What happened.** The implementation went into PR #15 and its
successor PR #17, adding ~2000 lines of content in `CutoffReasoning/`
(`PhaseAbsorbingThreshold.lean`, `OneThirdRuleBoundedUnrolling.lean`,
`MajorityBoundedUnrolling.lean`, `ConfigRoundBridge.lean`). The same PR
cycle added Phase 1+2+3 scaffolding for a planned "counts-aware cutoff"
(`Config.next`, `ViewAssignment`, `FaithfulVA`, `LockedOTR.lean`) that
would support non-tautological safety invariants.

**Audit finding.** The invariants being proved (`noTwoSuperMaj`,
`noTwoMajorities`, `noTwoAtThreshold`, `lockedConsistent`) were all
pigeonhole tautologies (§2.6). The safety-diameter bounds and the
phase observations were mathematically correct but the *consumers* of
them — the cutoff theorems — did zero work. The counts-aware cutoff
(`Config.next`) reduced to an alias of `cutoff_reliable` with an unused
parameter, and its one non-tautological example (`noTwoLocked_next_of_preLocked`
in `LockedOTR.lean`) was a standalone inductive proof with no
generalization path.

**Outcome.** PR #19 removed the entire exploration from mainline.
Removed content is preserved on branches `archive/cutoff-exploration`
(full state including Phase 1+2+3) and `archive/hollow-combinators`
(intermediate state) for reference.

**Lesson.** The symmetric-threshold framework cannot carry a safety
cutoff. Future safety work should either (a) instantiate a different
framework like `PhaseCounting` (§5), or (b) follow the hand-rolled
`OneThirdRuleCutoff` pattern (§4). The combinator approach with its
`autoCutoff`-generated bounds for Raft/VR/PBFT/HotStuff/etc. was also
in this category and was removed in the same PR.

---

## 8. Relationship summary

| Cutoff kind | Bounds | Class of protocols | Where proved | Status |
|---|---|---|---|---|
| Symmetric threshold (§2) | `n ≤ K_nodes` | SymThreshAlg | `Leslie/Cutoff.lean` | ✅ Sound but narrow; pigeonhole-collapses for safety on small `k` |
| Termination cutoff (§3) | `rounds ≤ T`, transfers across `n` | TV-deterministic SymThreshAlg | `Leslie/Cutoff.lean` (`TLA.TerminationCutoff`) | ✅ Real dynamical work, OTR instantiated |
| Hand-rolled safety (§4) | none (direct induction) | Extended-state SymThreshAlg with per-process decisions | `Examples/OneThirdRuleCutoff.lean` | ✅ The model for non-trivial safety |
| Phase-counting bounded unrolling (§5) | `trace length ≤ bound(m, n)` | Systems with monotone phase counter | `Combinators/PhaseCounting.lean` + `Paxos/Bounded*Proposer.lean` | ✅ 3 Paxos instantiations (PR #20) |
| Round cutoff (§6) | `rounds ≤ n·D + W` | Shift-invariant, window-local | Design preserved, not formalized | 🟡 On hold; no current target protocol |
| Symmetric safety bounded unrolling (§7) | `trace length ≤ D_safety` | Phase-absorbing SymThreshAlg | *removed* | ❌ Pigeonhole-collapsed; PR #19 removed |
| Combinator cutoff (`autoCutoff`) | structural per protocol | SymCPhase composition | *removed* | ❌ Hollow templates; PR #19 removed |

The right mental model: Leslie has **one sound symmetric-threshold
cutoff** (`cutoff_reliable`) whose natural home is **liveness** (via
`TerminationCutoff`), plus **one sound monotone-counter bounded-unrolling
framework** (`PhaseCounting`) whose natural home is Paxos-family safety.
The two are orthogonal and cover different classes of protocols. Safety
verification of protocols that fit neither class should follow the
hand-rolled `OneThirdRuleCutoff` pattern.

---

## 9. References

### Files in mainline

- `Leslie/Cutoff.lean` — symmetric threshold cutoff (`cutoff_reliable`,
  `thresh_scaling_down`, `Config`, `threshView`, `ConfigInv`,
  `threshDetermined`, `cutoffBound`, `otr_symthresh`, `majority_symthresh`)
  **plus** the termination cutoff under namespace `TLA.TerminationCutoff`
  (`tvDeterministic`, `iterSucc_tv_eq`, `bounded_termination_cutoff`,
  `isCollapsing`, `isIdentityBelowThreshold`, OTR instantiation).
- `Leslie/Examples/OneThirdRuleCutoff.lean` — hand-rolled OTR safety
  under lossy HO with extended `Config 4 n` and `IsValidUnreliableSucc`.
- `Leslie/Examples/Combinators/PhaseCounting.lean` — monotone-counter
  bounded-unrolling framework with refinement theorems for fault models.
- `Leslie/Examples/Paxos/BoundedSingleProposer.lean` — single-proposer
  Paxos-lite instantiation, counter bound `2·n`.
- `Leslie/Examples/Paxos/BoundedPaxos.lean` — m-proposer real Paxos
  wrapping `Leslie/Examples/Paxos.lean`, counter bound `2·m·n + m`,
  agreement derived from `PaxosTextbookN.agreement` via `PaxosInv`.

### Archived (for historical reference)

- Branch `archive/cutoff-exploration` — full exploration state before
  PR #19, including the safety-cutoff attempt, Phase 1+2+3 scaffolding
  (`Config.next`, `ViewAssignment`, `FaithfulVA`), and `LockedOTR.lean`.
- Branch `archive/hollow-combinators` — intermediate state with the
  `CutoffIntegration` combinator wrappers for Raft/VR/PBFT/HotStuff/etc.

### External

- Konnov, Lazić, Veith: "Para² : Parametric Parallel model-checking with
  Threshold Automata" — structural inspiration for `SymThreshAlg`.
- Drăgoi, Henzinger, Veith: PSync — round-based symbolic execution.
- Abdulla et al.: "View Abstraction" — view-based parameterized cutoffs.

---

## Appendix A. The safety diameter

Even though the symmetric-threshold safety cutoff in §7 was removed, the
`safety_diameter` concept it used is still a clean and useful definition
worth recording.

For a transition system `T` with initial-state predicate `Init`,
transition relation `→`, and safety property `I`, define:

> **Safety diameter `D_I(T)`:**
>
> - If `T ⊨ □I` (safety holds): `D_I(T) = 0`.
> - Otherwise, the smallest `d` such that every reachable violating
>   state has an `Init`-to-violation trace of length `≤ d`.

This is the bound at which straight-line BMC becomes sound and complete
for the safety question starting from `Init`. Running BMC from every
`Init` state to depth `d`:

- If `d ≥ D_I(T)` and BMC finds no violation, there is none: `T ⊨ □I`.
- If `d < D_I(T)`, BMC may miss violations.

**Starting from `Init`, not "reachable".** An earlier draft wrote "from
every reachable state" instead of "from every initial state". With
"reachable", the definition is vacuous: if `I` is not an invariant, some
reachable state `s` satisfies `¬I s`, so the length-0 prefix from `s`
already violates `I`, making `d = 0` work for every system. Measuring
from the designated starting set is essential.

`PhaseCountingSystem.bound` (§5.1) is a constructive upper bound on
`D_I` for a large class of protocols: any invariant `Safe` holds at all
reachable states iff it holds at all traces of length `≤ P.bound`
starting from `P.init`.

---

## Appendix B. BenOr round-cutoff feasibility study

First of three feasibility studies performed while designing the round
cutoff in §6. Target: Ben-Or's binary consensus
(`Leslie/Examples/BenOr.lean`).

### B.1 BenOr's state

```lean
structure LState where
  val       : Fin 2
  witnessed : Option (Fin 2)     -- this-round witness, reset each round
  decided   : Option (Fin 2)     -- permanent decision

structure GState (n : Nat) where
  round  : Nat                    -- global round counter (lockstep model)
  phase  : Fin 2                  -- 0 = Report, 1 = Propose
  locals : Fin n → LState
```

BenOr is a lockstep model — single global `round : Nat`, no per-process
round. All local state is round-independent data (`val` overwritten
each round, `witnessed` reset, `decided` untagged).

**None of the local state fields carry an explicit round label.** The
only round-valued field in `GState` is `GState.round` itself. BenOr has
no round-indexed history.

### B.2 Instance sketches

With only `GState.round` as the round-valued field, all instances are
trivial:

- `RoundShift`: `shift k s = { s with round := s.round + k }`
- `RoundObserver`: `maxRound = minRound = s.round` (lockstep)
- `RoundWindow`: `agreeAbove r s₁ s₂ := ...` with `W = 0`
- `BoundedAdvance`: `D = 1`
- `RoundLocal`: `W = 0`
- `RoundInvariant` for `lock_inv`: trivially window-local and
  shift-invariant (the invariant mentions no round)

### B.3 Outcome

BenOr fails as a stress test. The theorem collapses with `W = 0`;
verification delivers no new information beyond what existing
induction-on-`n` gives. Recommended (at the time): try OTR.

---

## Appendix C. One-Third Rule round-cutoff feasibility study

Second feasibility study. Target: the One-Third Rule
(`Leslie/Examples/OneThirdRule.lean`).

**Headline:** OTR is equally degenerate, for a deeper architectural
reason.

### C.1 The architectural root cause

Writing out the type of `RoundAlg.update`:

```lean
update : P → S → (P → Option M) → S
```

**`update` has no access to any round number, nor to any history from
previous rounds.** The local state type `S` is chosen by the protocol,
but the `RoundAlg` contract explicitly forbids peeking at past rounds'
state. Whatever is stored in `S` is round-independent by construction.

The global `round : Nat` in `RoundState` is purely bookkeeping. It is
observed by the `CommPred` and incremented by `round_step`, but the
algorithm never reads it.

**Corollary:** **every protocol built on Leslie's `RoundAlg` framework
is structurally round-history-free.** Behavior at round `r` depends only
on the locals at round `r` and the HO collection for round `r`. For
such a protocol:

- `W = 0` always suffices.
- The round cutoff theorem applies trivially but delivers no information.
- The core proof step — compressing history via `agreeAbove` — never
  fires.

This applies to every `RoundAlg`-based protocol in Leslie: OTR, BenOr,
LastVoting (despite its name — the "last vote" is stored in `S`, not
round-indexed), FloodMin, LeaderBroadcast, BallotLeader, etc.

### C.2 `RoundAlg` is already a kind of cutoff

Leslie's `RoundAlg` framework already achieves round compression by
construction. Because `update` has no access to history, every
`RoundAlg`-based protocol is tautologically "Markov" — each round's
behavior depends only on the current state. This is why node cutoffs
(§2) compose so well with `RoundAlg` protocols: `RoundAlg` handles the
round dimension by restricting expressivity, and a round cutoff would
add value only for protocols that step *outside* `RoundAlg`'s
restrictions.

### C.3 Outcome

OTR fails as a round-cutoff stress test for the same reason BenOr does,
and more fundamentally: the framework it's built on structurally forbids
round-indexed state. This redirected the feasibility effort toward
ballot-indexed protocols.

---

## Appendix D. Paxos round-cutoff feasibility study

Third and final feasibility study. Target: single-decree Paxos
(`Leslie/Examples/Paxos.lean`).

### D.1 Shift invariance: yes

Paxos transitions reference ballots only through comparisons
(`<`, `≤`, `>`, `≥`), equality tests, and assignments. No arithmetic
on ballot values — all ballot assignments are copies. Adding a constant
preserves order and equality, hence all behavior. **Shift invariance
holds.** ✓

### D.2 Window locality: no

The `RoundLocal W` condition requires that transitions only depend on
state within `W` ballots of the current maximum. **This fails for Paxos.**

Consider a reachable state where:
- Proposer 1 has ballot 1 and has reached phase 2b majority
- Proposer 2 has ballot 1000 and is doing phase 2a

Proposer 2's phase 2a checks `rep 2 i` for every acceptor in its
1b-quorum. An acceptor that has been promising since ballot 1 may have
`rep 2 i = some (1, v₁)` — a report from 999 ballots below. By the
`hconstr` condition, proposer 2 must pick the value of the highest-ballot
report; if ballot 1 is the only reported ballot, proposer 2 must use `v₁`.

**Proposer 2's transition depends on ballot values arbitrarily far
below its own.** No finite `W` suffices.

### D.3 The deeper observation

When we trace *where ballot values come from*, a stronger fact emerges:
**Paxos never mints new ballot values at runtime.** All ballot values
in any reachable state are drawn from the fixed `range ballot` of the
initial ballot function. This range has exactly `m` elements (one per
proposer), and `m` is a fixed protocol parameter.

**The total set of distinct ballot values appearing in any reachable
Paxos execution is bounded by `m`.** Single-decree Paxos has at most
`m` distinct ballot values across its entire execution — the "ballot
dimension" is already finite at the model level, bounded by `m`.

### D.4 Outcome

The round cutoff as designed does not apply to single-decree Paxos, but
for a surprising reason: **Paxos's "round" dimension is already finite
at the model level**. There is no unbounded round dimension to compress.

However, this very observation is what made the §5 phase-counting
approach viable: instead of trying to compress rounds, count them. The
`BoundedMProposer` instantiation in PR #20 gets a safety diameter of
`2·m·n + n + m` by structural slot counting — which is exactly what
"ballot dimension is finite at `m`" buys us. The round-cutoff feasibility
failure seeded the phase-counting framework that now handles Paxos.

---

## Appendix E. Combined conclusion of the three feasibility studies

The three studies (BenOr, OTR, Paxos) yielded a uniform negative result
for the round-cutoff theorem: **no protocol in Leslie's current corpus
satisfies the theorem's non-triviality conditions.**

The three failure modes are distinct:

| Protocol | Class | Why the theorem is vacuous/inapplicable |
|---|---|---|
| BenOr | `RoundAlg` | Global `round` counter only; no round-indexed local state |
| OTR | `RoundAlg` | Same architectural reason — `RoundAlg` forbids round history |
| Paxos | ballot-indexed | Ballot dimension is already finite (`m` proposers, no new ballots at runtime) |

**Findings that survived the negative result:**

1. **`RoundAlg` performs round compression by type.** Its restricted
   signature makes all HO-model protocols round-Markov by construction.
2. **Paxos's rounds are structurally finite.** This became the basis
   for the phase-counting framework in §5.
3. **Ballot renaming is a valid symmetry.** Paxos's invariance under
   strict-monotone ballot renumbering could support symbolic execution
   or model-checking tools even without a cutoff theorem.
4. **The round dimension / ballot structure distinction matters.**
   HO-model round protocols (lockstep, advancing) and ballot-indexed
   consensus (sparse, arbitrary-spaced) are fundamentally different
   and need different cutoff frameworks.

---

## Appendix F. Round-cutoff theorem design (preserved for reference)

The original §4 design is preserved here. None of it is currently
formalized.

### F.1 Formal state-level operations

```lean
class RoundShift (S : Type) where
  shift   : ℤ → S → S
  shift_zero (s : S)          : shift 0 s = s
  shift_add  (j k : ℤ) (s : S) : shift (j + k) s = shift j (shift k s)

class RoundObserver (S : Type) [RoundShift S] where
  maxRound : S → ℤ
  minRound : S → ℤ
  maxRound_shift (k : ℤ) (s : S) : maxRound (shift k s) = maxRound s + k
  minRound_shift (k : ℤ) (s : S) : minRound (shift k s) = minRound s + k
```

`ℤ` not `ℕ` because shifting by `-k` must be total.

### F.2 Round-shift invariance

```lean
structure RoundShiftInvariant (A : ActionSpec S Act) [RoundShift S] : Prop where
  init_closed : ∀ k s, A.init s → A.init (RoundShift.shift k s)
  next_equiv  : ∀ k s s' act,
                A.next s s' act ↔
                A.next (RoundShift.shift k s) (RoundShift.shift k s') act
```

**Subtlety.** The typical init predicate says "every process is at round
0", which is one orbit of the shift action, not shift-closed. Either
relax init to "every process at the same round, unspecified" or work
on shift-orbit quotients.

### F.3 Bounded advance

```lean
structure BoundedAdvance (A : ActionSpec S Act)
    [RoundShift S] [RoundObserver S] (D : ℕ) : Prop where
  max_advance  : ∀ s s' act, A.next s s' act →
                 RoundObserver.maxRound s' ≤ RoundObserver.maxRound s + D
  min_monotone : ∀ s s' act, A.next s s' act →
                 RoundObserver.minRound s ≤ RoundObserver.minRound s'
```

For almost all Leslie round-based algorithms, `D = 1`.

### F.4 Window locality

```lean
class RoundWindow (S : Type) [RoundShift S] [RoundObserver S] where
  agreeAbove : ℤ → S → S → Prop
  -- equivalence axioms, mono in r, respects shift
  agree_eq : ∀ s₁ s₂, agreeAbove (minRound s₁ - 1) s₁ s₂ ↔ s₁ = s₂

structure RoundLocal (A : ActionSpec S Act)
    [RoundShift S] [RoundObserver S] [RoundWindow S] (W : ℕ) : Prop where
  next_respects : ∀ s₁ s₂ s₁' act,
    RoundWindow.agreeAbove (RoundObserver.maxRound s₁ - W) s₁ s₂ →
    A.next s₁ s₁' act →
    ∃ s₂', A.next s₂ s₂' act ∧
           RoundWindow.agreeAbove (RoundObserver.maxRound s₁' - W) s₁' s₂'
```

### F.5 Target theorem

```lean
theorem round_cutoff (A : ActionSpec S Act) (I : S → Prop)
    [RoundShift S] [RoundObserver S] [RoundWindow S]
    (hAlg : RoundShiftInvariant A)
    (hAdv : BoundedAdvance A D)
    (hLoc : RoundLocal A W)
    (hInv : RoundInvariant I W)
    (n : ℕ) :
    (∀ s, Reachable A s → I s) ↔
    (∀ cfg ∈ canonicalConfigs n W,
     ∀ k ≤ n * D + W,
     ∀ s, ReachableFromIn A cfg k s → I s)
```

**Proof sketch.** Assume RHS; given a reachable state `s` with `¬ I s`,
shift so `minRound s = 0`, bound `maxRound` by `BoundedAdvance`, and if
the state has history beyond the window, use `RoundLocal` to truncate
it to a window-equivalent state reachable from a canonical config in
≤ `W` steps. `RoundInvariant` gives `¬ I s̃`. Contradiction.

The missing piece is formalizing "truncation" as a concrete operation
on states. Revisit if Leslie gains a multi-decree protocol that
exercises this.
