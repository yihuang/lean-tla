# Randomized Leslie: A Conservative Extension Plan (v2.2)

> **Revision history.** v1 (initial design); v2 addresses internal
> review: explicit Mathlib subsection, `ProbActionSpec` shape aligned
> with existing `ActionSpec`, reconciliation with existing
> `Examples/BenOr.lean`, fairness encoding made consistent, M2.5
> ElGamal replaced with statistical example, composition combinators
> given type-level disjointness, conservativity claim narrowed and
> made precise, AVSS certificate shape sketched, helper types defined.
> v2.1 records round-2 review findings: three foundational technical
> issues, a motivation gap, and a CI safety bug, scheduled as a 2-week
> M0 spike. v2.2 (this version) collapses M0 outcomes into the inline
> signatures: trace distributions are `Measure (Π n, σ × Option ι)`
> via `Kernel.trajMeasure` (M0.1), parallel composition is the
> shared-state `parallelWithNet` shape (M0.2), AST soundness uses
> Mathlib's `Submartingale.ae_tendsto_limitProcess` directly with a
> ~50-line shim (M0.3), CI gate uses an allowlist (M0.4). The §M0
> spike artifacts at `docs/randomized-leslie-spike/01–03-*.md` and
> `Leslie/Prob/Spike/*.lean` back every claim with working Lean.

## Goals and constraints

Extend Leslie to model and verify *randomized* distributed protocols
(asynchronous verifiable secret sharing, common coins, randomized
Byzantine agreement, threshold cryptography) while satisfying two hard
constraints:

1. **Conservative extension.** Existing files
   (`Basic`, `Action`, `Refinement`, `Round`, `Cutoff`, `Layers`,
   `Simulate`, `AssumeGuarantee`, `EnvAbstraction`, `SymShared`,
   `PhaseRound`, `Rules/*`, `Tactics/*`, `Gadgets/*`, `Examples/*`,
   `Rust/*`) remain byte-for-byte unchanged. Every existing theorem
   and proof keeps its meaning. (See *Conservativity, precisely*
   below for the formal statement.)
2. **Not coupled to the HO model.** The probabilistic core lives on top
   of the interleaving `ActionSpec`, which is where asynchronous
   Byzantine randomized protocols naturally sit. Round-based
   randomized reasoning is an *optional* later layer, not a prerequisite.

The headline target is a fully machine-checked end-to-end proof of
**Canetti–Rabin asynchronous Byzantine agreement** assembled from
verified AVSS and a verified common-coin protocol via a UC-style
composition theorem.

## Mathlib dependency

**Decision: take on Mathlib at M1, all at once, no incremental approach.**

Leslie's current `lakefile.lean` depends only on `aesop` and
`lintLlmProofs`, with no Mathlib dependency. The probabilistic
extension cannot avoid Mathlib: we need `PMF`, `Polynomial`,
`Field`, `MeasureTheory.Martingale`, `NNReal`, and analytic
machinery for the 2-D random walker example. Adding Mathlib has
real costs:

- *Cold build time.* From minutes to roughly an hour. CI economics
  change: caching the Mathlib build via `mathlib4-cache` is mandatory,
  not optional. The Mathlib cache reduces cold build time to ~10
  minutes once the cache is populated.
- *Dependency surface.* Mathlib has its own breaking-change cadence;
  `lean-toolchain` upgrades become coupled to Mathlib's release schedule.
- *Compile-time RAM.* Mathlib pushes `lake build` peak RAM into the
  several-gigabyte range; CI runners must be sized accordingly.

The argument *for* taking it on at M1 (rather than incrementally):

- Every `Leslie/Prob/` module needs Mathlib. There is no "first
  module that doesn't need it."
- Adding Mathlib mid-milestone forces a cascade of import changes
  and conflicts with the conservatism CI check.
- A single up-front commit "lakefile: add Mathlib dependency" cleanly
  delineates before/after.

**Mitigation plan:**

- Pin a specific Mathlib commit at start of M1; advance only at
  milestone boundaries.
- Use Mathlib's `cache` lake script in CI (the `mathlib4-cache`
  GitHub action).
- Document peak-RAM and build-time numbers after the M1 W1 commit so
  contributors know what to expect.
- The conservatism CI check (see below) ignores `lakefile.lean`,
  `lake-manifest.json`, and `lean-toolchain` so Mathlib upgrades
  don't trigger false positives.

## Design principles

1. **Embed via shape-preserving translation, don't refactor.**
   `ProbActionSpec` mirrors `ActionSpec`'s function-indexed shape
   (see *Core abstractions* below). A coercion
   `ActionSpec → ProbActionSpec` sends each deterministic gated action
   to its Dirac counterpart. Conservativity is a precisely-stated
   claim, not a hand-wave (see *Conservativity, precisely*).
2. **PMF for single steps, Measure for traces.** Per-step action
   effects are Mathlib `PMF` (probability mass functions over
   countable single-step branching — clean for AVSS, Shamir, common
   coin, randomized BA). Trace distributions are
   `MeasureTheory.Measure` on the cylinder σ-algebra, constructed
   from the per-step `PMF`s via `ProbabilityTheory.Kernel.trajMeasure`
   (Ionescu-Tulcea). The PMF/Measure boundary is "one step vs. many
   steps." This was v2's "Discrete probability first" with the
   measure-theoretic concession promoted explicitly: AST soundness
   needs Doob's martingale convergence, which is measure-theoretic;
   pretending otherwise was the v2 bug. M0.1 outcome.
3. **Separate the three sources of "uncertainty"** at the type level:
   probabilistic choice (inside an action body), adversarial scheduling
   (which action fires next), and adversarial corruption (which parties
   the adversary controls). This is task-PIOA discipline; it is the
   single most important design decision and the easiest to get wrong.
4. **Interleaving substrate, HO as add-on.** `Leslie/Prob/Action.lean`
   is the foundation. `Leslie/Prob/Round.lean` (a probabilistic HO
   model) is a strictly later, strictly optional layer.
5. **One composition theorem.** UC composition is proved *once* against
   `ProbActionSpec` and applied many times. Property-specific
   composition lemmas are exposed as separate combinators with
   *type-level disjointness* (see *Composition combinators* below) so
   users cannot accidentally compose secrecy goals under non-UC
   composition.
6. **Use sound proof rules with constructible certificates.** For AST,
   this means the POPL 2025 two-function rule (variant `U` for
   distance, supermartingale `V` for likelihood, sublevel-set
   compatibility) as the *primary* certificate, with weaker / derived
   rules (McIver–Morgan variant, FH 2015 + DSM, MMKK 2018) exposed as
   constructors that build certificates of this primary type. (The
   relative-completeness result of POPL 2025 is metatheoretic; users
   construct certificates, and what matters here is soundness plus a
   library of constructors covering the standard cases.) For
   distributed AST specifically, layer the POPL 2026 weak-fairness
   extension on top.
7. **Separate distance from likelihood at the API level.** This is the
   structural lesson of POPL 2025: forcing the variant to *be* a
   supermartingale conflates two conceptually distinct objects and
   produces incomplete or contrived certificates. Leslie's
   `Liveness.lean` mirrors the separation in its types.
8. **Mirror pRHL for distributional reasoning.** The relational-Hoare
   discipline from EasyCrypt (and successors CryptHOL, SSProve, the
   POPL 2025 quantitative pRHL) is the right vocabulary for secrecy
   and indistinguishability proofs. Build a relational judgment
   `Π₁ ≈⟨R⟩ Π₂` early (M1) so every secrecy proof afterwards uses the
   same skeleton.

## Architecture

### File layout

Existing files: **no changes**. New files only.

```
Leslie/
├── (existing files unchanged — see README for full inventory)
├── Prob/
│   ├── PMF.lean              PMF utilities, total variation, conditioning
│   ├── Action.lean           ProbGatedAction, ProbActionSpec
│   ├── Embed.lean            ActionSpec → ProbActionSpec, conservativity lemmas
│   ├── Adversary.lean        Scheduler / corruption model + fairness predicate
│   ├── Trace.lean            Trace distributions parameterized by adversary
│   ├── Refinement.lean       Probabilistic refinement (distributional A-L)
│   ├── Invariant.lean        Almost-sure invariants, prob analog of init_invariant
│   ├── Coupling.lean         pRHL-style relational judgment, identity & bijection
│   │                         couplings, eager/lazy sampling, up-to-bad
│   ├── Liveness.lean         POPL 2025 (V,U)-rule for AST; POPL 2026 fair-AST
│   │                         extension; derived rule constructors
│   ├── Quantitative.lean     [optional] Stochastic-invariant indicators,
│   │                         lower/upper bounds on termination probability
│   ├── Secrecy.lean          View functions, view-equivalence, statistical secrecy
│   ├── Polynomial.lean       Uniform polynomial sampling, t-evaluations-uniform
│   ├── Layers.lean           [Milestone 6] Probabilistic movers, prob Lipton
│   └── Round.lean            [Milestone 6] Randomized HO model
├── UC/
│   ├── IdealFunc.lean        Ideal functionalities as distinguished ActionSpecs
│   ├── Environment.lean      Environment + distinguisher
│   ├── Realize.lean          Realizes Π F ε  (simulation-based realization)
│   ├── Compose.lean          UC composition theorem
│   └── Hybrid.lean           Hybrid-model reasoning (Π in F-hybrid model)
├── Tactics/
│   └── Prob.lean             prob_unfold, by_coupling, coupling_identity,
│                             coupling_bijection, coupling_swap, coupling_up_to_bad,
│                             polynomial_uniform, ast_certificate, fair_ast,
│                             hybrid_step, realize_ideal
└── Examples/
    └── Prob/
        ├── Shamir.lean              [M1] univariate Shamir secrecy
        ├── OneTimePad.lean          [M2.5] crypto calibration (info-theoretic)
        ├── ITMAC.lean               [M2.5] info-theoretic MAC (replaces ElGamal)
        ├── BivariateShamir.lean     [M2] bivariate generalization
        ├── BrachaRBC.lean           [M2] async Byzantine, deterministic
        ├── SyncVSS.lean             [M2.7] BGW-style synchronous VSS
        │                                 (info-theoretic, n ≥ 3t+1, fixed rounds)
        ├── BenOrAsync.lean          [M3] async randomized BA — distinct from
        │                                 existing Leslie/Examples/BenOr.lean
        │                                 (HO/synchronous, deterministic over-approx)
        ├── CommonCoin.lean          [M3] Rabin-style weak common coin
        ├── AVSS.lean                [M3] Canetti–Rabin AVSS
        └── AsyncBA.lean             [M5] AVSS + coin → async BA
```

Total new code estimate: ~6,000–8,000 lines Lean across foundations,
tactics, and examples. Existing Leslie codebase: untouched.

### Helper types (defined here, used throughout)

For the `ProbActionSpec` and `Adversary` declarations to be readable
without forward references:

```lean
-- A party identifier; we use ℕ but the protocol fixes a finite range.
abbrev PartyId := ℕ

-- An action identifier in a ProbActionSpec; same shape as the existing
-- ActionSpec's index type ι.
-- (Concretely, ActionId is the user-chosen ι in `ProbActionSpec σ ι`.)

-- A history is a finite prefix of (state, action-taken) pairs.
def History (σ ι : Type) := List (σ × Option ι)

-- A trace is an infinite sequence of states with optional action labels;
-- terminated traces stutter at a terminal state.
def Trace (σ ι : Type) := Stream' (σ × Option ι)
```

These are deliberately concrete (not abstract types) so the rest of
the doc reads as Lean.

### Core abstractions — `ProbActionSpec` matching `ActionSpec`'s shape

The existing `Leslie/Action.lean` has (per review):

```lean
structure ActionSpec (σ ι : Type) where
  init    : σ → Prop
  actions : ι → GatedAction σ
```

— function-indexed by a user-chosen index type `ι`, no per-action
parameter. `ProbActionSpec` mirrors this shape exactly:

```lean
-- Leslie/Prob/Action.lean
structure ProbGatedAction (σ : Type) where
  guard  : σ → Prop
  effect : (s : σ) → guard s → PMF σ

structure ProbActionSpec (σ ι : Type) where
  init    : σ → Prop
  actions : ι → ProbGatedAction σ
```

Note: **no separate parameter `P`**. The original v1 draft had
`(S P : Type)` with `P` for per-action parameters; existing Leslie
folds parameters into `ι` (index actions by their parameters), so the
`P` is unnecessary and breaks the embedding.

The embedding becomes literally one line per field:

```lean
-- Leslie/Prob/Embed.lean
def GatedAction.toProb (a : GatedAction σ) : ProbGatedAction σ where
  guard  := a.guard
  effect := fun s _ => PMF.pure (a.effect s)

def ActionSpec.toProb (Π : ActionSpec σ ι) : ProbActionSpec σ ι where
  init    := Π.init
  actions := fun i => (Π.actions i).toProb
```

That is genuinely a coercion, not a translation. The reviewer's
critique on this point was correct and motivated this revision.

### Conservativity, precisely

The original v1 doc claimed a conservativity biconditional
`WF1 Π R term ↔ ASTCertificate Π.toProb term`. The review correctly
points out that `WF1` in `Rules/WF.lean` operates on
`pred σ / action σ`, not on `ActionSpec`, so this biconditional crosses
an abstraction boundary. The precise statement is narrower and lives
at three levels:

**Level 1 (file-level).** Existing files do not change. Verified by
CI script `scripts/check-conservative.sh`.

**Level 2 (semantic preservation, easy direction).** For every
existing `ActionSpec` `Π` and state predicate `φ`:

```lean
theorem invariant_preserved (Π : ActionSpec σ ι) (φ : σ → Prop) :
    Π ⊨ □φ → Π.toProb ⊨ □̃ φ

theorem refines_preserved (Π Σ : ActionSpec σ ι) :
    Π ⊑ Σ → Π.toProb ⊑ₚ Σ.toProb
```

These are essentially trivial because every PMF on the RHS is Dirac.
They give us "anything proved about `Π` lifts to `Π.toProb`," which
is the *useful* direction.

**Level 3 (the WF1 bridge).** `WF1` operates one abstraction level
below `ActionSpec`, on raw `pred σ` and `action σ`. The conservativity
claim there is:

```lean
-- Stated for WF1Premises (action-spec-flavored) only, not raw WF1.
theorem WF1Premises_implies_AST
    (Π : ActionSpec σ ι) (i : ι) (P Q : σ → Prop)
    (h : WF1Premises Π i P Q) :
    ∃ cert : FairASTCertificate Π.toProb (fun s => Q s),
      cert.fair_actions = {i}
```

This is one direction (deterministic-WF1 implies AST certificate);
the converse does not hold in general (an AST certificate may have a
non-trivial `V` even when the underlying spec is deterministic, e.g.,
when the user wants to use the rule as a more-flexible variant rule).
The reviewer was right that the original biconditional was overclaim;
this directional statement is what we actually need.

### Reconciliation with existing `Leslie/Examples/BenOr.lean`

The existing repository contains `Leslie/Examples/BenOr.lean` (per
review: ~859 lines, HO-model, restricted to reliable rounds for safety,
treats the coin as nondeterminism). This file is **not** what
`Examples/Prob/BenOrAsync.lean` (M3) replaces or supersedes; both
coexist and serve different purposes.

The relationship is:

- *Existing `Examples/BenOr.lean`* — synchronous (HO-model), coin as
  *demonic nondeterminism*. Proves agreement and validity under
  reliable-rounds assumption. Does **not** prove termination
  (impossible under demonic nondeterminism).
- *New `Examples/Prob/BenOrAsync.lean`* — asynchronous
  (`ProbActionSpec`), coin as *probabilistic choice*. Proves
  agreement, validity, **and** almost-sure termination under weak
  fairness.

The existing file is the "deterministic over-approximation" of the
new one in a precise sense:

```lean
-- Stretch goal in M3 (not blocking)
theorem BenOrAsync_refines_BenOrHO :
    BenOrAsync.spec.toProb_with_demonic_coin ⊑ₚ BenOrHO.spec.toProb
```

i.e., interpreting the async protocol's coin as nondeterministic
recovers the existing HO model up to scheduling. Proving this is *not*
a milestone deliverable — it's a sanity check that the new and old
proofs are not in conflict. If it doesn't go through cleanly, that's
a finding worth understanding before merging M3.

The naming distinction (`BenOr.lean` vs. `BenOrAsync.lean`) is
deliberate: it tells a reader of the example index which model is in
play.

### Composition combinators with type-level disjointness

The v1 doc claimed three combinators (`compose_refinement`,
`compose_fair_refinement`, `compose_uc`) would be "name-distinct so
users cannot accidentally compose secrecy under non-UC composition."
The review correctly points out this is aspirational without
type-level enforcement. Here is the type-level distinction:

```lean
-- Leslie/Prob/Refinement.lean
-- Trace-level refinement: same shape as existing Refinement.lean,
-- lifted to trace measures (Mathlib.MeasureTheory.Measure under
-- the cylinder σ-algebra; v2.2 update from PMF-of-streams).
def Refines (Π : ProbActionSpec σ ι) (Σ : ProbActionSpec σ' ι')
            [MeasurableSpace σ] [MeasurableSpace ι]
            [MeasurableSpace σ'] [MeasurableSpace ι'] : Prop :=
  ∀ (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] A,
    ∃ (μ₀' : Measure σ') (_ : IsProbabilityMeasure μ₀') A',
      Measure.map projectStuttering (traceDist Σ A' μ₀') = traceDist Π A μ₀
notation Π " ⊑ₚ " Σ => Refines Π Σ

-- Leslie/UC/Realize.lean
-- A *predicate-erased* realization claim. The ε is indistinguishability
-- error; the ideal functionality F has its own state and adversary
-- interface that ⊑ₚ does not expose.
structure Realizes
    (Π : ProbActionSpec σ ι)
    (F : IdealFunctionality σ_F ι_F)
    (ε : ℝ≥0) : Prop where
  simulator : RealAdversary Π → IdealAdversary F
  bound : ∀ Z : Environment, ∀ A : RealAdversary Π,
            (envView Z (Π ∥ A)).totalVariation
            (envView Z (F ∥ simulator A)) ≤ ε

-- The composition combinators take distinct argument types:

-- Safety composition: takes ⊑ₚ on both legs, produces ⊑ₚ on parallel.
-- Cannot accept a Realizes argument because Realizes is not Refines.
def compose_refinement
    (h₁ : Π₁ ⊑ₚ Σ₁) (h₂ : Π₂ ⊑ₚ Σ₂) (disjoint : ...) :
    (Π₁ ∥ Π₂) ⊑ₚ (Σ₁ ∥ Σ₂)

-- Fair-refinement composition: takes ⊑ₚ + fairness side conditions.
-- Same input type as compose_refinement but extra fairness premises.
def compose_fair_refinement
    (h₁ : Π₁ ⊑ₚ Σ₁) (h₂ : Π₂ ⊑ₚ Σ₂)
    (fair₁ : FairnessPreservation Π₁ Σ₁)
    (fair₂ : FairnessPreservation Π₂ Σ₂) :
    Π₁ ∥ Π₂ ⊨ weakFair → ◇̃ goal → ...

-- UC composition: takes Realizes + hybrid-model proof.
-- Realizes and hybridProof are distinct types from ⊑ₚ.
def compose_uc
    {F : IdealFunctionality σ_F ι_F}
    (h_real : Realizes Π_F F ε)
    (h_hyb  : HybridModelProof Π[F] φ δ) :
    Realizes (Π[F].substitute (Π_F / F)) φ.spec (δ + ε)
```

`Refines`, `Realizes`, and `HybridModelProof` are three distinct
types; you cannot pass a `⊑ₚ` proof to `compose_uc` because the type
checker rejects it. The safety claim is enforced by Lean's type
system, not by naming convention. (The reviewer's pushback on this
point was the right one to make.)

### Adversary, scheduler, fairness — no inconsistency

The v1 doc had two contradictory framings. v2 picks one:

**Fairness is a hard predicate on adversaries.** It lives in the
`Adversary` type and is used by `FairASTCertificate.sound` directly.

```lean
-- Leslie/Prob/Adversary.lean
structure Adversary (σ ι : Type) where
  schedule : History σ ι → Option ι           -- demonic scheduler
  corrupt  : Set PartyId                       -- static corruption

-- A fairness assumption set
structure FairnessAssumptions (σ ι : Type) where
  fair_actions : Set ι
  -- Predicate: an adversary is weakly fair w.r.t. these actions
  isWeaklyFair : Adversary σ ι → Prop

-- A fair adversary: bundle adversary + proof of fairness
structure FairAdversary (σ ι : Type) (F : FairnessAssumptions σ ι) where
  toAdversary : Adversary σ ι
  fair        : F.isWeaklyFair toAdversary
```

`FairASTCertificate.sound` then quantifies over `FairAdversary _ F`,
not over arbitrary adversaries with a temporal-side-condition. This
matches POPL 2026's encoding and removes the v1 inconsistency.

The scheduler is **demonic and history-deterministic** — given the
visible history, the adversary picks an action (or `none` to stutter).
This is the standard MDP / adversarial-randomization encoding (see
*Open questions* on whether to extend to randomized schedulers).

### `ProbActionSpec` and trace distributions

```lean
-- Leslie/Prob/Trace.lean
-- For any fixed (deterministic) adversary and an initial-state
-- distribution, a ProbActionSpec induces a probability measure over
-- infinite-trace product space. Constructed via Ionescu-Tulcea kernel
-- composition (`Mathlib.Probability.Kernel.IonescuTulcea.Traj.trajMeasure`).
def traceDist (Π : ProbActionSpec σ ι) (A : Adversary σ ι)
              [MeasurableSpace σ] [MeasurableSpace ι]
              (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
              Measure (Π n : ℕ, σ × Option ι)
```

The induction has the standard structure: at each step, the adversary
picks an action or stutters; if it picks `i`, the action's effect PMF
is sampled (lifted to a one-step Markov kernel); Ionescu-Tulcea
extends to a measure on the infinite product. **Decision: traces are
infinite product elements `Π n : ℕ, σ × Option ι` (always defined),
with termination encoded as eventual stuttering at a terminal state.**
The `Stream'`/`Π n` distinction is glued by a small (~30-line)
isomorphism in `Leslie/Prob/Trace.lean`.

Note the additional `[MeasurableSpace σ] [MeasurableSpace ι]`
typeclass requirements — these are the M0.1 cost of moving from
PMF-on-streams (which doesn't exist) to Measure-on-product (which
does, via Mathlib). For a finite-state `ProbActionSpec` they resolve
trivially.

### Coupling — pRHL-style relational judgment

```lean
-- Leslie/Prob/Coupling.lean
structure PMF.Coupling (μ : PMF α) (ν : PMF β) where
  joint    : PMF (α × β)
  marg_left  : joint.map Prod.fst = μ
  marg_right : joint.map Prod.snd = ν

def PMF.Coupling.supports (c : Coupling μ ν) (R : α → β → Prop) : Prop :=
  ∀ p ∈ c.joint.support, R p.1 p.2

theorem PMF.eq_of_coupling_id (c : PMF.Coupling μ ν)
        (h : c.supports (· = ·)) : μ = ν

-- Sound rules (skip / sample-identity / sample-bijection / swap / case)
theorem coupling_identity   : ...     -- same code, same randomness
theorem coupling_bijection  : ...     -- the AVSS-secrecy workhorse
theorem coupling_swap       : ...     -- eager-vs-lazy sampling
theorem coupling_up_to_bad  : ...     -- fundamental lemma of game-playing

-- Two ProbActionSpecs related by R produce R-coupled trace
-- distributions. Step-level couplings are PMF-flavored (good
-- ergonomics for sampling-based reasoning); trace-level couplings
-- are Measure-flavored (Mathlib's `Measure.prod` + projections).
-- The bridge is `Kernel.traj`'s functoriality: a step-level PMF
-- coupling lifts to a trace-level Measure coupling.
def RelatedTraces (Π₁ : ProbActionSpec σ₁ ι₁) (Π₂ : ProbActionSpec σ₂ ι₂)
                  (R : σ₁ → σ₂ → Prop) : Prop := ...

theorem RelatedTraces.view_eq (h : RelatedTraces Π₁ Π₂ R) ... :
    Measure.map V (traceDist Π₁ _ _) = Measure.map V' (traceDist Π₂ _ _)
```

### AST certificate — POPL 2025 + POPL 2026

```lean
-- Leslie/Prob/Liveness.lean — POPL 2025 two-function rule
structure ASTCertificate
    (Π : ProbActionSpec σ ι) (term : σ → Prop) where
  Inv     : σ → Prop
  V       : σ → ℝ≥0
  U       : σ → ℕ
  inv_init : ∀ s, Π.init s → Inv s
  inv_step : ∀ s, Inv s → ∀ s', s' ∈ supp(next Π s) → Inv s'
  V_pos    : ∀ s, Inv s → ¬ term s → V s > 0
  V_term   : ∀ s, term s → V s = 0
  V_super  : ∀ s, Inv s → ¬ term s → 𝔼[V ∘ next Π | s] ≤ V s
  U_term   : ∀ s, term s → U s = 0
  U_dec_det : ∀ s, Inv s → deterministic s →
                ∀ s' ∈ supp(next Π s), U s' < U s
  U_bdd_subl : ∀ r, ∃ M, ∀ s, Inv s → V s ≤ r → U s ≤ M
  U_dec_prob : ∀ r, ∃ ε > 0, ∀ s, Inv s → probabilistic s → V s ≤ r →
                ∑ s' ∈ supp(next Π s) with U s' < U s, prob s s' ≥ ε

theorem ASTCertificate.sound :
    ASTCertificate Π term →
    ∀ (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] (A : Adversary σ ι),
      ∀ᵐ ω ∂(traceDist Π A μ₀), ∃ n, term (ω n).1
```

```lean
-- POPL 2026 fair extension
structure FairASTCertificate
    (Π : ProbActionSpec σ ι) (F : FairnessAssumptions σ ι) (term : σ → Prop)
    extends ASTCertificate Π term where
  -- The supermartingale and variant conditions need only hold under
  -- adversaries weakly-fair to F.fair_actions
  V_super_fair : ∀ A : FairAdversary σ ι F, ∀ s, Inv s → ¬ term s →
                   𝔼[V ∘ next Π | s, A.toAdversary] ≤ V s

theorem FairASTCertificate.sound :
    FairASTCertificate Π F term →
    ∀ (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
      (A : FairAdversary σ ι F),
      ∀ᵐ ω ∂(traceDist Π A.toAdversary μ₀), ∃ n, term (ω n).1
```

### AVSS termination certificate — sketch

The reviewer's strongest point: the v1 doc proposed proving AVSS
termination via `FairASTCertificate` without specifying what `V`, `U`,
`Inv` look like. Here is the sketch.

**Setup.** AVSS (Canetti–Rabin '93) with `n ≥ 3t+1`, dealer with
secret `s`. Each party progresses through three phases: SHARE
(receive `(f(i, ·), f(·, i))` from dealer), ECHO (broadcast received
values for cross-checking), READY (broadcast a READY when enough
ECHOs match), OK (output share when enough READYs received). Honest
parties output a share once the protocol terminates.

**Invariant `Inv`.** Conjunction of:
- *Per-party local invariants:* receive buffers are subsets of legal
  messages; phase counter monotone; READY count monotone.
- *Cross-party invariants:* if two honest parties have READY-completed
  the same dealer, their share-views agree on `f(i,j)` for all `i,j`.
- *Adversary-stable invariants:* corrupt parties' message logs are
  monotone (they can send more, never retract).

These are existing-Leslie-style invariants; lift via
`invariant_preserved`.

**Distance variant `U`.** A lexicographic combination of three
counters, packed into a single `ℕ`:

```
U(s) = (# honest parties not yet OK) · K²
     + (# honest parties not yet READY) · K
     + (# unprocessed honest-to-honest messages in transit)
```

where `K` bounds each individual count. Decreases on each "useful"
honest step (delivery of an honest message that triggers ECHO/READY/OK).

**Likelihood supermartingale `V`.** This is the load-bearing piece
and where async randomized BA actually needs the POPL 2025 rule (an
RSM alone won't work because the adversary's delay budget is
unbounded). One workable shape:

```
V(s) = Σ_{honest i} max(0, T - phase_progress(i))
```

where `T` is a threshold and `phase_progress(i)` increases when honest
party `i` advances through SHARE → ECHO → READY → OK. Under any fair
adversary (delivering honest-to-honest messages eventually),
`phase_progress` is non-decreasing in expectation. `V` is a
supermartingale because adversarial actions can only stall, not undo,
honest progress.

**Sublevel-set compatibility.** On `{V ≤ r}`, at most a bounded number
of phase steps remain; `U` is bounded by the number of honest parties
times the per-party state space (finite per `Inv`).

**Fairness assumptions.** `F.fair_actions` = honest-to-honest message
delivery + honest local steps + AVSS coin actions if any. (Canetti–Rabin
AVSS itself does not toss a coin; the secret is the dealer's
randomness, and termination doesn't depend on probabilistic events
post-share.)

**Honest caveat.** This is a sketch, not a proof. The risk that the
shape doesn't quite work — e.g., that some adversary scheduling
prevents the supermartingale from being non-increasing on probabilistic
steps — is real. The M3 entry gate (see *Risk register*) is "discharge
this sketch into a Lean-level statement of `FairASTCertificate`
fields" before AVSS week 5. If that exercise reveals the rule needs
extension, that's a paper finding to discuss with the POPL 2026
authors.

### Why the substrate is interleaving, not HO

`Leslie/Prob/` extends `Leslie/Action.lean`, not `Leslie/Round.lean`:

| Protocol             | Natural model       | Why                                           |
|----------------------|---------------------|-----------------------------------------------|
| Shamir               | ActionSpec          | No network                                    |
| Bracha RBC           | ActionSpec          | Async; reacts to message arrival              |
| AVSS                 | ActionSpec          | Async; echo/ready/OK driven by reception      |
| Common coin (CR)     | ActionSpec          | Async; uses AVSS                              |
| Async BA (CR'93)     | ActionSpec          | Async                                         |
| Ben-Or (async)       | ActionSpec          | Async                                         |
| Ben-Or (sync, exists)| RoundSpec (HO)      | Existing; the deterministic over-approximation|
| OneThirdRule         | RoundSpec (HO)      | Existing; synchronous-round abstraction       |

A randomized HO model is worth having later for randomized synchronous
protocols (Feldman/Pedersen synchronous VSS, randomized ε-agreement),
but it is not on the critical path.

## Milestones

Effort estimates assume **one Leslie-fluent engineer** familiar with
Mathlib's `PMF` API. For a single engineer new to one of those, add
~40%; new to both, double. Each milestone produces a standalone
deliverable.

### M1 — Foundations + pRHL skeleton + Shamir (≈4 weeks)

**Code:** `Prob/PMF.lean`, `Prob/Action.lean`, `Prob/Embed.lean`,
`Prob/Coupling.lean` (full pRHL-style judgment, not just helpers),
`Prob/Polynomial.lean`, `Tactics/Prob.lean`
(`prob_unfold`, `by_coupling`, `coupling_identity`,
`coupling_bijection`, `coupling_swap`, `coupling_up_to_bad`,
`polynomial_uniform`),
`Examples/Prob/Shamir.lean`. Mathlib dependency added in M1 W1
(see *Mathlib dependency* above).

**Theorems:**
- Conservativity Level 2: `invariant_preserved`, `refines_preserved`
  (the easy direction; full WF1 bridge waits until M3 when the AST
  certificate exists).
- Polynomial uniformity: a uniformly random degree-`t` polynomial over
  a finite field, conditioned on `f(0) = s`, has uniform marginals at
  any `t` distinct nonzero points, independent of `s`.
- Shamir secrecy: any `t`-coalition's view is independent of the secret.
- Eager/lazy sampling commutation theorems for the swap rule.

**Why pRHL upfront, not later.** The relational shape is the right
vocabulary for *every* secrecy proof we will write. Building it now
(rather than discovering an ad-hoc version through Shamir) means AVSS
in M3 and any future computational milestone share one
well-understood core. Closer in spirit to SSProve's package-relational
approach than to raw EasyCrypt pRHL.

### M2 — Async Byzantine + bivariate Shamir (≈4 weeks)

**Code:** `Prob/Adversary.lean`, `Prob/Trace.lean`,
`Prob/Refinement.lean`, `Prob/Invariant.lean`,
`Examples/Prob/BivariateShamir.lean`, `Examples/Prob/BrachaRBC.lean`.

**Theorems:**
- Probabilistic Abadi–Lamport (`⊑ₚ`).
- Bracha RBC validity, agreement, totality (mostly reuses existing
  Leslie machinery; the *probabilistic* lifting is essentially vacuous,
  but the example forces us to nail down `Adversary`, `Trace`, and
  corruption modeling).
- Bivariate Shamir secrecy.

### M2.5 — Crypto idioms shakedown (≈2 weeks)

**Code:** `Examples/Prob/OneTimePad.lean`,
`Examples/Prob/ITMAC.lean` (information-theoretic MAC; replaces the
v1 ElGamal example).

**Goal.** Calibration milestone. Two information-theoretic examples
that exercise different parts of `Coupling.lean`:
- *One-time pad secrecy.* `coupling_bijection` workout. Trivial in
  any reasonable framework — if it's awkward, the framework is wrong.
- *Information-theoretic MAC* (e.g., Wegman–Carter style with
  pairwise-independent hashing, or even simpler: one-time MAC over a
  field). Statistical security: forgery probability `≤ 1/|F|`.
  Exercises `coupling_up_to_bad` (the "bad" event being a successful
  forgery) without requiring a negligible-function library.

**Why ElGamal is replaced.** ElGamal IND-CPA is computational. The
plan defers computational secrecy to "when a real protocol needs it"
(reasonable: AVSS is information-theoretic; Pedersen VSS is the first
example where we need DDH/discrete-log assumptions). Including ElGamal
in M2.5 would require either an axiomatized DDH (a hand-wave that
defeats the calibration purpose) or a real negligible-function layer
(which adds 2+ weeks and is misplaced before AVSS). Wegman-Carter
exercises `coupling_up_to_bad` *legitimately* in the
information-theoretic setting and is a much better calibration.

The negligible-function layer (`Prob/Negligible.lean`) is deferred
until a milestone after M5 where a computational protocol is in scope.

### M2.7 — Synchronous VSS (BGW-style, ≈3 weeks)

**Code:** `Examples/Prob/SyncVSS.lean`.

**Goal.** A *real* multi-round protocol with secrecy, correctness, and
commitment — but without the asynchrony / AST-rule overhead. This is
the natural rehearsal for M3's AVSS: same secrecy core (bivariate
Shamir), same share-distribution + complaint-resolution shape, but
deterministic 3-round termination in the synchronous broadcast model.
If the framework can verify a synchronous VSS cleanly, AVSS in M3
reduces to "add asynchrony + AST" rather than "build VSS from scratch
under asynchrony".

**Why synchronous VSS at all (not just go straight to AVSS).**
Canetti–Rabin AVSS conflates two hard things: (a) a VSS with
share/consistency/reconstruction phases, and (b) almost-sure
termination under an asynchronous adversarial scheduler. M2.7
isolates (a) on a deterministic round structure; M3 then adds (b) on
top of a now-validated VSS shape. Splitting the work also de-risks
M3 — if the certificate stub from the M3 entry gate runs into the
AST rule, we've already paid down the VSS proof cost separately.

**Protocol (BGW '88 VSS sub-protocol, n ≥ 3t+1, perfect security):**

- *Round 1 (share).* Dealer picks bivariate `F : F[x,y]` of degree
  `≤ t` in each variable with `F(0,0) = s`. Sends `f_i(y) := F(i,y)`
  and `g_i(x) := F(x,i)` to party `i`.
- *Round 2 (consistency).* Each party `i` sends `f_i(j)` to party `j`.
  Party `j` checks: `g_j(i) =? f_i(j)`. On mismatch, both broadcast
  the complaint `(i, j, value)`.
- *Round 3 (resolution).* Dealer broadcasts `F(i,j)` for each
  complained `(i,j)`. Honest parties cross-check against their own
  data; if dealer disagrees with any honest party's polynomial,
  dealer is exposed → output the default value `0`. Otherwise accept.
- *Reconstruction (any time after share completes).* Each party
  broadcasts `f_i`; honest parties run Lagrange to recover `s`.

**Theorems (synchronous VSS, n ≥ 3t+1):**
- *Termination:* deterministic — every honest party halts after
  round 3. No `FairASTCertificate`; the standard Leslie deterministic
  termination invariant suffices.
- *Correctness:* if dealer is honest with secret `s`, all honest
  outputs in reconstruction equal `s`. Lifts via Leslie
  `invariant_preserved` over the deterministic transition relation
  (PMF only on the dealer's choice of `F`).
- *Commitment:* even with corrupt dealer, after round 3 the
  reconstructed value is uniquely determined by the honest parties'
  shares (no equivocation). Pure invariant — no probabilistic
  reasoning needed.
- *Secrecy (information-theoretic):* the `t`-coalition view of the
  dealer's bivariate is independent of `F(0,0) = s`. Discharged by
  `coupling_bijection` reduction to `bivariate_evals_uniform`
  (already proved in M1).

**M2.7 deliverable.** `SyncVSS.lean`, ~700–1000 lines. The fact that
secrecy reduces to a *single* `bivariate_evals_uniform` call is the
acid test for the M1 algebraic core: if the reduction is more than
~30 lines, the framework needs cleanup before AVSS.

**Risk register.**
- *Multi-round bookkeeping.* The state machine carries 3 rounds of
  per-party messages. State-explosion risk if naive; mitigation:
  use `Finset.Iic` indexing as in `FinPrefix`, and per-round
  invariants (W2 task).
- *Complaint-resolution branching.* Round 3's honest-party logic
  has `O(n²)` branches per (i,j). Mitigation: factor into a single
  `resolveComplaints` helper with `#gen_frame_lemmas`.
- *Reusing M2 `Refines`.* Synchronous VSS is a deterministic protocol
  with one PMF (dealer's polynomial). Should embed cleanly via
  `Refines` to a "view" abstraction; if not, that's a `Refines`
  ergonomics issue worth fixing before AVSS.

**M2.7 closeout.** Open issues for any pRHL/`Refines` ergonomics
friction. Fix the top three before M3.

### M3 — AST rule + Ben-Or-async + AVSS + common coin (≈6 weeks)

**Code:** `Prob/Liveness.lean` (POPL 2025 `ASTCertificate` + POPL 2026
`FairASTCertificate` + derived rule constructors), `Prob/Secrecy.lean`,
`Examples/Prob/BenOrAsync.lean`, `Examples/Prob/CommonCoin.lean`,
`Examples/Prob/AVSS.lean`.

**M3 entry gate.** Before M3 W1, draft the AVSS certificate shape
(see *AVSS termination certificate — sketch* above) into a Lean stub
with `sorry`s — i.e., write the actual `FairASTCertificate Π_AVSS F_AVSS term`
declaration with `V`, `U`, `Inv`, `fair_actions` filled in but each
proof obligation as `sorry`. If the *shape* doesn't compile, that's a
sign the rule needs extension before AVSS can use it. This is the
1-page sketch that the reviewer asked for, in executable form.

**The AST rule, in detail.** `ASTCertificate` encodes Rule 3.2 of
Majumdar–Sathiyanarayana POPL 2025 verbatim: a likelihood
supermartingale `V`, a distance variant `U`, and sublevel-set
compatibility binding them. `FairASTCertificate` extends this with
`F : FairnessAssumptions` (a hard type-level predicate, see
*Adversary, scheduler, fairness*) so the supermartingale/variant
conditions need only hold under weakly-fair adversaries.

**Soundness of `ASTCertificate.sound`** follows the paper's proof:
partition runs by `sup_n V`, apply Doob's martingale convergence on
the diverging part to derive a contradiction (using `V`'s
non-negativity), and apply the finite-variant rule (Rule 3.1 in the
paper) on each bounded-`V` sublevel set. This requires Mathlib's
martingale convergence theorem for non-negative supermartingales — see
*Risk register*.

**Derived rule constructors.** For ergonomics, expose conventional
single-function rules as constructors that build an `ASTCertificate`:

```lean
def ofVariant     (R : σ → ℤ) ... : ASTCertificate Π term  -- McIver–Morgan
def ofRSM         (R : σ → ℝ≥0) ... : ASTCertificate Π term  -- FH 2015 + DSM
def ofParametric  (R : σ → ℝ≥0) (p d : ℝ → ℝ>0) ... : ASTCertificate Π term  -- MMKK 2018
def ofWF1Premises (Π : ActionSpec σ ι) (i : ι) ...
                    : FairASTCertificate Π.toProb F term     -- conservativity bridge
```

Each constructor reduces to the POPL 2025 theorem.

**Acceptance test for the rule.** Before any distributed example,
verify the 2-D random walker (Example 3.5 in POPL 2025) using
`ASTCertificate` directly. The 2DRW certificate uses
`V(x,y) = √(ln(1 + ‖(x,y)‖))` — this requires Mathlib analytic
machinery (logs, square roots, partial-derivative bounds). If the
Mathlib analytic imports become too heavy, the fallback is to verify
a simpler example (1-D random walker on `ℕ` with biased step) that
still requires both `V` and `U` but stays within `NNReal` arithmetic.
**M3 W2 trigger:** if 2DRW exceeds 200 lines or pulls in measure
theory beyond `MeasureTheory.Martingale`, switch to the simpler
example and document.

**Theorems (Ben-Or-async — calibration first):** termination
(almost-surely under weak fairness via `FairASTCertificate`),
agreement, validity. **Stretch goal:**
`BenOrAsync_refines_BenOrHO` — verify the existing
`Examples/BenOr.lean` is the deterministic over-approximation.

**Theorems (common coin):** with constant probability `≥ ρ`, all
honest parties output the same uniform bit.

**Theorems (AVSS, n ≥ 3t+1):**
- *Termination (AS):* via `FairASTCertificate` with the (V, U, Inv)
  sketch above — discharged into actual proofs.
- *Correctness:* if dealer honest with secret `s`, all honest outputs
  consistent with `s`. (Pure Leslie machinery, lifted via
  `invariant_preserved`.)
- *Commitment:* even with corrupt dealer, after share phase completes
  for one honest party, secret is uniquely determined.
- *Secrecy (information-theoretic):* the `t`-coalition view is
  independent of the dealer's secret. Discharged by
  `coupling_bijection` reduction to bivariate Shamir.

**M3 deliverable:** AVSS as the publishable artifact.

### M4 — UC composition (≈5 weeks)

**Code:** `UC/IdealFunc.lean`, `UC/Environment.lean`, `UC/Realize.lean`,
`UC/Compose.lean`, `UC/Hybrid.lean`, `Tactics/Prob.lean` extended.

The UC composition theorem and its three combinators
(`compose_refinement`, `compose_fair_refinement`, `compose_uc`) with
the type-level disjointness shown in *Composition combinators*.

Async UC formulation: Hirt–Maurer delivery-oracle style.

### M5 — Async BA via composition (≈4 weeks)

`Examples/Prob/AsyncBA.lean`. AVSS realizes `F_AVSS`, common coin
realizes `F_Coin`, hybrid-model BA proof, two applications of
`compose_uc`.

### M6 — Optional: probabilistic HO and probabilistic layers (≈6 weeks)

Out of scope unless a concrete randomized synchronous-round protocol
demands it.

## Open questions

1. **Adaptive corruption.** Static (M1–M5) suffices for AVSS. Adaptive
   requires care in simulator construction; defer.
2. **Computational secrecy.** Defer to a post-M5 milestone with a
   proper `Prob/Negligible.lean` layer.
3. **PAST.** Stay away. Π¹₁-complete; AST is what we need.
4. **Randomized scheduler.** v2 fixes the demonic, history-deterministic
   scheduler. Randomized schedulers are strictly more expressive
   (relevant for some quantitative analyses) but not needed for AST
   under fairness. Defer.
5. **Bidirectional WF1 ↔ AST.** v2 commits only to one direction
   (`WF1Premises_implies_AST`). Whether the converse can be stated
   meaningfully — even modulo "deterministic certificate" — is an open
   question that probably becomes interesting if a future protocol
   needs to extract a `WF1` proof from an AST certificate. Until then,
   not worth resolving.
6. **AST rule layering.** Two distinct types `ASTCertificate` /
   `FairASTCertificate` vs. unified parametric type with `F := ⊤`
   default. Recommendation: start with two types; collapse only if M3
   reveals friction.
7. **SMT vs Mathlib martingales.** Caesar (POPL 2026) uses SMT
   discharge against HeyVL. Leslie has Mathlib martingales available.
   Recommendation: option (A) — keep proof obligations first-order and
   SMT-friendly initially; switch to Mathlib martingales when a
   concrete proof needs them.

## Risk register

- **Mathlib build-time and CI cost.** *Mitigation:* `mathlib4-cache`,
  pin commit at M1 W1, advance only at milestone boundaries.
- **Mathlib analytic imports for 2DRW.** *Mitigation:* M3 W2 trigger
  to fall back to 1-D random walker if 2DRW pulls in measure theory.
- **Mathlib martingale-convergence gap.** Doob's theorem for
  non-negative supermartingales is load-bearing for
  `ASTCertificate.sound`. *Mitigation:* small shim in M3, upstream
  when stable; worst case ~200 lines from scratch.
  *Status (M0.3 outcome).* **Resolved.**
  `Submartingale.ae_tendsto_limitProcess` is in Mathlib v4.27.0; the
  AST stub at `Leslie/Prob/Spike/ASTSanity.lean` builds green with
  the full (V, U)-rule shape against the trace measure. Remaining
  shim is ~50 lines (negation, predictable filtration witness,
  sublevel-set Borel-Cantelli), not 200. See
  `docs/randomized-leslie-spike/02-ast-soundness.md`.
- **AVSS certificate shape doesn't fit POPL 2026 rule cleanly.**
  *Mitigation:* M3 entry gate requires the sketch be discharged into a
  Lean stub before AVSS work begins.
- **`ProbActionSpec` shape mismatch with future Leslie changes.** v2
  mirrors the function-indexed shape exactly, but if the `ι` discipline
  changes upstream, `Embed.lean` follows. *Mitigation:* CI conservatism
  check and the test that `ActionSpec.toProb` is one line per field.
- **pRHL ergonomics.** *Mitigation:* M2.5 calibration milestone.
- **Conservatism slippage.** *Mitigation:* CI script.
- **UC async fidelity.** *Mitigation:* commit to Hirt–Maurer; don't
  parameterize over UC variants.

## Round-2 review findings (resolve before M1)

Internal review of v2 surfaced three foundational technical issues, a
motivation gap, and a CI safety bug. Resolutions are scheduled as a
2-week M0 spike in the companion implementation plan v2.1; without
them, M1 W1 starts on uncertain foundations.

### 1. `PMF` cannot host trace distributions on infinite streams

Mathlib's `PMF α` is a discrete probability measure with countable
support. For `Trace σ ι := Stream' (σ × Option ι)` the value space is
uncountable for any non-singleton state. `PMF (Trace σ ι)` is therefore
not a real type; the M1–M2 sketches that use it (`traceDist`,
`Refines`, `RelatedTraces`) are operating on a type that does not exist.

The correct object is a measure on the cylinder σ-algebra over
`Stream' (σ × Option ι)`, constructed via Ionescu-Tulcea (kernel
composition) from the per-step `PMF`s. M0.1 spike deliverable: settle
the type and the construction in Lean against the M1 toolchain pin.

> **Status (M0.1 outcome).** **Resolved.** Option A adopted:
> per-step effects stay `PMF`; trace distributions are
> `Measure (Π n, X n)` via `Mathlib.Probability.Kernel.IonescuTulcea.Traj`
> (specifically `Kernel.trajMeasure`). Coin-flip prototype at
> `Leslie/Prob/Spike/CoinFlip.lean` (142 lines) builds green against
> Mathlib v4.27.0. No shimming required. Decision document and
> prototype outcome:
> `docs/randomized-leslie-spike/01-trace-measure.md`.
> The full type-signature sweep across §"Refinement",
> §"Coupling", §"Liveness", §"Trace" is deferred to v2.2 after M0.2
> and M0.3 close.

### 2. AST soundness pulls in measure theory on day 1 of M3

Doob's martingale convergence (load-bearing for `ASTCertificate.sound`,
per the M3 W1 plan) lives in `MeasureTheory.Martingale`. The
"discrete probability first, defer measure theory" framing is
incompatible with the headline soundness theorem. Reframe: discrete
probability is the *vocabulary* for single-step effects; measure
theory is *required* for trace-level reasoning and AST soundness.
M0.3 spike: write the soundness outline against the M0.1 trace type
before M1 starts, so the boundary is decided rather than discovered.

### 3. `parallel` state semantics are unspecified

The plan shows
`parallel : ProbActionSpec σ₁ ι₁ → ProbActionSpec σ₂ ι₂ → ProbActionSpec (σ₁ × σ₂) (ι₁ ⊕ ι₂)`
— disjoint state. Distributed protocols are not disjoint-state: they
share network buffers, message queues, and the adversary observes
both. UC composition rewires shared interfaces, which a disjoint-state
product cannot model. M0.2 spike deliverable: specify the shared-state
model (likely `σ₁ × σ_net × σ₂` with each side guarded on its half
plus the network as its own `ProbActionSpec`).

> **Status (M0.2 outcome).** **Resolved.** Shared-state product
> adopted: state is `σ₁ × σ_net × σ₂` with the network as its own
> `ProbActionSpec`; composition is action-set disjoint union
> (`ι₁ ⊕ ι_net ⊕ ι₂`) over a genuinely shared `σ_net`. This is the
> Hirt-Maurer async UC shape. Decision document and Lean shape stub
> (zero sorry):
> - `docs/randomized-leslie-spike/03-parallel-state.md`
> - `Leslie/Prob/Spike/ParallelShape.lean` (~150 lines including
>   `AsyncNet`, `composedStep`, two-party message-exchange demo)
>
> Promotion to `Leslie/Prob/Action.lean` and definition of
> `AsyncNet` for AVSS/coin/BA scheduled for M2 W1.

### 4. Motivation gap — POPL 2025 (V, U) rule justification

The plan's headline justification for the (V, U) rule is AVSS, but
the same plan admits "Canetti–Rabin AVSS itself does not toss a coin;
termination doesn't depend on probabilistic events post-share." If
termination is deterministic given fairness, then `V` is constant in
expectation and `U` (the variant) does all the work — which is the
RSM/variant rule, not the POPL 2025 two-function rule. The motivation
for choosing POPL 2025 over a simpler variant rule evaporates for
AVSS specifically.

The genuine probabilistic-AST workhorse is the **common coin**
(success probability `≥ ρ` per round, geometric decay over rounds) or
the **async BA** composition (rounds × coin). v2.1 should re-pitch the
rule's justification around those and demote AVSS to "uses the rule
for uniformity, not because the rule is required." The (V, U) sketch
in §"AVSS termination certificate — sketch" should be revisited with
this in mind: a single-counter variant rule may suffice for AVSS, in
which case the AVSS proof is simpler than v2 implied.

### 5. CI conservativity regex misses nested examples

The regex `^Leslie/Examples/[^/]+\.lean$` matches single-file examples
but not nested paths. Today on `main` this leaves
`Leslie/Examples/Combinators/`, `Leslie/Examples/Paxos/`, and
`Leslie/Examples/CacheCoherence/**` *unprotected* by the
conservatism gate. The CI safety net is silently broken for the
existing codebase shape. Fix: change to `^Leslie/Examples/.*\.lean$`
(audit the rest of the regex against `find Leslie -name '*.lean'`).
M0.4 spike task: fix and add a synthetic-diff test.

### 6. Smaller technical fixes for v2.1

- **`WF1Premises_implies_AST` with `fair_actions = {i}`** is
  operationally weak — it restricts to adversaries that fire only
  action `i`, throwing away interleaving. Either widen, or document
  why the degenerate case is what users actually want.
- **`U_dec_prob`'s `probabilistic s`** predicate has no model on
  `ProbActionSpec`: every effect is a `PMF`, some Dirac and some not,
  but the spec itself doesn't classify states. The
  pure-probabilistic vs. nondeterministic-probabilistic distinction
  needs explicit lifting.
- **`TraceRel R`** is used in `RelatedTraces.view_eq` but never
  defined.
- **AVSS secrecy via "`coupling_bijection` reduction to bivariate
  Shamir"** skips the simulator construction. The t-coalition's view
  includes network adversary scheduling; the reduction needs a
  simulator that translates network-trace adversary behavior into
  bivariate-evaluation adversary behavior. Sketch it.
- **Cross-spec adversaries for UC.** `Adversary σ ι` is per-spec but
  UC needs one physical adversary across `Π_AVSS ∥ Π_Coin`. The
  product-of-adversaries shape is not addressed.

### 7. Scope, venue, and build-vs-buy

- **Venue not stated.** "Publishable artifact" appears 3× without
  naming POPL / CAV / CCS / workshop. This determines whether
  AVSS-only (M1–M3, 16.5 weeks) is a viable end-state. Without a
  venue, the 25.5-week commitment is uncalibrated.
- **No early-validation milestone.** The first novel artifact is M3
  (16.5 weeks in). Add a "lift one existing Leslie deterministic
  protocol via `invariant_preserved` and prove something new" task
  inside M2 W4 to surface shape problems 10 weeks sooner.
- **Build vs. buy not justified.** Veil, EasyCrypt, IPDL, SSProve all
  have years of randomized + UC infrastructure. Add a one-paragraph
  build-vs-buy section: what specifically makes Leslie + Mathlib the
  right substrate vs. extending one of those?

## What success looks like

At end of M5:

- All existing files (OneThirdRule, Paxos, KVStore, the existing
  `BenOr.lean`, …) — unchanged, passing.
- A randomized layer entirely under `Leslie/Prob/` and `Leslie/UC/`.
- An end-to-end machine-checked proof of Canetti–Rabin async BA,
  factored as: AVSS realizes `F_AVSS` + coin realizes `F_Coin` +
  hybrid-model BA proof + UC composition.
- `Examples/Prob/BenOrAsync.lean` (with optional refinement to the
  existing `Examples/BenOr.lean` as a stretch goal).
- A relatively-complete AST rule used to discharge termination of
  Ben-Or-async, AVSS, common coin, and (compositionally) async BA.
- A pRHL-style relational judgment used for all secrecy proofs, with
  validated calibration on OneTimePad and Wegman–Carter MAC.
- A tactic library that makes a new probabilistic-protocol proof feel
  no harder than the deterministic ones already in `Examples/`.

## References

[Same as v1 — primary AST rules (POPL 2025, POPL 2026, POPL 2024),
earlier rules (McIver–Morgan, FH 2015, DSM OOPSLA 2019, MMKK 2018,
TACAS 2017), crypto/relational reasoning (EasyCrypt, CryptHOL,
SSProve, quantitative pRHL POPL 2025, Demonic Outcome Logic POPL 2025),
UC composition (Canetti, Hirt–Maurer), distributed protocols
(Canetti–Rabin 1993, Bracha 1987, Ben-Or 1983).]

## Changes from v1

| Concern (review #) | Resolution                                                          |
|--------------------|---------------------------------------------------------------------|
| 1. Mathlib unstated | New *Mathlib dependency* subsection with explicit accept decision. |
| 2. Shape mismatch  | `ProbActionSpec σ ι` mirrors `ActionSpec σ ι`. `P` parameter dropped. |
| 3. Existing BenOr  | New file is `BenOrAsync.lean`; relationship spelled out; refinement is a stretch goal. |
| 4. Fairness inconsistency | Fairness is a hard type predicate (`FairAdversary`). v1's "side-condition" framing dropped. |
| 5. ElGamal scope   | Replaced with `ITMAC.lean` (Wegman-Carter). Negligible-function layer deferred. |
| 6. Composition types | Five lines of Lean stub in *Composition combinators* showing `Refines` / `Realizes` / `HybridModelProof` are distinct types. |
| 7. WF1 conservativity | Narrowed to `WF1Premises_implies_AST` (one direction, action-spec level). |
| 8. AVSS certificate | New *AVSS termination certificate — sketch* subsection with V, U, Inv. M3 entry gate added. |
| 9. Helper types undefined | New *Helper types* subsection. |
| Existing-files inventory | Expanded to include AssumeGuarantee, EnvAbstraction, Simulate, SymShared, PhaseRound, Gadgets, Rust. |
| "Relatively complete" framing | Softened in design principles; metatheory framed as "soundness + library of constructors." |
| Sub-PMFs vs prefixes | Stated as a decision (infinite streams with terminal stuttering). |
| Demonic scheduler  | Stated explicitly in *Adversary, scheduler, fairness*; randomized scheduler in open questions. |
| Risk: Mathlib build | Added. |
| Risk: 2DRW imports | Promoted from open question to risk. |
| Timeline staffing  | Made explicit: estimates assume Leslie+Mathlib-fluent engineer; +40% to 2× for less-fluent staffing. |

## Changes from v2.1

| Topic | v2.2 update |
|---|---|
| Design principle 2 | "Discrete probability first" softened to "PMF for single steps, Measure for traces." Mathlib's measure-theoretic stack is no longer hidden — AST soundness needs Doob, which is measure-theoretic. M0.1 outcome. |
| `traceDist` | Signature updated from `PMF (Trace σ ι)` (which doesn't exist for non-trivial state) to `Measure (Π n : ℕ, σ × Option ι)` via `ProbabilityTheory.Kernel.trajMeasure`. Adds `[MeasurableSpace σ] [MeasurableSpace ι]` requirements and an explicit initial-distribution argument `μ₀ : Measure σ`. M0.1 outcome. |
| `Refines` (`⊑ₚ`) | Updated to quantify over an initial distribution `μ₀` and use `Measure.map` instead of `PMF`. Same shape, lifted to measures. |
| `RelatedTraces.view_eq` | Trace-level coupling expressed as `Measure.map` equality; step-level coupling stays PMF-flavored. Bridge is `Kernel.traj`'s functoriality. |
| `ASTCertificate.sound` / `FairASTCertificate.sound` | Conclusion expressed against `traceDist Π A μ₀` as `∀ᵐ ω, ∃ n, term (ω n).1`. The placeholder `□̃`/`◇̃` modal notation is replaced with the underlying measure-theoretic almost-everywhere quantifier; M3 W1 may reintroduce notation. |
| `parallel` shape | Round-2 finding 3 status: shared-state product `σ₁ × σ_net × σ₂` adopted, network is its own `ProbActionSpec`. Disjoint-state `(σ₁ × σ₂)` rejected. Lean stub: `Leslie/Prob/Spike/ParallelShape.lean`. M0.2 outcome. |
| §"Risk register" Mathlib martingale gap | Marked Resolved — Mathlib already has Doob; shim is ~50 lines, not 200. |
| §"Round-2 review findings" | Each of findings 1, 2, 3 carries a "Status" box pointing at the resolved spike artifact. |
| Spike artifact tree | New: `docs/randomized-leslie-spike/01-trace-measure.md`, `02-ast-soundness.md`, `03-parallel-state.md`; `Leslie/Prob/Spike/{CoinFlip,ASTSanity,ParallelShape}.lean`; `scripts/check-conservative.sh` + `.test.sh`; `.github/workflows/conservativity.yml`. |
| Critical-path estimates | Unchanged: AVSS 18.5 weeks, async BA 27.5 weeks. M0 actual elapsed: <1 day vs. 2-week budget. |
