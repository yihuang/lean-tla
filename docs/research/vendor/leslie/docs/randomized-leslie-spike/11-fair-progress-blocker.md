# M3 W3 finding — `pi_n_AST_fair` has *two* stacked gaps, not one

The earlier W2 brief on stuttering (`10-stuttering-adversary-finding.md`)
correctly identified that the *demonic* `ASTCertificate.pi_n_AST` is
provably false for stuttering adversaries and that the *fair* version
sidesteps this by virtue of `FairAdversary`'s fairness witness.

What the W2 brief did NOT spell out: **the fair version's witness is
opaque**, so even though the type signature rules out always-stutter,
the trajectory-level fairness statement needed by the proof can't be
extracted from `F.isWeaklyFair`.

Closing `pi_n_AST_fair` in the foreground revealed this second gap.

## The two gaps, explicitly

### Gap 1 — Trajectory-progress witness is unextractable

`Leslie/Prob/Adversary.lean`:

```lean
structure FairnessAssumptions (σ : Type*) (ι : Type*) where
  fair_actions : Set ι
  isWeaklyFair : Adversary σ ι → Prop  -- OPAQUE
```

`isWeaklyFair` is a `Prop`-valued predicate with no structure: it
gives no way to derive *any* trajectory-level statement about the
adversary's behavior. In particular, it does not provide:

> AE on the trace measure, every fair-required action fires
> infinitely often.

That's the actual statement the `pi_n_AST_fair` proof needs.

**Symptom**: the concrete fairness instances in our codebase use
the trivial placeholder:

```lean
-- BrachaRBC.lean
def brbFair (...) : FairnessAssumptions ... where
  fair_actions := Set.univ
  isWeaklyFair := fun _ => True   -- placeholder

-- BenOrAsync.lean, AVSSStub.lean: same
```

So `A.fair : F.isWeaklyFair A.toAdversary` is `True`, supplying no
information. The `pi_n_AST_fair` proof's first step ("from
`A.fair`, fair actions fire i.o.") cannot be discharged.

### Gap 2 — Mathlib Borel–Cantelli + filtration plumbing

Even *with* a trajectory-progress witness, the geometric-tail
argument requires:

1. The natural filtration on `Trace σ ι` (σ-algebra of the first
   `n+1` coordinates).
2. Conditional Borel–Cantelli (`MeasureTheory.ae_mem_limsup_atTop_iff`)
   threading `cert.U_dec_prob`'s per-step bound.
3. Combining with `U_bdd_subl` to derive the `M`-step termination
   bound.

This is the same gap blocking the demonic `pi_n_AST`. Estimate per
the W2 deep-fill agent: ~250 LOC of measure-theoretic plumbing.

## What landed

Foreground commit (this branch, after `b0c75f9`): a
`TrajectoryFairProgress` predicate exposing gap 1 cleanly, plus a
parameterized `pi_n_AST_fair_with_progress` that takes the
trajectory-progress witness as an explicit hypothesis. Both still
sorry'd (gap 2 remains), but the gap structure is now visible:

```lean
def TrajectoryFairProgress (spec : ProbActionSpec σ ι)
    (F : FairnessAssumptions σ ι)
    (_cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F) : Prop :=
  ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
    ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i

theorem pi_n_AST_fair_with_progress
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F)
    (_h_progress : TrajectoryFairProgress spec F cert μ₀ A)
    (N : ℕ) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  sorry  -- gap 2: Borel-Cantelli + filtration plumbing
```

## Resolution paths

### Gap 1 (trajectory-progress)

Three options (in order of preference):

**1a. Refactor `FairnessAssumptions` to require a witness.**

```lean
structure FairnessAssumptions (σ : Type*) (ι : Type*) where
  fair_actions : Set ι
  isWeaklyFair : Adversary σ ι → Prop
  /-- Trajectory-form fairness witness: under any adversary
  certified weakly fair, fair-required actions fire AE i.o. on
  the trace measure of any spec/μ₀. -/
  weak_fair_witness : ∀ (spec : ProbActionSpec σ ι)
      (A : Adversary σ ι), isWeaklyFair A →
      ∀ (μ₀ : Measure σ) [IsProbabilityMeasure μ₀],
        ∀ᵐ ω ∂(traceDist spec A μ₀),
          ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ fair_actions, (ω (n+1)).2 = some i
```

Cost: every concrete `FairnessAssumptions` instance must supply
this witness. `BrachaRBC`, `BenOrAsync`, `AVSSStub` currently use
`True`; they'd need real fairness predicates. The witness is
exactly what M3 W3+ proofs use, so this is honest accounting.

The witness is universally quantified over `spec` and `μ₀` to
avoid circularity with the trace measure. Concrete protocols
typically prove it from a **schedule-level** fairness predicate
(`isWeaklyFair := A.schedule satisfies "fair-required actions
fire eventually whenever continuously enabled"`).

**1b. Take the witness as a hypothesis on `pi_n_AST_fair`.**

What we just landed (`pi_n_AST_fair_with_progress`). Less
disruptive but pushes the obligation to every caller.

**1c. Define a `TrajectoryFair` subtype** of `FairAdversary` that
bundles the witness:

```lean
structure TrajectoryFairAdversary ... where
  toFair : FairAdversary σ ι F
  progress : TrajectoryFairProgress ... toFair
```

Concrete protocols then construct `TrajectoryFairAdversary`
instances directly. Less invasive than 1a; more uniform than 1b.

### Gap 2 (Borel-Cantelli + filtration)

This is pure Mathlib plumbing — estimated ~250 LOC. The shape of
the proof is the standard textbook "geometric tail bound for
positive-probability decrease + bounded variant ⇒ AS termination."
Mathlib has the ingredients
(`MeasureTheory.measure_eq_zero_of_summable_indicator`,
`ENNReal.tsum_geometric_lt_top`,
`MeasureTheory.ae_mem_limsup_atTop_iff`); the missing piece is the
assembly + the natural filtration on `Trace σ ι` from coordinate
projections.

A natural place for this assembly is a new module
`Leslie/Prob/Liveness/BorelCantelli.lean` (or similar) that
packages the geometric-tail argument generically and is consumed
by both `pi_n_AST` and `pi_n_AST_fair_with_progress`.

## Status of `pi_n_AST_fair` callers

`partition_almostDiamond_fair` and `FairASTCertificate.sound` are
**closed** transitively against `pi_n_AST_fair`'s sorry. So the
fair-soundness story has the right *shape* and works on day-1
calibration tests (`BenOrAsync.lean`); only the chain
`pi_n_AST_fair → partition → sound → AVSS termination` is sorry'd
end-to-end on the load-bearing finite-variant rule.

Closing both gaps unblocks AVSS termination (M3 W5–W6) and
`BrachaRBC.totality` (transitively, modulo the orthogonal
`AlmostDiamond_of_leads_to` bridge for `↝`-style statements).

## Recommended next step

Address gap 1 via option 1c (subtype with witness) — it's the
least disruptive and gives concrete protocols a clean target. Pair
with a focused Mathlib-side push on gap 2's Borel–Cantelli
assembly. Expected effort: ~1 week each. Both are deferred from
M3 W3 to M3 polish.
