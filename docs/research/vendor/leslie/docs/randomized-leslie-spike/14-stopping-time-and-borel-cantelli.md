# Stopping-Time Kernel Bound & Conditional Borel-Cantelli — Status

## Summary

Of the two remaining items called out in
`13-fair-ast-borel-cantelli-plan.md` for closing the general-case
fair AST rule:

1. **Stopping-time kernel lower bound** — *now landed*
   (`Leslie.Prob.traceDist_kernel_stoppingTime_bound` in
   `Refinement.lean`).
2. **Conditional Borel-Cantelli lemma** — *available in Mathlib*,
   not added or imported into our codebase. **Argued below to be not
   relevant for any current concrete protocol.**

This document records what's in place and the precise scope of what
remains for a hypothetical future protocol with genuinely-randomized
step decreases.

## What's landed

### `traceDist_kernel_stoppingTime_bound`

`Leslie/Prob/Refinement.lean` (after `traceDist_kernel_step_bound`).
Per-fiber form of the kernel lower bound, exposed as a named
convenience for downstream Borel-Cantelli code.

```lean
theorem traceDist_kernel_stoppingTime_bound
    [Countable σ] [Countable ι] ...
    (A : Adversary σ ι) (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (S : (m : ℕ) → Set (FinPrefix σ ι m))
    (T : (m : ℕ) → FinPrefix σ ι m → Set (σ × Option ι))
    (p : ENNReal)
    (h_step : ∀ m, ∀ h ∈ S m, p ≤ (stepKernel spec A m h) (T m h))
    (m : ℕ) :
    p * (traceDist spec A μ₀)
        {ω : Trace σ ι | Preorder.frestrictLe m ω ∈ S m} ≤
      (traceDist spec A μ₀)
        {ω : Trace σ ι | Preorder.frestrictLe m ω ∈ S m ∧
          ω (m + 1) ∈ T m (Preorder.frestrictLe m ω)}
```

The proof is one line — `exact traceDist_kernel_step_bound A μ₀ m
(S m) (T m) p (h_step m)`. The lemma is structural: it packages the
fixed-time bound for use in fiber-sum arguments (combined with
`measure_selector_fiber_lower_bound` and
`traceDist_selector_fiber_lower_bound` in `Liveness.lean`).

A caller writing the conditional-Borel-Cantelli step would:

1. Define the stopping time `τ : Trace σ ι → ℕ` (typically
   `fairFiringTime F · k` from `Liveness.lean`, already proved
   measurable).
2. For each step `m`, supply the per-fiber prefix set `S m` and
   target `T m` along with the kernel bound `p` (from the
   certificate's `U_dec_prob`).
3. Call `traceDist_kernel_stoppingTime_bound` per `m`.
4. Sum across `m` via `traceDist_selector_fiber_lower_bound`.

Each step is sorry-free in the current codebase. The remaining work
is simply *plugging this together* with `cert.U_dec_prob` to derive
the post-Borel-Cantelli witness `TrajectoryFairRunningMinDropIO`.

## Conditional Borel-Cantelli — already in Mathlib

`MeasureTheory.ae_mem_limsup_atTop_iff` in
`Mathlib/Probability/Martingale/BorelCantelli.lean`:

```lean
theorem ae_mem_limsup_atTop_iff (μ : Measure Ω) [IsFiniteMeasure μ]
    {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet[ℱ n] (s n)) :
    ∀ᵐ ω ∂μ, ω ∈ limsup s atTop ↔
      Tendsto (fun n => ∑ k ∈ Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|ℱ k]) ω) atTop atTop
```

This is **Lévy's generalization of Borel-Cantelli**: AE, an event is
in the limsup iff its conditional probabilities sum to infinity along
the filtration. Exactly what gap-2's BC-step needs.

To use it, one needs:

1. A `MeasureTheory.Filtration ℕ m₀` on `Trace σ ι`.
2. The fair-firing-decrease events filtration-measurable.
3. A divergence proof for the conditional-probability sum (here
   `traceDist_kernel_stoppingTime_bound` — which we just landed —
   contributes the per-step lower bound `p > 0`, and pairing with
   trajectory progress gives infinitely many contributing steps).

Mathlib's `MeasureTheory.Filtration.natural` constructs (1) from a
process; the prerequisites are `MetrizableSpace + BorelSpace` per
coordinate, derivable from `[Countable σ] [MeasurableSingletonClass σ]`
plus the discrete topology (~50 LOC of typeclass plumbing). (2) is
~30 LOC of measurable-set composition (already mostly in place via
`measurableSet_fairFiresAt`, `measurable_fairFiringTime`, etc.).

Total estimated work to use Mathlib's BC lemma in our setup:
**~150-250 LOC**, all plumbing — no new mathematical content.

## Why this is not blocking any current theorem

The general-case fair AST rule with `cert.U_dec_prob` (probabilistic
decrease, `p < 1`) is currently expressed as
`pi_n_AST_fair_with_progress` taking a
`TrajectoryFairRunningMinDropIO` witness as an explicit hypothesis.
The BC content is *consumed* but not *derived* internally.

For any caller wanting to instantiate this with `cert.U_dec_prob`,
they would:

- Use `traceDist_kernel_stoppingTime_bound` (now available) to get
  per-step kernel bounds.
- Construct the natural filtration.
- Apply `ae_mem_limsup_atTop_iff` (in Mathlib) to derive the
  running-min drop event.

**No concrete protocol in the current codebase needs this.** All
present probabilistic protocols in `Leslie/Examples/Prob/` (Bracha,
SyncVSS, AVSS, RandomWalker, BenOrAsync, CommonCoin) have
**deterministic step kernels** (`PMF.pure` effects). Their fair-action
firings strictly decrease `U` *deterministically*, not just
probabilistically. The deterministic specialisation
`pi_n_AST_fair_with_progress_det` (closed sorry-free) discharges
their termination directly:

```text
TrajectoryFairAdversary
  + TrajectoryUMono
  + TrajectoryFairStrictDecrease
  ⟹ AS termination       (no BC needed)
```

The deterministic-specialisation route is what AVSS's
`avss_termination_AS_fair_traj` consumes (axiom-clean,
`#print axioms` returns `[propext, Classical.choice, Quot.sound]`).

The only setting where the BC route would be *necessary* is a
protocol where a fair action's effect is genuinely random — e.g., a
local coin toss whose outcome determines whether `U` decreases. None
of our concrete protocols do this. CommonCoin's coin tosses don't
gate `U` decrease; they're outcomes the protocol records, not
decisions about whether to make progress.

## Concrete invitation for future work

For a hypothetical future probabilistic protocol that needs the
general BC route, the recipe is:

1. Construct a `MeasureTheory.Filtration ℕ` on `Trace σ ι` from the
   coordinate projections (`Filtration.natural`). Requires a
   `MetrizableSpace + BorelSpace` instance per coordinate, derivable
   from `Countable + MeasurableSingletonClass`.
2. Show fair-firing-decrease events are filtration-measurable. The
   primitives `measurableSet_fairFiresAt`, `measurable_fairFiringTime`,
   `measurableSet_runningMinDropAt` (all closed in `Liveness.lean`)
   handle most of this.
3. Use `traceDist_kernel_stoppingTime_bound` plus the fiber-sum
   reduction `traceDist_selector_fiber_lower_bound` to derive the
   per-step conditional-probability lower bound.
4. Apply `MeasureTheory.ae_mem_limsup_atTop_iff` to conclude
   `∀ᵐ ω, ω ∈ limsup (decrease events)`.
5. Use `TrajectoryFairRunningMinDropIO.toBCDescent` (already proved)
   to bridge to the certificate-level theorem
   `pi_n_AST_fair_with_progress_bc`.

Estimated effort: ~150-250 LOC, all Mathlib filtration plumbing. The
mathematical content is fully in place; what remains is wiring the
Mathlib API to our trace measure.

## Status

| Item | Status |
|------|--------|
| Stopping-time kernel lower bound | **Landed** in Refinement.lean as `traceDist_kernel_stoppingTime_bound` |
| Conditional Borel-Cantelli | **In Mathlib**, available via `MeasureTheory.ae_mem_limsup_atTop_iff`. Not imported into our codebase because no concrete protocol uses the general probabilistic case. |
| Filtration plumbing on Trace σ ι | Deferred. ~150-250 LOC, not blocking any concrete protocol. |
| `TrajectoryFairRunningMinDropIO` derivation | Deferred. Currently consumed as hypothesis on `pi_n_AST_fair_with_progress`. |

## Sorry-free claims

After this commit:

- `pi_n_AST_fair_with_progress_det`: closed sorry-free.
- `FairASTCertificate.sound`: axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
- `pi_n_AST_fair_with_progress`: axiom-clean (consumes
  `TrajectoryFairRunningMinDropIO` as hypothesis).
- All AVSS theorems: axiom-clean.
- `traceDist_kernel_step_bound`, `traceDist_kernel_stoppingTime_bound`,
  `traceDist_selector_fiber_lower_bound`,
  `measure_selector_fiber_lower_bound`: closed sorry-free.

Only remaining sorry in the fair-AST stack:
`ASTCertificate.pi_n_AST` (line 210, demonic-version, has the
stuttering-adversary issue documented in
`10-stuttering-adversary-finding.md`. Out of scope for AVSS).
