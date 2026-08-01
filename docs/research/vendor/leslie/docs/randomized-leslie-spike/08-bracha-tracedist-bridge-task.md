# M2 W3 polish — close the `AlmostBox_of_pure_inductive` bridge

`Leslie/Examples/Prob/BrachaRBC.lean` carries 4 sorries from the M2 W3
structural commit (5422f63). Three of them depend on the **same**
missing helper in `Leslie/Prob/Refinement.lean`; the fourth needs a
liveness counterpart that's already on the M3 critical path.

This brief is for closing those four sorries.

## Repository state at task start

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `feat/randomized-leslie-m2-w3` (already checked out)
- PR: #27 (stacked on PR #26)
- Mathlib v4.27.0
- Build: `lake build`
- Per-file: `lake env lean Leslie/Examples/Prob/BrachaRBC.lean`
- Conservativity gate: `bash scripts/check-conservative.sh` (currently OK at 30 files)

## The four sorries

| Line | Theorem                              | Blocker                                           |
|------|--------------------------------------|---------------------------------------------------|
| 520  | `brbProb_budget_AS`                  | `AlmostBox_of_pure_inductive` (missing helper)    |
| 547  | `brbProb_validity_AS`                | same                                              |
| 578  | `brbProb_agreement_AS`               | same                                              |
| 627  | `brbProb_totality_AS_fair`           | `AlmostDiamond_of_leads_to` (missing helper)      |

## Goal

Add two helpers to `Leslie/Prob/Refinement.lean` and close all four
Bracha sorries.

### Helper 1 — `AlmostBox_of_pure_inductive`

**Intuition.** When every action's effect is a Dirac
(`PMF.pure (det_step a s)`), the per-step kernel `stepKernel spec A n`
collapses to a deterministic `Kernel.deterministic`. The trajectory
measure becomes a Dirac on the unique trace produced by iterating
the deterministic kernel from the initial state. AE-truth on a Dirac
collapses to truth at the unique trajectory point, and a deterministic
inductive invariant transfers immediately.

**Statement (target shape):**

```lean
theorem AlmostBox_of_pure_inductive
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (P : σ → Prop)
    (det_step : ι → σ → σ)
    (h_pure : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        (spec.actions i).effect s h = PMF.pure (det_step i s))
    (h_step : ∀ (i : ι) (s : σ),
        (spec.actions i).gate s → P s → P (det_step i s))
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, P s)
    (A : Adversary σ ι) :
    AlmostBox spec A μ₀ P
```

Note the `h_init` form is `∀ᵐ s ∂μ₀, P s` rather than the
`μ₀ {s} ≠ 0 → P s` shape currently used in BrachaRBC.lean. After
adding the helper, also adjust the four BrachaRBC theorems'
`h_init` parameters to match (it's a strictly cleaner phrasing
that's compatible with `IsProbabilityMeasure μ₀` and the AE
formulation).

**Proof outline.**

1. `traceDist spec A μ₀ = Kernel.trajMeasure (μ₀.map (·, none)) (stepKernel spec A)`
   — by definition of `traceDist`.

2. By induction on `n`, prove the n-step marginal of `traceDist`
   satisfies an inductive invariant:

   ```
   ∀ n, ∀ᵐ ω ∂traceDist spec A μ₀, P (ω n).1
   ```

   - `n = 0`: the 0-th coordinate of `Kernel.trajMeasure` equals
     `μ₀.map (·, none)`'s first projection, which is `μ₀`.
     `h_init` finishes.
   - `n+1`: the `(n+1)`-th coordinate is the `stepKernel` of the
     n-th coordinate. With `h_pure`, this kernel becomes a Dirac
     on either `(det_step i s, some i)` (gated branch) or
     `(s, none)` (stutter branch). In either case the first
     projection is either `det_step i s` (preserved by `h_step`)
     or `s` (vacuously preserved). Combine the two cases with the
     inductive hypothesis.

3. `AlmostBox` unfolds to `∀ᵐ ω ∂(traceDist spec A μ₀), ∀ n, P (ω n).1`.
   The countable-AE swap (`∀ᵐ ω, ∀ n, P (ω n).1 ↔ ∀ n, ∀ᵐ ω, P (ω n).1`)
   plus step 2 finishes.

The countable-AE swap is `MeasureTheory.ae_all_iff` (Mathlib).
The n-step marginal extraction will likely need
`Mathlib.Probability.Kernel.IonescuTulcea.Traj` lemmas — search
for `Kernel.trajMeasure` and `Kernel.partialTraj` in Mathlib.

**Estimated effort:** 80–150 lines (most of it extracting marginals).

### Helper 2 — `AlmostDiamond_of_leads_to`

**Intuition.** Same idea but for liveness: from a deterministic
leads-to under fairness, lift to `AlmostDiamond` under the
adversary fairness in `FairAdversary`.

**Status.** Lower priority than Helper 1 because:
- The deterministic upstream `totality` itself is currently broken
  (24 errors in `ByzantineReliableBroadcast.lean`'s liveness
  section, see "Upstream cleanup" below).
- The cleanest formulation depends on `FairASTCertificate`, which
  is M3 W1 work.

Recommended order: close Helper 1 first (closes 3 of 4 sorries),
then defer Helper 2 to M3 W1 alongside `FairASTCertificate`.

## Closing the four Bracha sorries

After Helper 1 lands, each of `brbProb_budget_AS`,
`brbProb_validity_AS`, `brbProb_agreement_AS` becomes:

```lean
  refine AlmostBox_of_pure_inductive
    (P := <the predicate>)
    (det_step := brbStep n f Value)
    (h_pure := <by simp [brbProb]>)
    (h_step := <inductive step>)
    μ₀ ?_ A
  · -- a.e. initial: from h_init via ae_iff_dirac or similar
    sorry  -- adjust h_init phrasing
```

For `brbProb_budget_AS` the inductive step is `brbStep_preserves_budget`
(already proved at §5.1). For validity/agreement, the inductive steps
need the `brb_inv` content from upstream `ByzantineReliableBroadcast`.

For totality (after Helper 2 lands), the body translates upstream
`totality`'s leads-to chain into the `AlmostDiamond` formulation.

## Upstream cleanup (independent task)

`Leslie/Examples/ByzantineReliableBroadcast.lean` (main-branch code,
not in any import graph because of the errors) has **24 compile errors**
in its liveness section (lines 1611+). All are `rw` failures from a
`Nat` simp-normal-form change in Lean 4.27 / mathlib v4.27.0:
`0 + (k' + 1)` is now normalized to `k' + 1 + 0`. The fix is mechanical
(1 line per site) — change each `rw [show 0 + (k' + 1) = ... from …]`
to match the new normal form. Sites: `stable_or_corrupt`,
`corrupt_persistent`, `voteRecv_list_stable`, `voted_stable`,
`sent_stable`, `returned_stable`, `countVoteRecv_stable`,
`voteRecv_persist`, `vote_msg_tracking`, `wf_*` (full list via
`grep -n "rw \[show 0" Leslie/Examples/ByzantineReliableBroadcast.lean`).

Once fixed, `BrachaRBC.lean` can drop its local redeclarations of
`MsgType`/`Message`/`LocalState`/`State`/`Action`/etc. and just
`import Leslie.Examples.ByzantineReliableBroadcast`. Net savings:
~150 lines in BrachaRBC.lean.

This is independent of the Helper 1 work; can be done in parallel.

## Constraints

1. **Allowed paths**: `Leslie/Prob/Refinement.lean` (target for
   Helper 1), `Leslie/Examples/Prob/BrachaRBC.lean` (sorry-fillers),
   `docs/randomized-leslie-spike/` (notes). Do NOT touch other
   `Leslie/Prob/*` files unless absolutely necessary — keep the
   helper localized to `Refinement.lean`.
2. **No new dependencies** in `lakefile.lean`.
3. **Don't push** to origin.

## Acceptance

- `lake build`: green; same 4 pre-existing project sorries unchanged
  (Refinement.lean ×2, LastVoting.lean ×2). New sorries in
  `BrachaRBC.lean` should drop from 4 → 1 (totality only).
- `bash scripts/check-conservative.sh`: passes.
- `lake env lean Leslie/Examples/Prob/BrachaRBC.lean`: green.
- One commit on `feat/randomized-leslie-m2-w3`.

## Branch state at task start

```
5422f63 feat(M2 W3): probabilistic Bracha RBC — ProbActionSpec + safety statements
44b94d2 docs(M2.7): add synchronous VSS (BGW-style) milestone
2a8a030 feat(M2 W2 polish): close Refines.comp + Refines_safe — 0 sorries
2d5066d feat(M2 W2 polish): real schedule-and-gate-conditional stepKernel
... (older commits)
```

Sorries on `Leslie/Examples/Prob/BrachaRBC.lean`: 4 (budget,
validity, agreement, totality).
Sorries on `Leslie/Prob/Refinement.lean`: 0.
Sorries on `Leslie/Prob/Trace.lean`: 0.

## Reference

- `Leslie/Prob/Refinement.lean` — target for Helper 1.
- `Leslie/Prob/Trace.lean` — `traceDist` body, `stepKernel`,
  Markov-kernel instance.
- `Leslie/Examples/Prob/BrachaRBC.lean` — the four sorries.
- `Leslie/Examples/ByzantineReliableBroadcast.lean` — upstream
  deterministic Bracha; broken in the liveness section, see
  "Upstream cleanup".
- `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` — the
  Ionescu-Tulcea trajectory; needed for n-step marginal extraction
  in Helper 1.
- `Mathlib/MeasureTheory/Measure/AE.lean` —
  `MeasureTheory.ae_all_iff` for the countable-AE swap.
