# M2 W3 polish (continued) — close `Kernel.trajMeasure_marginal_succ`

After commit `bc9af4b`, the remaining structural gap blocking the
BrachaRBC AlmostBox closures is **inside** the helper
`AlmostBox_of_pure_inductive` body (in `Leslie/Prob/Refinement.lean`,
line 225). The helper signature is pinned down (the BrachaRBC budget
proof now applies it via a one-liner); only the body's induction step
needs an n-step marginal lemma for `Kernel.trajMeasure` that
Mathlib v4.27.0 does not expose in directly usable form.

This brief is for closing that single sorry.

## Repository state at task start

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `feat/randomized-leslie-m2-w3` (commit `bc9af4b` or later)
- Mathlib v4.27.0
- Build: `lake build`
- Per-file: `lake env lean Leslie/Prob/Refinement.lean`
- Conservativity gate: `bash scripts/check-conservative.sh` (OK at 31 files)

## The sorry

`Leslie/Prob/Refinement.lean:225` —
`AlmostBox_of_pure_inductive`'s body. Documented at
`Leslie/Prob/Refinement.lean:181` (section header).

Once this closes, three downstream sorries close transitively:

- `Leslie/Examples/Prob/BrachaRBC.lean:520` — `brbProb_budget_AS`
  (already a one-line `exact AlmostBox_of_pure_inductive ...`,
  so transitive closure is immediate).
- `Leslie/Examples/Prob/BrachaRBC.lean:556` — `brbProb_validity_AS`
  (additionally needs a ported `local_consistent` invariant from
  upstream `brb_inv` conjunct 6).
- `Leslie/Examples/Prob/BrachaRBC.lean:588` — `brbProb_agreement_AS`
  (additionally needs `brb_inv` conjuncts 7–9 + echo-quorum-
  intersection lemma).

Note: with PR #28 merged into main, `BrachaRBC.lean` can also be
refactored to drop its local redeclarations and
`import Leslie.Examples.ByzantineReliableBroadcast`. Validity and
agreement then reduce to one-liners against upstream `brb_inv`.

`brbProb_totality_AS_fair` (line 636) blocks separately on
`AlmostDiamond_of_leads_to`; that's M3 W1 work.

## The missing Mathlib lemma

Target shape (informal):

```lean
theorem Kernel.trajMeasure_marginal_succ
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] [IsProbabilityMeasure μ₀]
    (n : ℕ) :
    (Kernel.trajMeasure μ₀ κ).map (fun ω => ω (n + 1)) =
      (Kernel.trajMeasure μ₀ κ).map (fun ω => ω n) >>= ?_
      -- where the bind is through the kernel applied to the right history.
```

The exact form depends on which kind of n-step marginal is most useful
to consumers. The agent's note says this is derivable from existing
Mathlib lemmas (`map_traj_succ_self` plus
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`) in roughly
80 lines.

## Suggested workflow

1. Look at `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`. Grep
   for `map_traj_succ_self` and study its usage.
2. Try to derive the single-coordinate marginal recurrence directly
   from the joint-marginal lemma
   `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`.
3. With that, the body of `AlmostBox_of_pure_inductive` becomes a
   countable-AE swap (`MeasureTheory.ae_all_iff`) plus an induction
   on `n` using the marginal recurrence.
4. The deterministic-step preservation (`h_step`) closes the inductive
   step by reasoning about `PMF.toMeasure_pure` (`(PMF.pure x).toMeasure
   = Measure.dirac x`), so the kernel pushforward at each step is a
   Dirac and the AE-truth transports.

## Constraints

1. **Allowed paths**: `Leslie/Prob/Refinement.lean` (the helper body),
   `docs/randomized-leslie-spike/`. Other files only if absolutely
   necessary (e.g., a small helper in `Leslie/Prob/Trace.lean` if it
   stabilizes the proof).
2. No new dependencies in `lakefile.lean`.
3. Don't push to origin.
4. Do not regress `Leslie/Prob/Refinement.lean`'s sorry count past 1
   during the work; final state must be 0.

## Acceptance

- `lake env lean Leslie/Prob/Refinement.lean`: 0 sorries.
- `lake build Leslie.Examples.Prob.BrachaRBC` (or `lake build`): green.
- `lake env lean Leslie/Examples/Prob/BrachaRBC.lean`: at most 3 sorries
  remaining (validity, agreement, totality), down from current 3
  (the budget proof closes automatically).
- If you also wire validity / agreement to use upstream `brb_inv`
  (after PR #28's BRB fix lands on main), even better — that drops
  BrachaRBC sorries to 1 (totality only).
- `bash scripts/check-conservative.sh`: passes.
- One commit on `feat/randomized-leslie-m2-w3` describing the
  derivation.

## Branch state at task start

```
bc9af4b feat(M2 W3 polish): AlmostBox_of_pure_inductive bridge + close brbProb_budget_AS
0f5d648 docs(M2 W3 polish): brief for AlmostBox_of_pure_inductive bridge
5422f63 feat(M2 W3): probabilistic Bracha RBC — ProbActionSpec + safety statements
44b94d2 docs(M2.7): add synchronous VSS (BGW-style) milestone
... (older)
```

Sorries on `Leslie/Prob/Refinement.lean`: 1 (helper body).
Sorries on `Leslie/Examples/Prob/BrachaRBC.lean`: 3
(validity, agreement, totality).
Sorries on `Leslie/Prob/Trace.lean`: 0.

## Reference

- `Leslie/Prob/Refinement.lean` — target (line 225).
- `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` — the
  Ionescu-Tulcea trajectory and joint-marginal lemma.
- `Mathlib/MeasureTheory/Measure/AE.lean` —
  `MeasureTheory.ae_all_iff` for the countable-AE swap.
- `Mathlib/Probability/ProbabilityMassFunction/Basic.lean` —
  `PMF.toMeasure_pure` for Dirac form.
- `docs/randomized-leslie-spike/08-bracha-tracedist-bridge-task.md`
  — the original brief, now superseded for the budget closure but
  still relevant for validity / agreement / totality TODOs.
