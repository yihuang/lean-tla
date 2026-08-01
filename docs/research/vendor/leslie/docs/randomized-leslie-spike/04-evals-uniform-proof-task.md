# M1 W3 polish task — close `evals_uniform`

> **Status: ✅ landed in commit `c8ad591`** ("feat(M1 W3): close
> evals_uniform — algebraic core of Shamir secrecy"). The follow-up
> task for `bivariate_evals_uniform` (originally noted below as
> "deferred to M2") also landed, in commit `1eb647e`. This document
> is retained as the historical briefing.

This document is the briefing for the focused proving session that
closed the deferred `sorry` in `Leslie/Prob/Polynomial.lean`'s
`evals_uniform`. It captures the proof strategy mapped out, the
exact Mathlib lemmas used, and the acceptance criteria.

## Goal

Prove `evals_uniform` without `sorry`. The statement is fixed; do
not change the public signature except as noted (you may add
hypotheses if necessary, but propagate them to callers in
`Leslie/Examples/Prob/Shamir.lean`).

```lean
theorem evals_uniform (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card ≤ d) (h_nz : (0 : F) ∉ pts) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F)
```

`bivariate_evals_uniform` was originally permitted to remain
`sorry` (deferred to M2 per implementation plan v2.2 §M1 W3). It
has since been closed in commit `1eb647e` via row-then-column
reduction; see `docs/randomized-leslie-spike/05-bivariate-evals-uniform-task.md`.

## Repository state

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `randomized-leslie` (already checked out; do not switch)
- Mathlib v4.27.0 already in `lakefile.lean`
- Build: `lake build Leslie.Prob.Polynomial`
- Full project: `lake build`
- Conservativity gate: `bash scripts/check-conservative.sh`
  (must show "Conservative-extension check: OK ...")

## Setup context

`uniformWithFixedZero d s` is defined as:
```lean
noncomputable def uniformWithFixedZero (d : ℕ) (s : F) : PMF (Polynomial F) :=
  (PMF.uniform (Fin d → F)).map fun coefs =>
    Polynomial.C s + ∑ i : Fin d,
      Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)
```

Helper already proved (use it):
```lean
theorem PMF.uniform_map_of_bijective
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {f : α → β} (hf : Function.Bijective f) :
    (PMF.uniform α).map f = PMF.uniform β
```

Typeclass context:
```lean
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
```

## Proof strategy

By `PMF.map_comp`, the LHS reduces to:
```
(PMF.uniform (Fin d → F)).map (eval_at_pts ∘ poly_from_coefs)
```
where the composition is
`coefs ↦ fun p : pts => s + ∑ i, coefs i * p.val^(i+1)`.

The full eval map factors as a chain of bijections + a
marginalization:

1. **Translation** by `(fun p => s)` is a bijection on `pts → F`.
   So drop the `s` constant and prove:
   ```
   (uniform (Fin d → F)).map (fun coefs p => ∑ i, coefs i * p.val^(i+1))
     = uniform (pts → F)
   ```

2. **Diagonal scaling**: `eval coefs p = p.val * (∑ i, coefs i * p.val^i)`
   where the inner sum is `Q(p)` with `Q(X) = ∑ coefs i * X^i ∈ degreeLT F d`.
   Diagonal scaling by `p.val` per coordinate (all nonzero, since
   `0 ∉ pts`) is a bijection on `pts → F`.

3. **Polynomial coefficient equivalence** —
   `Polynomial.degreeLTEquiv F d : degreeLT F d ≃ₗ[F] (Fin d → F)`:
   bijection between coefficients and polynomials of degree < d.

4. **Lagrange evaluation equivalence** —
   `Lagrange.funEquivDegreeLT (Subtype.val_injective)` for
   `pts.card = d`: bijection between `degreeLT F (#pts)` and
   `pts → F`.

When `pts.card = d`, steps 1–4 chain to give a bijection;
apply `PMF.uniform_map_of_bijective`.

When `pts.card < d`: extend `pts` to `pts'` of size `d` in
`F \ {0}` (this requires `d < Fintype.card F`, an extra hypothesis
you may need to add to `evals_uniform`). Apply the `=` case to
`pts'`, then project the result down to `pts → F` — this projection
of uniform is uniform (marginal-of-product fact).

## Alternative direct approach (often cleaner)

Prove **injectivity** directly using
`Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero` from
`Mathlib/LinearAlgebra/Lagrange.lean:46`. For `pts.card = d`, given
two coefficient assignments with identical evaluations:

- Define `Δ(X) := ∑ (c1 - c2)(i) * X^(i+1)`, degree ≤ d.
- `Δ` vanishes at all of `pts` (by hypothesis) and at `0`
  (constant term is 0).
- So `Δ` vanishes at `pts ∪ {0}`, size `d + 1` since `0 ∉ pts`.
- `Δ.degree < d + 1 = (insert 0 pts).card`.
- Apply `eq_zero_of_degree_lt_of_eval_finset_eq_zero` → `Δ = 0`.
- From `Δ = 0`, extract `c1 = c2` by reading off coefficients
  (each `Polynomial.C (c1 i - c2 i) * X^(i+1)` term must vanish).

Then use `Fintype.bijective_iff_injective_and_card`
(`Mathlib/Data/Fintype/EquivFin.lean:268`) to lift injectivity to
bijectivity, since `Fintype.card (Fin d → F) = Fintype.card F^d =
Fintype.card (pts → F)` when `pts.card = d`.

## Key Mathlib lemmas (exact paths in v4.27.0)

- `Lagrange.funEquivDegreeLT` —
  `Mathlib/LinearAlgebra/Lagrange.lean:384`
- `Polynomial.degreeLTEquiv` —
  `Mathlib/RingTheory/Polynomial/Basic.lean:112`
- `Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero` —
  `Mathlib/LinearAlgebra/Lagrange.lean:46`
- `Fintype.bijective_iff_injective_and_card` —
  `Mathlib/Data/Fintype/EquivFin.lean:268`
- `Polynomial.degree_C_mul_X_pow_le`, `Polynomial.degree_sum_le` —
  for the degree bound on Δ
- `Polynomial.eval_finset_sum`, `Polynomial.eval_C`,
  `Polynomial.eval_pow`, `Polynomial.eval_X`, `Polynomial.eval_zero`
  — for Δ-eval reasoning
- `PMF.map_comp`, `PMF.uniform_map_of_bijective` — composition
  and bijection-pushforward

## Constraints

1. **Header fence**: do NOT modify the public signatures of
   `evals_uniform` or `bivariate_evals_uniform` except for adding
   necessary hypotheses (e.g., `Fintype.card F` bound). If you add
   hypotheses, propagate to `Leslie/Examples/Prob/Shamir.lean`'s
   three theorems (`shamir_secrecy_pts`, `shamir_secrecy`,
   `shamir_secrecy_via_step`).

2. **Allowed paths** (per `scripts/check-conservative.sh` allowlist):
   - `Leslie/Prob/Polynomial.lean` (main target)
   - `Leslie/Examples/Prob/Shamir.lean` (signature propagation
     only — proofs unchanged)
   - Other `Leslie/Prob/*` files if you need helpers
   - `docs/randomized-leslie-spike/` for notes
   - Do NOT touch existing Leslie code: `Leslie/Refinement.lean`,
     `Leslie/Action.lean`, `Leslie/Round.lean`, etc.

3. **`bivariate_evals_uniform`** may remain `sorry`. The plan
   defers it to M2.

4. **Add no new dependencies** to `lakefile.lean` (Mathlib is
   already pinned at v4.27.0).

5. **Don't push to origin**. Local commits on `randomized-leslie`
   are fine; the user pushes when ready.

## Acceptance criteria

- `lake build Leslie.Prob.Polynomial` green with at most 1 `sorry`
  (`bivariate_evals_uniform`).
- `lake build Leslie.Examples.Prob.Shamir` green.
- `lake build` (full project) green; same 4 pre-existing project
  `sorry`s unchanged (`Refinement.lean` ×2, `LastVoting.lean` ×2).
- `bash scripts/check-conservative.sh` passes (no violations).
- One commit on `randomized-leslie` describing the proof strategy
  and any signature changes.

## What to do if you can't close the proof

If after serious attempt (≥ 60 min, several Mathlib lemma searches)
you can't close `evals_uniform`:

1. Do NOT commit a worse state than the current one (which has
   2 clean `sorry`s).
2. Document specific Mathlib gaps you hit (which lemma you needed
   but couldn't find; which typeclass issue stumped you).
3. Make a partial attempt — e.g., prove only the `pts.card = d`
   case as a separate `evals_uniform_eq_card` lemma, leaving the
   general `evals_uniform` to invoke it (with `sorry` for the
   marginalization step). That would be progress.
4. Commit your partial result with a clear message and update
   this document with what you found.

## Reference files to read first

In this order:
1. `Leslie/Prob/Polynomial.lean` (the target file)
2. `Leslie/Examples/Prob/Shamir.lean` (consumer; for signature
   propagation if needed)
3. `Leslie/Prob/PMF.lean` (helper context)
4. The Mathlib files at line numbers noted above
5. `docs/randomized-leslie-spike/01-trace-measure.md` for context
   on the broader randomized-leslie design

## Branch state at task start

```
e546395 fix(M1 W4): apply review fixes to Shamir model
b4cd79d feat(M1 W4): Shamir secret sharing — secrecy proven (modulo evals_uniform)
9ac45d0 feat(M1 W3): polynomial uniformity foundations (definitions + statements)
5f6e62b feat(M1 W2): pRHL coupling + Adversary/Trace stubs + demo
f3d3c28 test(M1 W1): Knuth-Yao 6-sided die — non-trivial probabilistic example
... (older commits)
```

Current sorries on the branch:
- `Leslie/Prob/Polynomial.lean:107` — `evals_uniform` (target)
- `Leslie/Prob/Polynomial.lean:116` — `bivariate_evals_uniform` (defer)
- `Leslie/Refinement.lean:382, 469` — pre-existing on main
- `Leslie/Examples/LastVoting.lean:302, 396` — pre-existing on main
