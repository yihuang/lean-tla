# M3 W2 finding — `pi_n_AST` is false against stuttering adversary

The `lean4:sorry-filler-deep` agent dispatched at M3 W2 (commit
`00b168f`) discovered a soundness issue while attempting to close
`Leslie.Prob.ASTCertificate.pi_n_AST`:

> Under a demonic adversary that always stutters (`A.schedule _ = none`),
> the state is constant, the hypothesis `∀ n, V (ω n).1 ≤ N` is
> trivially satisfied, but termination need not hold. The certificate
> is missing a "non-stuttering / progress" field.

This is **correct**. With our `Adversary σ ι` definition allowing
`schedule : List (σ × Option ι) → Option ι` to return `none`,
`stepKernel` produces `Dirac (s, none)` — a constant trace. The
hypothesis `∀ n, cert.V (ω n).1 ≤ N` is trivially true (V is
constant), but `terminated (ω n).1` may never hold if the initial
state isn't terminated.

So `pi_n_AST` as stated is **provably false** for stuttering
adversaries.

## Where this comes from

POPL 2025 Rule 3.2 is for demonic adversaries that pick an action
at every step in a probabilistic transition system. There's no
stuttering option — the adversary HAS to fire something. Our
`Adversary` model permits `none` (stuttering) for modeling
asynchronous protocols (Bracha, AVSS) where the adversary delays
delivery; this is consistent with our `traceDist` design but
breaks the demonic AST rule.

In the POPL 2026 fair extension (`FairASTCertificate`), fairness
implicitly rules out indefinite stuttering: a fair adversary
*must* eventually fire fair-required actions. So
`FairASTCertificate.sound` doesn't have this issue at the rule
level — but its proof still has to derive trajectory-progress
from the fairness predicate.

## Resolution paths (in order of preference)

### Option 1 — Add a `progress` field to `ASTCertificate`

Easiest. Add a field encoding "from any non-terminated state, some
gated action is enabled" and require the demonic adversary to fire
it. Concretely:

```lean
structure ASTCertificate ... where
  ...
  /-- Some gated action is enabled at every non-terminated invariant
  state. Combined with the demonic-adversary semantics (which fires
  some enabled action at every step), this rules out indefinite
  stuttering as a way to dodge the variant decrease. -/
  progress : ∀ s, Inv s → ¬ terminated s → ∃ i, (spec.actions i).gate s
```

But this still doesn't force the adversary to fire something —
it only says something is fireable. The adversary may still
choose `none`. So we'd ALSO need a constraint on the adversary,
like:

```lean
def NonStutteringAdversary (spec : ProbActionSpec σ ι) (terminated : σ → Prop)
    (A : Adversary σ ι) : Prop :=
  ∀ s, ¬ terminated s → ∀ h, A.schedule h ≠ none ∨ ¬ ∃ i, (spec.actions i).gate s
```

(The schedule can be `none` only at terminated states or when no
action is enabled.)

This is a non-trivial Adversary refinement.

### Option 2 — Use only the fair version (`FairASTCertificate`)

Drop `ASTCertificate.sound` from M3 — focus all soundness effort
on `FairASTCertificate.sound`, where the fairness predicate
already rules out indefinite stuttering. AVSS termination uses
`FairASTCertificate` anyway (M3 W3+).

`ASTCertificate` (the demonic version) remains as a structural
concept matching POPL 2025 Rule 3.2; but its `sound` theorem stays
sorry'd indefinitely, with a docstring explaining the stuttering
issue.

### Option 3 — Restrict `pi_n_AST` hypothesis to non-stuttering traces

Add a per-trace non-stuttering hypothesis:

```lean
theorem pi_n_AST (cert : ASTCertificate spec terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : Adversary σ ι) (N : ℕ) :
    ∀ᵐ ω ∂(traceDist spec A μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) →
      (∀ n, ¬ terminated (ω n).1 → ∃ i, (ω (n+1)).2 = some i) →
      ∃ n, terminated (ω n).1 := by
  ...
```

The added hypothesis `∀ n, ¬ terminated → ∃ i, action label is some i`
captures "every non-terminated step fires SOME action." This
is provable from a non-stuttering adversary plus the progress
predicate. The downside is that downstream callers (`sound`,
`partition_almostDiamond`) must now thread the non-stuttering
hypothesis through.

## Recommendation

**Option 2** for the immediate term:

- Drop `ASTCertificate.sound` from M3 deliverables (keep the
  structure for documentation but mark `sound` as
  "demonic — stuttering issue, see this brief").
- Focus M3 W3 on `FairASTCertificate.sound` (which is what AVSS
  uses).
- The structural fix (Option 1) is M3 polish or M4 work; it's
  not on the AVSS critical path.

This leaves PR #30 with 2 sorries in `Liveness.lean`:
- `pi_n_AST` — documented as blocked on the stuttering issue.
- `FairASTCertificate.sound` — the M3 W3 deliverable.

Both are tractable separately; neither blocks AVSS.

## Status of M3 W2 deep-dive (commit 00b168f)

The agent took **Option C** (the brief's fallback) and closed
`pi_infty_zero` by adding `AlmostBox_of_inductive` (a non-pure-effect
generalization of `AlmostBox_of_pure_inductive`) to
`Leslie/Prob/Refinement.lean`. The new helper covers the
trajectory-Inv lift cleanly.

Sorry count after `00b168f`:
- `Leslie/Prob/Liveness.lean` — 2 (`pi_n_AST` line 204,
  `FairASTCertificate.sound` line 435).
- `Leslie/Examples/Prob/BrachaRBC.lean` — 1 (totality, M3 W3).
- `Leslie/Examples/Prob/AVSSStub.lean` — 1 (avssCert,
  entry-gate budget).
- `Leslie/Refinement.lean` — 2 (pre-existing project sorries).
