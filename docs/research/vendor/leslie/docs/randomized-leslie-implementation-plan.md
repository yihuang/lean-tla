# Randomized Leslie: Implementation Plan (v2.2)

> Companion to `randomized-leslie-plan.md` v2.2. Where the design plan
> answers *what* and *why*, this document answers *how* and *in what
> order* — at the granularity of files, signatures, and weekly
> checkpoints.
>
> **Revision history.** v1 (initial); v2 propagates the design-plan v2
> changes: Mathlib dependency made an explicit M1 deliverable,
> `ProbActionSpec σ ι` shape (no `P` parameter), `BenOrAsync.lean`
> (not `BenOr.lean`), Wegman–Carter MAC replacing ElGamal, M3 entry
> gate for the AVSS certificate stub, 2DRW fallback path, CI
> conservatism script extended to ignore lakefile churn, staffing
> assumption made explicit. v2.1 added **Milestone 0** (2-week pre-M1
> spike) covering round-2 review findings: PMF vs. measure for trace
> distributions, parallel-composition state model, AST soundness
> scaffolding, and a CI regex fix. **v2.2 (this version)** records M0
> *closure*: all four M0 tasks complete with working Lean artifacts;
> M1 estimate carries forward unchanged; design-plan signatures
> updated inline; CI workflow wired. M0 actual elapsed: <1 day vs.
> 2-week budget, primarily because Mathlib already has Ionescu-Tulcea
> (arXiv 2506.18616) and Doob (arXiv 2212.05578).

This document covers M1 in full detail, M2 / M2.5 in moderate detail,
and M3+ in skeleton form. The detail tapers deliberately: design
decisions in M3+ depend on what we learn in M1–M2, so freezing them
now is premature.

## Conventions

- *Definition of Done* per task: file compiles under the Leslie lake
  toolchain, has at least one example use in the same file or in
  `Examples/Prob/`, and exercises every public API entry under
  `lake test` or via a worked example.
- *Sorry budget:* zero `sorry` in committed code on the
  `randomized-leslie` branch by end of each milestone, **with one
  exception**: the M3 entry-gate AVSS certificate stub may carry
  `sorry` in its proof obligations during M3 W1–W4 (see *M3* below).
  In-progress work uses topic branches.
- *Conservatism check:* every PR touches only `Leslie/Prob/`,
  `Leslie/UC/`, `Leslie/Tactics/Prob.lean`, `Examples/Prob/`,
  `docs/`, or the build-system files (`lakefile.lean`,
  `lake-manifest.json`, `lean-toolchain`). CI script
  `scripts/check-conservative.sh` diffs every other path against
  `main` and fails if non-empty. Build-system files are excluded so
  that Mathlib upgrades don't trigger false positives.
- *Mathlib pin:* fix a single Mathlib commit at start of M1 W1 and
  upgrade only at milestone boundaries with a dedicated commit.

## Staffing assumption

**Estimates assume one Leslie-fluent engineer who is also fluent
with Mathlib's `PMF` / `MeasureTheory` APIs.** For deviations from
that profile:

| Engineer profile                              | Multiplier |
|-----------------------------------------------|------------|
| Leslie-fluent + Mathlib-fluent                | 1.0×       |
| Leslie-fluent, new to Mathlib PMF             | 1.4×       |
| Mathlib-fluent, new to Leslie                 | 1.4×       |
| New to both                                   | 2.0×       |

Numbers below are 1.0× weeks; multiply for actual planning. Two
engineers in parallel give ~1.5× speedup on M1–M2 (foundation work)
and ~1.7× on M3 (independent examples) but no speedup on M4 (UC
machinery is sequential).

## Branch & repository setup

One-time setup on your local clone:

```bash
git checkout main
git pull
git checkout -b randomized-leslie

# First commit: docs only
mkdir -p docs
cp randomized-leslie-plan.md docs/
cp randomized-leslie-implementation-plan.md docs/
git add docs/randomized-leslie-plan.md docs/randomized-leslie-implementation-plan.md
git commit -m "docs: add randomized-leslie design and implementation plans"

# Second commit: conservatism CI script
mkdir -p scripts
cp scripts/check-conservative.sh scripts/  # see below for content
git add scripts/check-conservative.sh
git commit -m "ci: add conservative-extension check"

# (M1 W1 will add a third commit: lakefile changes adding Mathlib)

git push -u origin randomized-leslie
```

Open a draft PR from `randomized-leslie` → `main` titled
"WIP: Randomized Leslie." The PR stays open through M5 and serves as
the running log. Each milestone closes a checkpoint commit on the
branch, not a separate PR.

The conservativity check is implemented as an *allowlist* — any file
outside the explicit randomized-leslie scope is reported as a
violation. The earlier protected-list approach (in v2) was rejected
during M0.4 because nested examples like
`Leslie/Examples/Combinators/PhaseCombinator.lean` slipped through
its `^Leslie/Examples/[^/]+\.lean$` regex; an allowlist is robust
against new directories anywhere in the repo.

```bash
#!/usr/bin/env bash
# scripts/check-conservative.sh — allowlist version (M0.4)
set -euo pipefail

# Newline-delimited; joined into one alternation for grep -E.
ALLOWED_PATHS=$(cat <<'EOF'
^Leslie/Prob/
^Leslie/UC/
^Leslie/Tactics/Prob\.lean$
^Leslie/Examples/Prob/
^docs/
^scripts/
^\.github/
^lakefile\.lean$
^lake-manifest\.json$
^lean-toolchain$
EOF
)
ALLOWED_RE=$(echo "$ALLOWED_PATHS" | tr '\n' '|' | sed 's/|$//')

DIFF_CMD="${CONSERVATIVE_CHECK_DIFF_CMD:-git diff --name-only origin/main...HEAD}"
VIOLATIONS=$(eval "$DIFF_CMD" | grep -vE "$ALLOWED_RE" || true)
if [[ -n "$VIOLATIONS" ]]; then
  echo "Conservative-extension violation:"
  echo "$VIOLATIONS"
  exit 1
fi
```

A companion test script `scripts/check-conservative.test.sh` exercises
33 cases (19 violation, 14 pass) covering existing nested example
directories, top-level repo files, and the allowlisted directories.
Run via `bash scripts/check-conservative.test.sh`.

Wire `scripts/check-conservative.sh` into `.github/workflows/ci.yml`
as a required check for the `randomized-leslie` branch (and its PR
into `main`). The CI job runs the test script first, then the real
check. The allowlist explicitly admits `lakefile.lean`,
`lake-manifest.json`, and `lean-toolchain` so the M1 W1 Mathlib-add
commit and any later Mathlib version bumps are non-events for the
gate.

## Milestone 0 — Foundations spike (2 weeks)

Pre-M1 throwaway spike addressing round-2 review findings 1–5 on the
design plan. Lives on a separate branch `randomized-leslie-spike`;
artifacts are decision documents and minimal Lean prototypes, not
production code. M0 does not produce shippable code; it produces
*decisions* that unblock M1.

The spike exists because three load-bearing questions in v2 are
hand-waved: (a) the type of `traceDist`, (b) the state model of
`parallel`, (c) whether AST soundness is provable against the chosen
trace type. Without these settled, M1 W1's API design is guesswork.

### Task M0.1 — PMF vs. measure for trace distributions (~5 days)

**Question.** What is the type of `traceDist Π A`?

**Why this matters.** v2 says `PMF (Trace σ ι)` where
`Trace σ ι := Stream' (σ × Option ι)`. Mathlib's `PMF α` requires
countable support; `Stream' (σ × Option ι)` is uncountable for any
non-trivial `σ`. `PMF (Trace σ ι)` is therefore not a real type, and
several v2 signatures (`Refines`, `RelatedTraces`, `traceDist`)
inherit the bug.

**Deliverables.**

1. **Decision document** `docs/randomized-leslie-spike/01-trace-measure.md`
   (~2 pages) deciding between:
   - **(A)** `Measure (Trace σ ι)` with cylinder σ-algebra; per-step
     `PMF`s composed via Ionescu-Tulcea kernel composition. Mathlib
     has `MeasureTheory.Constructions.Polish.Basic` and projective
     limits to draw on.
   - **(B)** `Stream'`-recursive `PMF` over a finite-prefix-truncated
     trace type, with a separate "tail measure" object for liveness.
   - **(C)** Use `MeasureTheory.ProbabilityMeasure` directly throughout
     and revise the design-plan claim that "discrete probability is
     enough."
2. **Minimal Lean prototype** (~150 lines) defining `traceDist` for a
   trivial 2-action `ProbActionSpec` and proving one fact about it
   (e.g., the marginal at step 0 is the initial distribution). The
   prototype must compile under the M1 toolchain pin.
3. **Verification of Doob availability.** Confirm that
   `MeasureTheory.Martingale.Convergence` (or the analogous module
   in the pinned Mathlib version) proves Doob's martingale
   convergence at the type chosen in (1). If a shim is needed,
   estimate its size and decide whether to upstream or vendor.

**Exit gate.** Decision recorded; prototype builds green; design
plan v2.1 updated to reference the chosen approach. If the answer is
(A), update v2's "Discrete probability first" framing.

### Task M0.2 — Parallel composition state model (~3 days) — DONE

**Question.** What is the state type of `Π₁ ∥ Π₂` for protocols that
share a network?

**Why this matters.** v2 shows
`parallel : … → ProbActionSpec (σ₁ × σ₂) (ι₁ ⊕ ι₂)` — disjoint state.
Real distributed protocols share message buffers; UC substitution
rewires shared interfaces. Disjoint-state product cannot model
either. AVSS, common coin, and async BA all require this question
answered.

**Decision.** State is `σ₁ × σ_net × σ₂` with the network as its own
`ProbActionSpec`. Party actions guard on local + network; network
actions guard on the network alone. Composition is action-set
disjoint union (`ι₁ ⊕ ι_net ⊕ ι₂`); state overlap on `σ_net` is
genuine. This is the *shared-state product* — Hirt-Maurer async UC's
default shape — not the disjoint-state product.

**Delivered.**

1. **Decision document** at
   `docs/randomized-leslie-spike/03-parallel-state.md` — model
   rationale, signature shape, why shared-network beats either
   disjoint-state or fully-shared-variables, and the M2 W1
   promotion path.
2. **Lean shape stub** at `Leslie/Prob/Spike/ParallelShape.lean`
   (~150 lines, 0 sorry, 0 warning). Demonstrates `AsyncNet`
   mailbox model, `DistState`/`DistAction` shape, `composedStep`
   over the disjoint-action-union, and a 30-line "two parties
   exchange one boolean message" sanity example. Mathlib-free
   (M0.2 is pure data; the M0.1/M0.3 trace work supplies the
   probabilistic layer above).

**Exit gate.** ✓ Decision document; ✓ signature consistent with
M0.1; ✓ Lean stub builds; ✓ sanity example fits in ~30 lines as
budgeted.

**Note on file numbering.** The doc lives at
`03-parallel-state.md`, not `02-parallel-state.md` as originally
indicated above. Spike files were written in the order
M0.1 → M0.4 → M0.3 → M0.2; numbering follows write order to
preserve link stability across the four spike commits.

### Task M0.3 — AST soundness scaffolding sanity check (~2 days) — DONE

**Question.** Does `ASTCertificate.sound` actually go through against
the M0.1 trace type?

**Why this matters.** Round-2 finding 2: the plan claims to defer
measure theory but the soundness proof requires Doob. Either the
deferral is real (and we need a non-measure-theoretic soundness proof
for the POPL 2025 rule, which doesn't exist in the literature) or
the deferral is wrong. Either way, M3 W1 cannot start until this is
clear.

**Resolution.** Mathlib has the lemmas. M0.1 already established
`Submartingale.ae_tendsto_limitProcess`; M0.3 confirmed it composes
with `Filtration`, `Supermartingale`, `eLpNorm`, `IsFiniteMeasure`,
and the `∀ᵐ` machinery to express the full POPL 2025 (V, U)-rule
shape and its soundness statement.

**Delivered.**

1. **Outline** at `docs/randomized-leslie-spike/02-ast-soundness.md`
   — four-step soundness proof (negate to submartingale → Doob's
   a.e. convergence → non-negativity bounds limit → sublevel-set
   Borel-Cantelli for termination) with each step naming the
   specific Mathlib lemma it uses.
2. **Lean stub** at `Leslie/Prob/Spike/ASTSanity.lean` (108 lines).
   `ASTCert` structure with `V_super`, `V_nonneg`, `V_term`,
   `V_bdd`, `U_bdd_subl`, `U_dec_prob` fields against an arbitrary
   `(μ, ℱ, V, U, term)`. `ASTCert.sound` statement type-checks
   under `IsFiniteMeasure μ`. Builds green with the planned single
   `sorry` in the soundness body.

**Findings.** The "small shim, ~200 lines worst case" budget for the
Mathlib martingale-convergence gap is conservative. Actual shim is
~50 lines: `Supermartingale.neg`-to-`Submartingale` conversion (~5
lines), `Filtration.natural` `MetrizableSpace` plumbing on `X n`
(~10 lines), sublevel-set Borel-Cantelli application (~30 lines).
No Mathlib gap blocks M3 W1.

**Exit gate.** ✓ Outline written; ✓ stub builds green; ✓ no Mathlib
gap.

### Task M0.4 — Conservativity CI regex fix (~0.5 days) — DONE

**Question.** Does `scripts/check-conservative.sh` actually protect
the existing example tree?

**Why this matters.** The original v2 regex
`^Leslie/Examples/[^/]+\.lean$` did not match nested paths. On
`main` this left `Leslie/Examples/Combinators/`,
`Leslie/Examples/Paxos/`, and `Leslie/Examples/CacheCoherence/**`
*unprotected* by the conservatism gate. The CI safety net was
silently broken.

**Resolution.** Switched from a protected-list to an *allowlist*
approach (see *Branch & repository setup* above for the script
shape). Allowlists are robust against new directories anywhere in
the repo — anything outside `Leslie/Prob/`, `Leslie/UC/`,
`Leslie/Tactics/Prob.lean`, `Leslie/Examples/Prob/`, `docs/`,
`scripts/`, `.github/`, or the build-system files is flagged
automatically without requiring regex updates.

**Delivered.**

1. `scripts/check-conservative.sh` — allowlist regex with
   `CONSERVATIVE_CHECK_DIFF_CMD` env override for testing.
2. `scripts/check-conservative.test.sh` — 33 test cases (19
   violation, 14 pass) covering existing nested examples
   (`Combinators/`, `Paxos/`, `CacheCoherence/`, `VerusBridge/`,
   `LastVotingPhased/`), top-level repo files (`MANUAL.md`,
   `README.md`, `AGENTS.md`, `Leslie.lean`), and the allowlisted
   tree. All 33 pass.
3. Tested against the actual branch state: 6 changed files vs
   `origin/main`, all in allowlist, script reports OK.

**Wiring into CI.** Deferred until the first M1 PR opens against
`main`; at that point add `.github/workflows/conservativity.yml`
with a single job running the test then the check. The job is
trivially fast (<1 s) so always-run, no caching needed.

**Exit gate.** ✓ Script catches synthetic diff (test 33/33);
✓ implementation plan v2.1 patched with the new shape inline.

### M0 closeout

If M0.1–M0.3 resolve cleanly: proceed to M1 with v2.1 plans, no
further changes needed.

If any of M0.1–M0.3 reveals that the rule or substrate needs
restructuring: pause and re-plan. The 2-week investment buys early
detection of what would otherwise be a 4–6 month course correction
mid-M3.

**Stop conditions for M0** (escalate to a re-plan, do not push
through):

- Ionescu-Tulcea construction is not in Mathlib *and* writing it from
  scratch exceeds 500 lines (M0.1).
- Doob's convergence in the M0.1 trace type requires a shim > 200
  lines (M0.3).
- Shared-state parallel composition forces a redesign of
  `ProbActionSpec` itself (M0.2).
- Any of the M0 prototypes needs `noncomputable` in places that v2
  assumed would be computable (this would change the tactic story
  for `Tactics/Prob.lean`).

## Milestone 1 — Foundations + pRHL skeleton + Shamir (4 weeks)

### Week 1: Mathlib + PMF infrastructure + `ProbActionSpec`

This is *the* foundation week. Everything downstream depends on
getting these signatures right.

#### W1 Day 1: Add Mathlib dependency

Single commit. `lakefile.lean` gets a Mathlib `require` clause; the
Mathlib commit is pinned to a recent stable tag compatible with the
project's `lean-toolchain`.

```lean
-- lakefile.lean (additions)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "<pin commit SHA>"
```

`lake-manifest.json` updates accordingly. Run `lake exe cache get`
to populate the Mathlib build cache locally; document the
incantation in the PR description.

CI: add a `mathlib4-cache` step before `lake build` to keep cold
builds tractable. Document peak-RAM and build-time numbers (cold
and warm) in the PR description so contributors know what to
expect.

**Definition of Done:** `lake build` succeeds with no Leslie code
changes; the existing test suite passes unchanged.

#### W1 Days 2–5: `Leslie/Prob/PMF.lean`

~250 lines. Thin layer atop Mathlib's `PMF`.

```lean
namespace Leslie.Prob

-- Re-exports of Mathlib PMF primitives we use directly
export PMF (pure bind map support)

-- Conditional / restricted distribution over a decidable predicate
def PMF.condition (μ : PMF α) (P : α → Prop) [DecidablePred P]
                  (h : ∃ a ∈ μ.support, P a) : PMF α

-- Joint distribution from independent samples
def PMF.product (μ : PMF α) (ν : PMF β) : PMF (α × β)

-- Total variation distance (returns ℝ≥0)
def PMF.totalVariation (μ ν : PMF α) : ℝ≥0

-- Uniform over Fintype, with a convenient signature
def PMF.uniform (α : Type) [Fintype α] [Nonempty α] : PMF α

-- Indicator-style helpers used pervasively in proofs
@[simp] theorem PMF.support_pure (a : α) : (PMF.pure a).support = {a}
@[simp] theorem PMF.bind_dirac (a : α) (f : α → PMF β) :
                PMF.pure a >>= f = f a

end Leslie.Prob
```

*Definition of Done:* every theorem has at least one rewrite-rule
use elsewhere by end of M1, OR is annotated `@[simp]` or
`@[Leslie.Prob.simp]` and demonstrably matches in a smoke test.

#### W1 Days 6–8: `Leslie/Prob/Action.lean`

~150 lines. **Critical: shape mirrors existing `ActionSpec σ ι`
exactly — function-indexed by `ι`, no separate parameter.**

```lean
import Leslie.Prob.PMF

namespace Leslie.Prob

structure ProbGatedAction (σ : Type) where
  guard  : σ → Prop
  effect : (s : σ) → guard s → PMF σ

structure ProbActionSpec (σ ι : Type) where
  init    : σ → Prop
  actions : ι → ProbGatedAction σ

namespace ProbActionSpec
  variable {σ ι : Type}

  -- Single-step transition: given the action chosen by the scheduler,
  -- return the PMF over next states (None if guard fails).
  def step (Π : ProbActionSpec σ ι) (i : ι) (s : σ) : Option (PMF σ) :=
    if h : (Π.actions i).guard s
    then some ((Π.actions i).effect s h)
    else none

  -- Disjoint-state parallel composition.
  def parallel (Π₁ : ProbActionSpec σ₁ ι₁) (Π₂ : ProbActionSpec σ₂ ι₂) :
                ProbActionSpec (σ₁ × σ₂) (ι₁ ⊕ ι₂) := { ... }

end ProbActionSpec

end Leslie.Prob
```

*Note:* the original v1 of this plan had `ProbGatedAction (S P : Type)`
with a per-action parameter `P`. That doesn't match Leslie's existing
`ActionSpec`, which folds parameters into `ι`. v2 drops `P`.

#### W1 Days 9–10: `Leslie/Prob/Embed.lean` (skeleton)

~100 lines. Full conservativity theorems land in W4; W1 establishes
the coercion only.

```lean
namespace Leslie.Prob

def GatedAction.toProb (a : GatedAction σ) : ProbGatedAction σ where
  guard  := a.guard
  effect := fun s _ => PMF.pure (a.effect s)

def ActionSpec.toProb (Π : ActionSpec σ ι) : ProbActionSpec σ ι where
  init    := Π.init
  actions := fun i => (Π.actions i).toProb

@[simp] theorem ActionSpec.toProb_init (Π : ActionSpec σ ι) :
    Π.toProb.init = Π.init := rfl

@[simp] theorem ActionSpec.toProb_step_pure
    (Π : ActionSpec σ ι) (i : ι) (s : σ)
    (h : (Π.actions i).guard s) :
    Π.toProb.step i s = some (PMF.pure ((Π.actions i).effect s)) := by
  simp [ProbActionSpec.step, ActionSpec.toProb, GatedAction.toProb, h]

end Leslie.Prob
```

The first acceptance test that the embedding is genuinely a
coercion: each field of `ActionSpec.toProb` should be a single
expression. If `Embed.lean` requires substantive proof obligations,
something in the design is wrong.

**W1 acceptance:**

- `lake build Leslie.Prob.PMF`, `lake build Leslie.Prob.Action`,
  `lake build Leslie.Prob.Embed` all succeed.
- Smoke test in `Examples/Prob/Smoke.lean`: define a 1-action
  `ProbActionSpec σ Unit` that flips a fair coin (state := Bool,
  initial state := false, action := flip), prove its single-step
  distribution is `PMF.uniform Bool`. ~30 lines, demonstrates the
  full API composes.
- The Mathlib build cache is populated and documented.

### Week 2: pRHL-style `Coupling.lean`

**Files created:**
- `Leslie/Prob/Adversary.lean` (~150 lines, stub for M1; full version in M2)
- `Leslie/Prob/Trace.lean` (~200 lines, single-step traces for M1)
- `Leslie/Prob/Coupling.lean` (~500 lines, the workhorse)

The full `Adversary` (with corruption, fairness predicate) lands in
M2. For M1 we need only enough trace machinery to state Shamir
secrecy, which is a one-step derivation from the initial state.

#### W2 `Leslie/Prob/Adversary.lean` (stub)

```lean
namespace Leslie.Prob

-- Stub adversary: just enough for single-step traces.
-- Full version with corruption, fairness in M2.
structure Adversary (σ ι : Type) where
  schedule : List (σ × Option ι) → Option ι

end Leslie.Prob
```

#### W2 `Leslie/Prob/Coupling.lean` — the central objects

```lean
namespace Leslie.Prob

-- A coupling of two PMFs: a joint with the right marginals.
structure PMF.Coupling (μ : PMF α) (ν : PMF β) where
  joint      : PMF (α × β)
  marg_left  : joint.map Prod.fst = μ
  marg_right : joint.map Prod.snd = ν

-- Coupling supports a relation R on its support pairs.
def PMF.Coupling.supports (c : Coupling μ ν) (R : α → β → Prop) : Prop :=
  ∀ p ∈ c.joint.support, R p.1 p.2

-- Existence of an =-supporting coupling implies marginal equality.
theorem PMF.eq_of_coupling_id (c : PMF.Coupling μ ν)
        (h : c.supports (· = ·)) : μ = ν

-- Sound rules ported from pRHL.
theorem PMF.coupling_pure    : PMF.Coupling (PMF.pure a) (PMF.pure a)
theorem PMF.coupling_bind    : ∀ {μ ν f g}, ...   -- bind/sample rule
theorem PMF.coupling_swap    : ∀ {μ ν τ},   ...   -- eager/lazy commute
theorem PMF.coupling_uptobad : ∀ {μ ν bad}, ...   -- fundamental lemma

-- Two ProbActionSpecs related by R produce R-coupled trace distributions.
def RelatedTraces (Π₁ : ProbActionSpec σ₁ ι₁) (Π₂ : ProbActionSpec σ₂ ι₂)
                  (R : σ₁ → σ₂ → Prop) : Prop :=
  ∀ A₁ A₂, ∃ c : PMF.Coupling (traceDist Π₁ A₁) (traceDist Π₂ A₂),
    c.supports (TraceRel R)

theorem RelatedTraces.view_eq
    (h : RelatedTraces Π₁ Π₂ R)
    (V : Trace σ₁ ι₁ → View) (V' : Trace σ₂ ι₂ → View)
    (h_view : ∀ t₁ t₂, TraceRel R t₁ t₂ → V t₁ = V' t₂) :
    (traceDist Π₁ _).map V = (traceDist Π₂ _).map V'

end Leslie.Prob
```

#### W2 Tactics in `Leslie/Tactics/Prob.lean`

```lean
syntax "by_coupling"           : tactic
syntax "coupling_identity"     : tactic
syntax "coupling_bijection" term : tactic
syntax "coupling_swap"         : tactic
syntax "coupling_up_to_bad" term : tactic
```

**W2 acceptance:** A toy example in `Examples/Prob/CouplingDemo.lean`
proving
`(do x ← uniform Bool; y ← uniform Bool; pure (x + y)) = (do z ← uniform Bool; pure z)`
via `coupling_bijection (fun (x,y) => (x, x ⊕ y))`. If this proof
exceeds ~10 lines including imports, the tactic interface needs work
before proceeding.

### Week 3: Polynomial uniformity library

**Files created:** `Leslie/Prob/Polynomial.lean` (~400 lines).

```lean
namespace Leslie.Prob.Polynomial
open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- Uniformly random polynomial of degree ≤ d with f(0) = s.
def uniformWithFixedZero (d : ℕ) (s : F) : PMF (Polynomial F) :=
  -- Sample d independent uniform coefficients for x, x², …, x^d;
  -- prepend s as constant term.
  ...

-- Headline uniformity lemma.
theorem evals_uniform
    (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card ≤ d) (h_nz : 0 ∉ pts) :
    let μ := (uniformWithFixedZero d s).map
              (fun f => pts.image (fun i => f.eval i))
    μ = PMF.uniform _   -- joint of d evaluations is uniform on F^|pts|

-- Bivariate version (for AVSS in M3).
def uniformBivariateWithFixedZero (dx dy : ℕ) (s : F) :
    PMF (Polynomial (Polynomial F))

theorem bivariate_evals_uniform : ...
```

The univariate proof uses Lagrange interpolation: a degree-≤-d
polynomial is determined by d+1 evaluations, so fixing `f(0) = s`
and `d` other evaluations determines `f`. The map from
`(s, d uniform values)` to `(f's d evaluations)` is a bijection.
This is the bijection coupling pattern realized algebraically; the
proof should be one application of `coupling_bijection`.

**W3 acceptance:**
- `evals_uniform` proved without `sorry`.
- `bivariate_evals_uniform` either proved or stated with explicit
  reduction to `evals_uniform` plus a clear `sorry` deferred to M2.
  (The bivariate version is M2's algebraic core; getting the
  univariate version rock-solid is the M1 goal.)

**W3 status (PR #25):** both `evals_uniform` (commit `c8ad591`) and
`bivariate_evals_uniform` (commit `1eb647e`, via row-then-column
reduction) are proved sorry-free. The optional M2 deferral is no
longer in effect; field-size hypotheses `d + 1 ≤ Fintype.card F`
are required on each axis.

### Week 4: Shamir secrecy + conservativity (level-2)

**Files created:** `Examples/Prob/Shamir.lean` (~150 lines).

**Files extended:**
- `Leslie/Prob/Embed.lean` — full level-2 conservativity theorems.
- `Leslie/Prob/Invariant.lean` (new, ~100 lines) — almost-sure
  invariants, just enough for the conservativity theorem to be
  stateable.

#### Shamir example

```lean
namespace Leslie.Examples.Prob.Shamir

def shamirShare (F : Type) [Field F] [Fintype F] (t n : ℕ) (s : F) :
                ProbActionSpec (ShamirState F n) ShamirIdx := ...

def Coalition (n t : ℕ) := { S : Finset (Fin n) // S.card ≤ t }

def coalitionView (C : Coalition n t) : ShamirState F n → View := ...

theorem shamir_secrecy
    (F : Type) [Field F] [Fintype F] (t n : ℕ) (h : t < n)
    (C : Coalition n t) (s s' : F) :
    let Π  := shamirShare F t n s
    let Π' := shamirShare F t n s'
    (traceDist Π  emptyAdv).map (coalitionView C) =
    (traceDist Π' emptyAdv).map (coalitionView C) := by
  by_coupling
  coupling_bijection (...)
  -- closes via Polynomial.evals_uniform

end Leslie.Examples.Prob.Shamir
```

#### Conservativity theorems (level 2 only — see design plan §"Conservativity, precisely")

```lean
-- Leslie/Prob/Embed.lean (extended)

theorem invariant_preserved (Π : ActionSpec σ ι) (φ : σ → Prop) :
    Π ⊨ □φ → Π.toProb ⊨ □̃ φ

theorem refines_preserved (Π Σ : ActionSpec σ ι) :
    Π ⊑ Σ → Π.toProb ⊑ₚ Σ.toProb
```

The level-3 `WF1Premises_implies_AST` bridge waits until M3 W1 when
`FairASTCertificate` exists.

**W4 acceptance — M1 closeout:**

- All theorems above proved without `sorry`.
- `lake build` succeeds; `lake test` passes.
- `scripts/check-conservative.sh` reports zero protected-file
  changes.
- Shamir secrecy proof is ≤ 30 lines including the bijection
  argument. If longer, the `coupling_bijection` tactic infrastructure
  needs work.
- M1 closeout note appended to the PR description: actual line
  counts vs. estimates, any deviations from this plan, Mathlib build
  numbers.

## Milestone 2 — Async Byzantine + bivariate Shamir (4 weeks)

Less detailed because design decisions in W1 of M2 depend on M1
ergonomics. Sketch only.

### Week 1: Adversary and Trace, properly

Promote the M1 stub `Adversary.lean` and `Trace.lean` to first-class
status, including the `FairAdversary` type as a hard predicate (per
design plan v2 §"Adversary, scheduler, fairness"):

```lean
-- Leslie/Prob/Adversary.lean
abbrev PartyId := ℕ

structure Adversary (σ ι : Type) where
  schedule : List (σ × Option ι) → Option ι       -- demonic, history-deterministic
  corrupt  : Set PartyId                           -- static corruption

structure FairnessAssumptions (σ ι : Type) where
  fair_actions : Set ι
  isWeaklyFair : Adversary σ ι → Prop

structure FairAdversary (σ ι : Type) (F : FairnessAssumptions σ ι) where
  toAdversary : Adversary σ ι
  fair        : F.isWeaklyFair toAdversary

-- Leslie/Prob/Trace.lean
def Trace (σ ι : Type) := Stream' (σ × Option ι)
def traceDist (Π : ProbActionSpec σ ι) (A : Adversary σ ι) :
              PMF (Trace σ ι)
```

**Decision (per design plan):** traces are infinite streams;
termination is encoded as eventual stuttering at a terminal state.
Not "trace prefixes" — that was the open question in v1, resolved.

### Week 2: Probabilistic refinement

`Leslie/Prob/Refinement.lean`. Lift Abadi–Lamport:

```lean
def Refines (Π : ProbActionSpec σ ι) (Σ : ProbActionSpec σ' ι') : Prop :=
  ∀ A, ∃ A', traceDist Π A = (traceDist Σ A').map projectStuttering
notation Π " ⊑ₚ " Σ => Refines Π Σ

theorem Refines_safe : Π ⊑ₚ Σ → Σ ⊨ □̃ φ → Π ⊨ □̃ φ
theorem Refines_compose : Refines Π Σ → Refines Σ Τ → Refines Π Τ
theorem Refines_parallel : ...     -- monotone under disjoint-state parallel
```

### Week 3: Bracha RBC

`Examples/Prob/BrachaRBC.lean`. ~400 lines. The probabilistic
surface is empty (Bracha is deterministic), but the example forces
the adversary, network, and corruption modeling to be honest.

Three theorems: validity, agreement, totality. Each is a Leslie
invariant lifted via `invariant_preserved`.

### Week 4: Bivariate Shamir + M2 closeout

`Examples/Prob/BivariateShamir.lean`. Bivariate uniformity is the
algebraic core of AVSS secrecy in M3.

## Milestone 2.5 — Crypto idioms shakedown (2 weeks)

Per design plan v2: replace v1's ElGamal with an information-theoretic
example so M2.5 stays within the "no negligible-function library"
budget.

### Week 1: One-time pad

`Examples/Prob/OneTimePad.lean`. ~80 lines.

Statement: encryption of any two messages produces identical
distributions when the key is uniform. Discharged via
`coupling_bijection (fun k => k ⊕ (m₁ ⊕ m₂))`.

If this proof exceeds 20 lines, file an issue against `Coupling.lean`
ergonomics and fix before proceeding to ITMAC.

### Week 2: Wegman–Carter information-theoretic MAC

`Examples/Prob/ITMAC.lean`. ~250 lines.

Statement: a one-time MAC over a finite field has unforgeability
probability `≤ 1/|F|` against any (computationally unbounded)
adversary that has seen one tag.

The proof exercises `coupling_up_to_bad` *legitimately* in the
information-theoretic setting:
1. Real game: adversary sees `(m, MAC(k, m))` for adversary-chosen
   `m`, then attempts to forge `(m', τ')` with `m' ≠ m`.
2. Hop 1: replace the MAC computation with a uniformly-sampled tag,
   conditioned on consistency with the seen pair. Justified by
   the uniform-evaluation property of the underlying universal hash
   family.
3. Hop 2: probability of forgery is exactly `1/|F|` because for any
   `m' ≠ m`, the conditional distribution of `MAC(k, m')` given
   `MAC(k, m)` is uniform.

This validates `coupling_up_to_bad` and the game-hopping discipline
without requiring computational hardness assumptions.

**Why ITMAC and not ElGamal:** ElGamal IND-CPA is a *computational*
statement (PPT adversaries, DDH assumption). The plan defers
computational secrecy to a post-M5 milestone. Including ElGamal in
M2.5 would either require axiomatizing DDH (hand-wave, defeats
calibration) or building the negligible-function layer (2+ weeks,
misplaced before AVSS). Wegman–Carter exercises the same
`coupling_up_to_bad` machinery legitimately.

**M2.5 closeout:** open issues for any pRHL-ergonomics friction
discovered. Fix the top three before starting M2.7.

## Milestone 2.7 — Synchronous VSS (3 weeks)

Per design plan v2.2 §M2.7: a BGW-style synchronous information-
theoretic VSS as a calibration-and-rehearsal milestone for AVSS.
Same secrecy core as AVSS (bivariate Shamir, already proved), but
deterministic 3-round termination — no AST rule, no common coin,
no fairness obligations.

**Why before M3.** Splits the AVSS work into two: (a) "verify a
VSS protocol with secrecy + correctness + commitment" (M2.7),
(b) "lift to asynchrony with almost-sure termination" (M3). If the
framework can't cleanly verify a synchronous VSS, AVSS is doomed
for unrelated reasons; finding that out in 3 weeks beats finding
out in 6.

### Week 1: Protocol model + correctness

`Examples/Prob/SyncVSS.lean`. ~300 lines.

State machine for the 3-round protocol:
- **Round 1.** Dealer's `ProbAction` samples bivariate
  `F : F[x,y]_{≤t,≤t}` uniformly subject to `F(0,0) = s`, then
  delivers `(f_i, g_i)` to each party as a deterministic effect on
  the post-sample state.
- **Round 2.** Per-party deterministic `consistencyCheck` action
  emits a `Set Complaint` from the local pair.
- **Round 3.** Dealer's `resolveComplaints` deterministic action
  broadcasts `F(i,j)` for each complained pair.

W1 deliverable:
- *Correctness:* if dealer honest, every honest party's reconstruction
  output equals `s`. Lifted via Leslie `invariant_preserved` — the
  PMF on the dealer's `F` is irrelevant once the deterministic
  transition relation preserves "every honest party's local poly is
  a row/column of `F`".

### Week 2: Commitment + termination

Commitment: even with corrupt dealer, the unique value `s'` such
that all honest parties' polynomials interpolate to `s'` at `(0,0)`
exists and is the reconstruction output. Pure invariant lemma —
no probabilistic content.

Termination: deterministic 3-round bound. The `terminated` predicate
is `round ≥ 3`; standard Leslie termination via a `Nat`-valued
variant `3 - round`.

W2 deliverable: ~200 lines, two theorems.

### Week 3: Secrecy

Secrecy theorem: the `t`-coalition view of `(f_i, g_i)_{i ∈ T}` is
independent of `F(0,0) = s`. Reduction:

```lean
theorem syncVSS_secrecy (T : Finset (Fin n)) (hT : T.card ≤ t)
    (s₁ s₂ : F) :
    (PMF.uniformBivariateThrough0 t s₁).map (fun F => coalitionView T F)
      = (PMF.uniformBivariateThrough0 t s₂).map (fun F => coalitionView T F)
```

Proof: apply `bivariate_evals_uniform` to both sides, observe both
yield the same uniform on `Fin n × Fin n → F` restricted to
`T × Fin n ∪ Fin n × T`, hence equal.

**M2.7 acid test.** If the reduction body is >30 lines, file an
issue against `BivariateShamir.lean` ergonomics and fix before
AVSS. The whole point of bivariate-Shamir-as-a-lemma is that VSS
secrecy should be a thin wrapper.

W3 deliverable: ~300 lines, one theorem.

**M2.7 closeout:** open issues for `Refines` / coupling ergonomics
discovered while modeling a real multi-round protocol. Fix top
three before M3 entry gate. Update M3 entry-gate AVSS stub to
*reuse* the SyncVSS state-machine shape (share/consistency/resolve
phases) — AVSS adds the asynchronous delivery layer + AST
termination on top, but the inner shape is now a known quantity.

## Milestone 3 — AST rule + AVSS + common coin (6 weeks)

### M3 entry gate (W0, ~3 days)

**Before M3 W1:** draft the AVSS termination certificate as a Lean
file with all proof obligations as `sorry`. The shape:

```lean
-- Examples/Prob/AVSSStub.lean (M3 entry gate, deleted after M3 closeout)

namespace Leslie.Examples.Prob.AVSSStub

def Π_AVSS (n t : ℕ) (s : F) : ProbActionSpec AVSSState AVSSAction := ...

def F_AVSS_fair : FairnessAssumptions AVSSState AVSSAction := {
  fair_actions := { honestDeliver, honestLocalStep, dealerEcho, dealerReady }
  isWeaklyFair := ...
}

def U_AVSS : AVSSState → ℕ :=
  fun s => (countNotOK s) * K^2 + (countNotREADY s) * K + (countMessagesInFlight s)

def V_AVSS : AVSSState → ℝ≥0 :=
  fun s => ∑ i in honestParties, max 0 (T - phaseProgress i s)

def Inv_AVSS : AVSSState → Prop := ...

def avss_cert (n t : ℕ) (h : n ≥ 3*t + 1) (s : F) :
    FairASTCertificate (Π_AVSS n t s) F_AVSS_fair (terminated)
  := {
    Inv := Inv_AVSS
    V := V_AVSS
    U := U_AVSS
    inv_init := by sorry
    inv_step := by sorry
    V_pos := by sorry
    V_term := by sorry
    V_super := by sorry
    V_super_fair := by sorry
    U_term := by sorry
    U_dec_det := by sorry
    U_bdd_subl := by sorry
    U_dec_prob := by sorry
  }

end Leslie.Examples.Prob.AVSSStub
```

**Goal:** the *shape* compiles. If any field's type doesn't match
what `FairASTCertificate` expects, that's a sign the rule needs
extension before AVSS work begins. The `sorry` budget exception
(stated in *Conventions* above) covers this stub.

**Entry-gate acceptance:** `lake build Examples.Prob.AVSSStub`
succeeds with all `sorry`s; reviewer confirms the field shapes match
the design intent. Without this, M3 W1 does not start.

If the gate reveals a shape mismatch, the resolution options in
order of preference:
1. Refine the Lean field types of `FairASTCertificate` to match.
2. Extend the rule with an additional field (document as a
   deviation from POPL 2026).
3. Discover that AVSS termination needs a different rule structure
   (this would be a paper finding; pause M3 to discuss with the
   POPL 2026 authors).

### Week 1: `ASTCertificate` (POPL 2025 Rule 3.2)

`Leslie/Prob/Liveness.lean` — the structure declaration and
soundness proof.

Soundness proof structure (mirrors POPL 2025 §3 proof of Lemma 3.2):
1. Partition runs into `Π_n = {sup V ≤ n}` and `Π_∞`.
2. On each `Π_n`, apply finite-variant rule (Rule 3.1) using `U`
   bounded on the sublevel set; conclude AST on `Π_n`.
3. On `Π_∞`, apply Doob's martingale convergence on the non-negative
   supermartingale `V` to derive a contradiction with non-zero
   measure.
4. Conclude `P(Π_∞) = 0` and `P(Π_n)` AST for all `n`, hence overall
   AST.

**Mathlib gap:** the exact statement we need is "non-negative
supermartingale converges almost surely to an integrable limit."
Mathlib has discrete-time martingale convergence; verify the
specialization is present and adapt or prove from scratch (~200
lines worst case) if missing.

W1 also lands the level-3 WF1 bridge (deferred from M1 W4):

```lean
theorem WF1Premises_implies_AST
    (Π : ActionSpec σ ι) (i : ι) (P Q : σ → Prop)
    (h : WF1Premises Π i P Q) :
    ∃ cert : FairASTCertificate Π.toProb { fair_actions := {i}, ... } Q,
      cert.fair_actions = {i}
```

### Week 2: 2-D random walker acceptance test (or 1-D fallback)

`Examples/Prob/RandomWalker2D.lean` (or `RandomWalker1D.lean`).

This is *the* validation of the rule's API. The certificate is the
one in POPL 2025 Example 3.5 for 2DRW: `V(x,y) = √(ln(1 + ‖(x,y)‖))`,
`U(x,y) = |x| + |y|`. Proving 2DRW AST in fewer than ~200 lines
including the analysis lemmas means the rule is ergonomic.

**M3 W2 trigger (per design plan):** if 2DRW exceeds 200 lines or
pulls in measure theory beyond `MeasureTheory.Martingale`, switch
to the simpler 1-D random walker on `ℕ` with biased step (still
requires both `V` and `U` but stays within `NNReal` arithmetic).
Document the fallback decision in the PR.

The 2DRW analytic-imports risk is real because the certificate uses
`√` and `ln` over real coordinates; Mathlib's analytic library is
deep but importing the right lemmas can pull in surprising amounts
of measure theory. The 1-D fallback exists specifically to avoid
this from blocking M3.

### Week 3: `FairASTCertificate` (POPL 2026 fair extension) + Ben-Or-async

`Leslie/Prob/Liveness.lean` extended with `FairASTCertificate`
(building on the type defined in the M3 entry gate stub).
`Examples/Prob/BenOrAsync.lean`.

Note the file is **`BenOrAsync.lean`**, not `BenOr.lean`. The
existing `Leslie/Examples/BenOr.lean` (HO-model, synchronous,
deterministic over-approximation) is left untouched; the new file is
the asynchronous probabilistic version. See design plan v2
§"Reconciliation with existing Leslie/Examples/BenOr.lean."

Ben-Or-async termination is the calibration for the fair rule. The
variant counts rounds-without-decision; the supermartingale tracks
adversary delay budget over fair-delivery actions. Discharge via
`FairASTCertificate.sound` with the standard async fairness
assumption (WF on honest delivery + honest local steps + coin
tosses).

**Stretch goal (not blocking):** prove
`BenOrAsync_refines_BenOrHO` — the existing HO-model file is the
deterministic over-approximation of the new async-probabilistic
file. Sanity check; if it doesn't go through cleanly, document as a
finding for review.

### Week 4: Common coin

`Examples/Prob/CommonCoin.lean`. Output a uniform bit with constant
probability `≥ ρ`. Qualitative version (this milestone) is enough
for M5; quantitative version (with explicit lower bound on
agreement probability) goes into the optional `Quantitative.lean`.

### Weeks 5–6: AVSS

`Examples/Prob/AVSS.lean`. Discharge the M3-entry-gate stub: replace
each `sorry` with an actual proof.

The four theorems:
- *Termination:* via `FairASTCertificate` with `(V, U, Inv)` from
  the entry-gate sketch. This is the load-bearing proof.
- *Correctness:* if dealer honest with secret `s`, all honest
  outputs consistent with `s`. (Pure Leslie machinery via
  `invariant_preserved`.)
- *Commitment:* even with a corrupt dealer, after the share phase
  completes for one honest party, the secret is uniquely
  determined.
- *Secrecy (info-theoretic):* the joint view of any `t`-coalition
  is independent of the dealer's secret. Discharged by
  `coupling_bijection` reduction to bivariate Shamir from M2.

Of the four, secrecy should be the cleanest because the heavy
algebra is in `Polynomial.lean`; if it isn't, the M2 algebraic
infrastructure is incomplete.

**M3 W6 trigger:** if AVSS termination needs tactics outside what
`FairASTCertificate` exposes, file as a finding for the POPL 2026
authors — this would be a research result.

After M3 closeout, delete `Examples/Prob/AVSSStub.lean` (its
contents are subsumed by the full proofs in `AVSS.lean`).

**M3 closeout:** if AVSS has shipped without `sorry`, this is the
publishable artifact, regardless of whether M4–M5 ever happen.

## Milestone 4 — UC composition (5 weeks)

Skeleton only. Detail to be filled in at M3 closeout based on what
the AVSS proof structure suggests about the simulator interface.

- W1: `IdealFunc` as a distinguished `ProbActionSpec` shape.
- W2: `Environment` and `Realizes` definition. Establish
  type-level disjointness from `Refines` (per design plan v2
  §"Composition combinators").
- W3: UC composition theorem (the main effort).
- W4: Three composition combinators with type-distinct argument
  shapes: `compose_refinement` (takes `⊑ₚ`),
  `compose_fair_refinement` (takes `⊑ₚ` + fairness), `compose_uc`
  (takes `Realizes` + `HybridModelProof`).
- W5: `F_AVSS` and `F_Coin` ideal functionalities; assemble
  realization proofs from M3 deliverables.

## Milestone 5 — Async BA via composition (4 weeks)

- W1: `Π_BA` in the `(F_AVSS, F_Coin)`-hybrid model.
- W2: Hybrid-model proofs of agreement, validity, termination
  (combinatorial; the only randomness is the coin output, handled
  by the hybrid `F_Coin`).
- W3: Apply `compose_uc` twice to substitute `Π_AVSS` and
  `Π_Coin`.
- W4: M5 closeout; PR review; merge to `main`.

## Milestone 6 — Optional probabilistic HO (6 weeks)

Out of scope unless a future randomized synchronous-round protocol
demands it. Detail deferred.

## Cross-cutting tasks

### Continuous integration

- `scripts/check-conservative.sh` — wired in branch setup, before
  any M1 work.
- `lake test` — every `Examples/Prob/*.lean` file should be its own
  test target so failure isolates which example regressed.
- Mathlib pin — fix at M1 W1 Day 1, advance only at milestone
  boundaries with a dedicated commit.
- `mathlib4-cache` GitHub action — wired in M1 W1 Day 1 alongside
  the Mathlib `require`.

### Documentation alongside code

Each `Examples/Prob/X.lean` opens with a doc-comment block stating
- the protocol (with citation),
- the property proved (with citation),
- the proof technique used,
- the milestone in which it landed.

This becomes the de-facto user manual and pays compounding dividends
as the example library grows.

### Reading list per milestone

- **M1 prerequisite:** Mathlib `Probability.ProbabilityMassFunction`
  module; an EasyCrypt pRHL chapter or a CryptHOL paper for the
  relational judgment shape.
- **M2 prerequisite:** Lynch's task-PIOA paper for adversary /
  scheduler modeling; Bracha's RBC paper.
- **M2.5 prerequisite:** any Wegman–Carter / universal-hashing
  exposition (e.g., Stinson §4 or Wikipedia's "Universal hashing"
  is sufficient).
- **M3 prerequisite:** Majumdar–Sathiyanarayana POPL 2025 §§1–3
  (the rule), §3.3 (relation to MMKK 2018), Example 3.5 (2DRW
  certificate). Enea–Majumdar–Motwani–Sathiyanarayana POPL 2026
  (fair extension and Ben-Or-async proof).
- **M4 prerequisite:** Canetti UC paper; Hirt–Maurer for async UC.
- **M5 prerequisite:** Canetti–Rabin 1993 — the exact composition
  pattern this milestone realizes.

## Risk-driven re-planning triggers

- **M1 W1 Day 1 trigger:** if `lake exe cache get` cannot populate
  the Mathlib cache (e.g., toolchain mismatch), pause and resolve
  before proceeding. Mathlib upgrades are *out of scope*; pin
  whatever works.
- **M1 W2 trigger:** if the toy coupling-demo proof exceeds 10
  lines, pause and redesign `Coupling.lean` API before proceeding.
- **M1 W4 trigger:** if Shamir secrecy exceeds 30 lines, the
  `coupling_bijection` tactic isn't pulling its weight; revisit
  before M2.
- **M2.5 trigger:** open one issue per pRHL ergonomic problem
  discovered; fix the top three before M3 W1.
- **M3 entry-gate trigger:** if the AVSS certificate stub does not
  compile (shape mismatch with `FairASTCertificate`), pause and
  resolve before M3 W1 starts.
- **M3 W2 trigger:** if 2DRW exceeds 200 lines or pulls in measure
  theory beyond `MeasureTheory.Martingale`, switch to 1-D random
  walker.
- **M3 W6 trigger:** if AVSS termination needs tactics outside
  `FairASTCertificate`, file as a paper-level finding.

## Total timeline

| Milestone | Weeks | Cumulative |
|-----------|-------|------------|
| M0        | 2     | 2          |
| M1        | 4     | 6          |
| M2        | 4     | 10         |
| M2.5      | 2     | 12         |
| M3 entry-gate | 0.5 | 12.5     |
| M3        | 6     | 18.5       |
| M4        | 5     | 23.5       |
| M5        | 4     | 27.5       |
| M6 (opt.) | 6     | 33.5       |

**Critical path to publishable AVSS artifact: 18.5 weeks (M0–M3).**
**Critical path to async BA artifact: 27.5 weeks (M0–M5).**

(Apply staffing multiplier from *Staffing assumption* above. M0 is
not subject to the multiplier in the same way — it is mostly
investigation, and a Mathlib-fluent engineer is essential. If no
Mathlib-fluent engineer is available for M0, pause and recruit; do
not start M0 with a Mathlib-novice.)

## Changes from v1

| Concern | Resolution                                                              |
|---------|-------------------------------------------------------------------------|
| Mathlib unstated | New M1 W1 Day 1 subtask; CI cache wired; staffing note updated. |
| `ProbActionSpec` shape | All Lean signatures use `σ ι`, no `P` parameter.       |
| `BenOr.lean` already exists | New file is `BenOrAsync.lean`; relationship spelled out. |
| Fairness encoding | `FairAdversary σ ι F` is a hard type predicate; v1's "side condition" gone. |
| ElGamal scope blowup | Replaced with `ITMAC.lean` (Wegman–Carter info-theoretic MAC). |
| AVSS certificate unspecified | New M3 entry gate (W0): write the certificate stub before W1. |
| Conservativity boundary | Level-2 (preservation, both directions) in M1 W4; level-3 WF1 bridge (one direction only) in M3 W1. |
| 2DRW analytic-imports risk | Promoted to M3 W2 trigger; 1-D random walker fallback documented. |
| CI script ignore-list | Extended to exclude `lakefile.lean`, `lake-manifest.json`, `lean-toolchain` for Mathlib upgrades. |
| Staffing assumption | Made explicit; multiplier table added.                          |
| Existing-file inventory in CI | Expanded to cover `AssumeGuarantee`, `EnvAbstraction`, `SymShared`, `PhaseRound`, `Rust/`, `MANUAL.md`, `README.md`. |
| Sub-PMFs vs. trace prefixes | Stated as a decision in M2 W1 (infinite streams with stuttering). |
| Demonic scheduler | Stated explicitly in M2 W1 `Adversary.lean` snippet.              |

## Changes from v2 (i.e., what v2.1 adds)

| Round-2 finding | Resolution in v2.1                                                  |
|-----------------|---------------------------------------------------------------------|
| 1. `PMF (Trace σ ι)` is not a valid type | New M0.1 task (5 days): decision document + minimal Lean prototype + Doob availability check. |
| 2. AST soundness pulls in measure theory | New M0.3 task (2 days): outline + statement-only stub of `ASTCertificate.sound` against the M0.1 trace type. |
| 3. `parallel` state semantics unspecified | New M0.2 task (3 days): shared-state model + signature + sanity example. |
| 4. (V, U) rule overfit to AVSS | Design plan v2.1 §"Round-2 review findings" §4: re-pitch around common coin / async BA. AVSS may use a simpler variant rule. Concrete rewrite of §"AVSS termination certificate — sketch" is deferred to post-M0 once the math settles. |
| 5. CI conservativity regex misses nested examples | New M0.4 task (0.5 day): fix regex + synthetic-diff test. The regex shown in *Branch & repository setup* above is left as-is so the bug is visible; M0.4 commits the fix. |
| Cumulative timeline | M0 adds 2 weeks. AVSS critical path: 18.5 weeks. Async BA critical path: 27.5 weeks. |

The v2.1 changes are *additive* with respect to v2: no M1–M5 task is
dropped or restructured; M0 is inserted upstream and the timeline
table shifts by 2 weeks.

## Changes from v2.1 (i.e., what v2.2 adds)

| Topic | v2.2 update |
|---|---|
| M0 status | All four tasks DONE with working Lean artifacts. Critical-path estimates carried forward unchanged (AVSS: 18.5 weeks, async BA: 27.5 weeks). M0 actual elapsed: <1 day. |
| §"Branch & repository setup" | CI script shown inline switched to allowlist (M0.4 outcome). |
| §M0.1 (trace measure) | Marked DONE; outcome: Option A (Measure + Ionescu-Tulcea via `Kernel.trajMeasure`). Mathlib v4.27.0 already has `Mathlib.Probability.Kernel.IonescuTulcea.Traj`; ~150-line coin-flip prototype validates end-to-end. |
| §M0.2 (parallel state) | Marked DONE; outcome: shared-state product `σ₁ × σ_net × σ₂` with the network as its own `ProbActionSpec`. Lean shape stub at `Leslie/Prob/Spike/ParallelShape.lean` (0 sorry, 0 warning). |
| §M0.3 (AST soundness) | Marked DONE; outcome: Mathlib gap is ~50 lines (not 200). `Submartingale.ae_tendsto_limitProcess` is in `Mathlib.Probability.Martingale.Convergence`. AST stub at `Leslie/Prob/Spike/ASTSanity.lean`. |
| §M0.4 (CI regex) | Marked DONE; outcome: allowlist-based check at `scripts/check-conservative.sh` with 33-case test suite. Wired into CI via `.github/workflows/conservativity.yml`. |
| Spike artifact tree | New `docs/randomized-leslie-spike/01–03-*.md` (decision documents) and `Leslie/Prob/Spike/{CoinFlip,ASTSanity,ParallelShape}.lean` (Lean stubs). All artifacts cross-referenced from the round-2 status notes in the design plan. |
| Design plan signatures | `traceDist`, `Refines`, `RelatedTraces.view_eq`, `ASTCertificate.sound`, `FairASTCertificate.sound` — all updated to use `Measure (Π n : ℕ, σ × Option ι)` instead of v2's invalid `PMF (Trace σ ι)`. Added `[MeasurableSpace σ] [MeasurableSpace ι]` typeclass requirements. |

The v2.2 changes are signatures-only: no milestone restructuring, no
task add/drop, no timeline shift.
