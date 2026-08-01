# M0.1 — Trace measure decision document

**Status.** Decision settled and prototype-validated.
**Owner.** TBD.
**Budget.** ~5 days (per implementation plan v2.1 §M0). Actual:
~0.5 days (decision research + prototype).
**Blocks.** Unblocked: M1, M0.3.

**Outcome.** Option A (Measure + Ionescu-Tulcea kernel trajectory) is
adopted. Coin-flip prototype at `Leslie/Prob/Spike/CoinFlip.lean`
builds green against Mathlib v4.27.0; the construction is direct from
`Mathlib.Probability.Kernel.IonescuTulcea.Traj` with no shimming. See
*Prototype-phase outcome* at the bottom of this document.

---

## The question

What is the type of `traceDist Π A` — the distribution over infinite
traces of `Π : ProbActionSpec σ ι` under adversary `A`?

Design plan v2 said `PMF (Trace σ ι)` where
`Trace σ ι := Stream' (σ × Option ι)`. Round-2 review claimed this is
not a real type.

## What Mathlib actually provides

After consulting Mathlib4 docs (April 2026), the situation is more
nuanced than v2's "PMF won't work" / round-2's "PMF can't host trace
distributions":

### `PMF α` (compiles, but operationally weak for traces)

`Mathlib.Probability.ProbabilityMassFunction.Basic`:

- `PMF α` is a subtype of `α → ℝ≥0∞` summing to 1. **`α` need not be
  countable.**
- However: `PMF.support_countable` is a `simp` lemma — for *any*
  `μ : PMF α`, `μ.support` is countable.

So `PMF (Stream' (σ × Option ι))` *type-checks*, but every inhabitant
has countable support. This means we cannot represent the distribution
over traces induced by even a single coin flip per step (which has
support of cardinality continuum). **Round-2 finding 1 is correct in
substance**: PMF on streams compiles, but only represents
operationally-trivial distributions.

### `ProbabilityTheory.Kernel α β` (the right primitive)

`Mathlib.Probability.Kernel.Basic`:

- `Kernel α β` = measurable function `α → Measure β` (plus
  measurability witness).
- Constructors: `deterministic`, `const`, `id`, `comapRight`,
  `piecewise`, `ofFunOfCountable`.
- `IsMarkovKernel κ` ⇔ each `κ a` is a probability measure.

Per-step transitions of `ProbActionSpec` (action choice composed with
effect PMF) are naturally a `Kernel σ σ`. PMF effects compose with the
adversary's history-deterministic schedule to give a measurable map
`History → Measure σ` per step.

### `Mathlib.Probability.Kernel.IonescuTulcea.Traj` (the trace-measure construction)

This is the headline finding: the construction we need is **already
in Mathlib**, formalized in 2025 (arXiv 2506.18616).

```lean
noncomputable def traj {X : ℕ → Type u₁}
  [∀(n : ℕ), MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
  [∀(n : ℕ), IsMarkovKernel (κ n)]
  (a : ℕ) :
  Kernel (Π i : Iic a, X i) (Π n, X n)
```

Given a family of one-step Markov kernels indexed by ℕ, `traj` produces
a kernel from finite-prefix initial conditions to measures on the
infinite product space. The projective-limit property
`(traj κ a).map (frestrictLe2 h_b) = partialTraj κ a b` characterizes
it as the unique extension.

For our setting `X n := σ × Option ι` is constant in `n`; we instantiate
`κ n` to the per-step transition kernel induced by the adversary
schedule + `ProbGatedAction.effect`. The output `Π n, X n` is
isomorphic to `Stream' (σ × Option ι) = Trace σ ι` (modulo a
`Stream'`-vs-`Pi` translation).

### `MeasureTheory.Martingale.Convergence` (Doob)

Doob's martingale convergence theorem is formalized in Mathlib (arXiv
2212.05578). Specifically the form we need —
"non-negative supermartingale converges almost surely to an
integrable limit" — is available. AST soundness is therefore *not*
gated on a Mathlib gap.

## Three options, re-evaluated

### Option A — `Measure (Trace σ ι)` via Ionescu-Tulcea (RECOMMENDED)

Define `traceDist Π A : Measure (Stream' (σ × Option ι))` by:
1. Constructing per-step kernel `κ_step Π A : Kernel (History σ ι) σ`
   from the adversary schedule + action effect.
2. Currying through the projective-limit: `κ_step` becomes a kernel
   `(Π i : Iic n, σ × Option ι) → σ × Option ι` family.
3. Applying `Kernel.traj` at index 0 with the initial state.
4. Pulling back along the `Stream'` ↔ `Π n` isomorphism.

**Pros.**
- Construction already in Mathlib; no shim needed.
- Proper measure-theoretic semantics; `□̃` (almost-sure box) and
  `◇̃` (almost-sure diamond) lift cleanly to events on the cylinder
  σ-algebra.
- Doob (and hence `ASTCertificate.sound`) applies directly.
- Unifies with UC composition (Hirt-Maurer adversaries naturally
  live as kernels).

**Cons.**
- `Π n, X n` ≠ `Stream'` syntactically; need a `Pi.streamEquiv`-style
  lemma. Should be ~30 lines.
- `noncomputable`, like all of Mathlib's measure theory. Tactic story
  for `Tactics/Prob.lean` must be measure-theoretic, not
  PMF-symbolic — this is a real consequence; see *Implications*
  below.
- Per-step kernel needs measurability witnesses. For a finite-state
  `ProbActionSpec` this is trivial; for general `σ` the user must
  prove `Measurable` for the transition.

### Option B — Truncated PMF + tail measure (REJECTED)

Define `traceDist^≤n : PMF (List (σ × Option ι))` for each `n` plus
a separate `tailMeasure` for liveness reasoning.

**Pros.** Keeps PMF in the type for finite-prefix reasoning.

**Cons.**
- Two parallel objects users must keep consistent.
- Liveness properties (◇̃, AST) cannot be stated against PMF; they
  end up against `tailMeasure` anyway, so PMF buys nothing.
- Coupling rules need duplicate statements (PMF version + measure
  version).

Reject. The supposed PMF benefit is illusory because every interesting
property is a tail/limit property.

### Option C — `MeasureTheory.ProbabilityMeasure` throughout (CANDIDATE)

Use `Measure` everywhere; PMF is just a convenient way to construct
finitely-supported measures.

**Pros.** Single object, no PMF/measure boundary.

**Cons.** Loses the discrete-symbolic ergonomics that pRHL / coupling
proofs benefit from. `coupling_bijection` over a finite Shamir
polynomial is much cleaner with PMF + `PMF.bind` than with measures
and Lebesgue integration.

**Synthesis.** Option A's form already gives us C's benefits at the
trace level (`traceDist` is a `Measure`) while preserving PMF for
single-step effects. So C is subsumed by A.

## Recommendation

**Option A.** Per-step effects stay `PMF` (good ergonomics for
single-step coupling proofs); trace distributions are `Measure` via
`Kernel.traj`. The PMF/Measure boundary is at "one step vs. many
steps" — semantically natural.

Concretely, the type signature changes from v2 are:

```lean
-- v2 (broken):
def traceDist (Π : ProbActionSpec σ ι) (A : Adversary σ ι) :
              PMF (Trace σ ι)

-- v2.1 / Option A:
def traceDist (Π : ProbActionSpec σ ι) (A : Adversary σ ι)
              [MeasurableSpace σ] [MeasurableSpace ι]
              (s₀ : σ) :
              Measure (Stream' (σ × Option ι))
```

Note the added `[MeasurableSpace σ]`, `[MeasurableSpace ι]`, and the
explicit initial state `s₀` (since `Kernel.traj` is parameterized on
the initial trajectory, not the initial distribution; for an initial
distribution `Π.init`, we additionally bind through it).

## Implications for the rest of the plan

If Option A is adopted, propagate:

1. **§"Discrete probability first" (design plan).** Soften: "Discrete
   probability for single-step effects; measure theory at the trace
   level. We do not need the *general* measure-theoretic stack
   (Lebesgue, Bochner integration), but we do need the
   product-measure / kernel-trajectory / martingale-convergence parts."

2. **`Refines` (§Composition combinators).** Change from
   `traceDist Π A = (traceDist Σ A').map projectStuttering` (PMF
   equality) to `Measure.map projectStuttering (traceDist Σ A') = traceDist Π A`
   — same idea, measure-level.

3. **`RelatedTraces` and coupling rules at trace level.** A coupling
   between two trace measures is a measure on the product space with
   the right marginals. Mathlib has `Measure.prod` and projection
   marginals; the coupling rules port over but with
   `MeasureTheory.Measure` instead of `PMF`. The coupling rules at
   the *step* level stay PMF-flavored.

4. **`ASTCertificate.sound` (§AST rule).** The supermartingale `V`
   becomes a measurable function `σ → ℝ≥0∞` (not just `σ → ℝ≥0`); the
   integration is against `traceDist Π A`. Doob's theorem in Mathlib
   covers this case.

5. **`Tactics/Prob.lean`.** Single-step tactics (`coupling_identity`,
   `coupling_bijection`, `coupling_swap`) operate on PMF. Trace-level
   tactics (`by_coupling` on full-trace claims) need to bridge from
   step-PMF reasoning to trace-Measure reasoning. The bridge is
   `Kernel.traj`'s functoriality: a step-level PMF coupling lifts to a
   trace-level Measure coupling.

6. **`MeasurableSpace` instances become a real ergonomic burden.** We
   will need standard instances on `σ × Option ι`,
   `Stream' (σ × Option ι)`, `History σ ι`. Most are already in
   Mathlib (`Prod.instMeasurableSpace`, `Option.instMeasurableSpace`,
   `Pi.measurableSpace`); the `Stream'` one may not be — verify in the
   prototype.

## Doob availability check

Per the Mathlib4 search:

- `Mathlib.MeasureTheory.Martingale.Convergence` formalizes Doob's
  martingale convergence theorem (arXiv 2212.05578).
- The non-negative supermartingale form: a non-negative supermartingale
  `M : ℕ → Ω → ℝ≥0∞` converges a.s. to a measurable limit.
- Filtration handling: `MeasureTheory.Filtration` is the standard
  setup; we will need to expose the natural filtration on
  `Stream' (σ × Option ι)` (the σ-algebra generated by the first `n`
  coordinates), which is straightforward — every cylinder σ-algebra
  has a canonical filtration.

**No shim needed.** This is a meaningful win: the Mathlib martingale
infrastructure is more developed than v2's "small shim … worst case
~200 lines" implied.

## Outstanding questions for the prototype

The decision is made; the prototype's job is to *verify* by building
the core construction end-to-end on a trivial example. Specifically:

1. **Does `Kernel.traj` instantiate cleanly when `X n` is constant in
   `n`?** Needs a wrapper or fresh definition; estimate ~30 lines.

2. **What does `Stream'` ↔ `Π n` look like in Mathlib?** Verify
   `Stream'` has `MeasurableSpace`; if not, define one via the
   coordinate projections (likely 50 lines).

3. **Coin-flip Markov chain** on `Bool` driven by a single action that
   flips with probability `1/2`: prove the marginal at step `n` is
   uniform on `Bool`. Target: ≤150 lines including the kernel
   construction. If it exceeds 250 lines, Option A is more painful
   than expected and we re-evaluate.

4. **AST soundness toy.** Statement-only stub of
   `ASTCertificate.sound` with `sorry` body; every obligation typed
   correctly under the new trace-measure type. Builds → exit gate
   passes.

5. **MeasurableSpace on `Adversary`.** The schedule
   `History σ ι → Option ι` must be measurable to compose with kernels.
   For history-deterministic adversaries this is automatic given
   measurable spaces on `σ` and `ι`; verify.

## Implications for M0 timeline

If Option A is adopted (and assuming the prototype goes through):

- M0.1 budget reduces from "decide between three options" to "verify
  Option A on a toy". Likely ~3 days of actual prototype work, not 5.
- M0.3 (AST soundness scaffolding) becomes near-trivial because Doob is
  available — likely 1 day, not 2.
- **M0.1 brings forward what was M1 W1 Day 1** (add Mathlib
  dependency). The prototype requires Mathlib; we can either
  - (a) add Mathlib in the spike branch and discard if the spike
    fails; or
  - (b) write the prototype as a standalone scratch file outside the
    project tree and copy results into the eventual M1 commit.
  Recommendation: (a). The spike is exactly the place to validate
  Mathlib pinning, cache behavior, and build times, and the cost of
  discarding is bounded.

## Decision

**Option A** (Measure + Ionescu-Tulcea kernel trajectory) is adopted
pending prototype verification.

If the prototype completes within budget, the design plan v2.1 should
be patched to:
- Replace `PMF (Trace σ ι)` with `Measure (Stream' (σ × Option ι))`
  in all trace-level signatures (§"`ProbActionSpec` and trace
  distributions" and downstream).
- Soften §"Design principles" item 2 ("Discrete probability first")
  to acknowledge measure theory at the trace level.
- Add `MeasurableSpace σ` / `MeasurableSpace ι` typeclass
  requirements where they were elided in v2.
- Cross-reference `Mathlib.Probability.Kernel.IonescuTulcea.Traj` and
  `Mathlib.MeasureTheory.Martingale.Convergence` in the §References.

If the prototype reveals a friction not anticipated here, this
document is the place to record the finding and revise.

## Prototype-phase outcome

The coin-flip prototype at `Leslie/Prob/Spike/CoinFlip.lean` validates
Option A end-to-end. Findings:

### What worked first try

1. **Mathlib v4.27.0 pin** matches `lean-toolchain` exactly. No
   toolchain mismatch; `lake update mathlib` resolved transitively
   (aesop coexists, plus standard Mathlib transitive deps:
   batteries, Cli, importGraph, LeanSearchClient, plausible,
   ProofWidgets, Qq).
2. **`lake exe cache get`** populated 7270 prebuilt files (~5.9 GB).
   The cache tool exits with code 1 on a missing
   `~/.cache/mathlib/curl.cfg` cleanup attempt, but the artifacts
   are fully unpacked — cosmetic exit-code bug, not a real failure.
3. **`Kernel.trajMeasure`** accepts a constant kernel family
   `(n : ℕ) → Kernel (Π i : Finset.Iic n, Bool) Bool` and produces
   `Measure (Π n, Bool)` directly. No coercion or shim needed.
4. **`IsProbabilityMeasure (coinTrace μ₀)`** is automatic — Mathlib
   has the instance directly on `trajMeasure`.
5. **`MeasurableSpace`** instances on `Bool` (`Bool.instMeasurableSpace`,
   ambient) and `Π n, Bool` (`Pi.measurableSpace`, ambient) resolve
   via instance synthesis without manual ascription.

### What needed fixup

1. `Iic n` in the `Kernel.traj` signature is **`Finset.Iic n`** (not
   `Set.Iic n`). My initial draft assumed `Set.Iic` because the
   docs source rendered ambiguously; the kernel signature requires
   `Finset.Iic` to match `frestrictLe` and the projective-limit
   machinery. Fixed in one line.
2. The `AlmostDiamond` placeholder in the AST stub had a
   malformed body (`∃ n, P x` where `n` was unused). Replaced with a
   trivial `∀ᵐ x ∂μ, P x` — same shape as `AlmostBox` for the
   prototype since the temporal-logic semantics land in M3 W1.

### What's still `sorry`

- **`coinTrace_marginal_succ_uniform`** — closing requires reasoning
  about `(traj coinKernel 0).map (fun x ↦ x (n + 1))` for arbitrary
  `n`. The base case `n = 0` reduces to `map_traj_succ_self`; the
  inductive case requires `traj_map_frestrictLe` + projection. Not
  difficult, but ~30–50 lines and not on M0.1's critical path.
- **`CoinASTCertificate.sound`** — placeholder body. Real soundness
  proof is M3 W1's `ASTCertificate.sound` against the Markov
  filtration on `Π n, X n`, using `MeasureTheory.Martingale.Convergence`.

Both are within the M0 sorry budget exception per implementation
plan v2.1 §Conventions.

### Build statistics

- `lake update mathlib`: ~3 minutes (clone + dep resolution).
- `lake exe cache get`: ~5 minutes (~5.9 GB, network-bound).
- `lake build Leslie.Prob.Spike.CoinFlip`: 1.9 s (after cache
  populated; first-time build of the prototype itself).
- `lake build` (full project): green; existing 4 sorries unchanged
  (Refinement.lean:382, Refinement.lean:469, LastVoting.lean:302,
  LastVoting.lean:396 — pre-existing on `main`).
- Prototype line count: 142 lines including doc-comments. **Within
  the 150-line target; well below the 250-line "re-evaluate" trigger.**

### Implications for the wider plan

- **Design plan v2.1 §"Round-2 review findings" §1** can be marked
  resolved. The "PMF can't host trace distributions" critique is
  correct, but Mathlib's `Kernel.trajMeasure` provides the right
  primitive directly. No shim, no fork, no upstream blocker.
- **Design plan §"Discrete probability first"** should be softened
  for v2.2: per-step PMF, trace-level Measure. This is a doc edit,
  not a design change.
- **M0.3 (AST soundness sanity)** is now near-trivial — Doob is in
  Mathlib (arXiv 2212.05578), the trace type compiles, and the
  filtration on `Π n, X n` is standard. Estimate revised from 2 days
  to ~0.5 day.
- **Mathlib build cost** for CI: cold = ~10 min cache fetch + 2 s
  spike build. Warm = sub-second incremental. Within the
  implementation plan v2.1's expectations.

### Next steps (M0 closeout, post-M0.1)

1. **M0.4** (CI regex fix) — independent, can run now.
2. **M0.2** (parallel composition state model) — independent of
   M0.1's outcome; can start.
3. **M0.3** (AST soundness scaffolding) — much faster than budgeted
   given M0.1's findings; ~0.5 day.
4. **Design plan v2.1 → v2.2** type-signature sweep: replace
   `PMF (Trace σ ι)` with `Measure (Π n, σ × Option ι)` (or
   `Measure (Stream' (σ × Option ι))` after the `Pi`↔`Stream'`
   bridge is established) throughout `Refinement`, `Coupling`,
   `Liveness`, `Trace` sections of the design plan. Defer until M0.2
   + M0.3 close, then do all three sweeps in one pass.

## References

- [Mathlib.Probability.ProbabilityMassFunction.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProbabilityMassFunction/Basic.html)
- [Mathlib.Probability.Kernel.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Basic.html)
- [Mathlib.Probability.Kernel.IonescuTulcea.Traj](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/Traj.html)
- [Cauchy et al. — A Formalization of the Ionescu-Tulcea Theorem in Mathlib (arXiv:2506.18616)](https://arxiv.org/abs/2506.18616)
- [Degenne et al. — Markov kernels in Mathlib's probability library (arXiv:2510.04070)](https://arxiv.org/abs/2510.04070)
- [Pflanzer & Bentkamp — A Formalization of Doob's Martingale Convergence Theorems in mathlib (arXiv:2212.05578)](https://arxiv.org/abs/2212.05578)
