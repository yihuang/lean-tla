# M2 W2 polish — lift `traceDist` to the real conditional kernel

The current `stepKernel` (commit `f857f00`) is **stutter-only**: every
trace is `(s₀, none), (s₀, none), ...`. This task replaces it with
the full schedule-and-gate-conditional kernel that actually reflects
the adversary's choices and the spec's effect distributions.

Per the M2 W1 polish document (file header in
`Leslie/Prob/Trace.lean`), three paths were available; the user
chose path **(2)**: typeclass refinement, specifically adding
`[Countable ι]` to expose the schedule's measurability.

## Goal

Realize the conceptual definition documented in
`Leslie/Prob/Trace.lean`'s "Per-step kernel" section:

```
match A.schedule h.toList with
| none   => Dirac (currentState h, none)
| some i =>
    if (spec.actions i).gate (currentState h)
    then ((spec.actions i).effect ...).toMeasure.map (·, some i)
    else Dirac (currentState h, none)
```

The `traceDist` body must remain `Kernel.trajMeasure ...` over a
`stepKernel` that has this branching structure. The current
`Trace.lean` has a stutter-only realization with detailed
documentation of the blockers; replace that with the real one.

## Repository state

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `feat/randomized-leslie-m2-w1` (already checked out)
- Mathlib v4.27.0 in `lakefile.lean`
- Build: `lake build Leslie.Prob.Trace`, `lake build`
- Conservativity gate: `bash scripts/check-conservative.sh`

## Strategy: `[Countable ι]` plus what's needed

Add `[Countable ι]` as a typeclass requirement on `stepKernel`
and `traceDist`. This alone is **likely insufficient** — see
"Reasoning about measurability" below — so additional typeclasses
or hypotheses may be needed. The user's preference: keep the
typeclass overhead minimal.

### Reasoning about measurability

For `A.schedule ∘ FinPrefix.toList : FinPrefix σ ι n → Option ι`
to be measurable:

1. With `MeasurableSpace (Option ι) := ⊤` (already declared
   locally), every set in `Option ι` is measurable. To make
   `A.schedule ∘ toList` measurable, every preimage in
   `FinPrefix σ ι n` must be measurable.

2. With `[Countable ι]`, `Option ι` is countable; every set is a
   countable union of singletons. So measurability of
   `A.schedule ∘ toList` reduces to measurability of each
   singleton-preimage `(A.schedule ∘ toList)⁻¹{x}` for
   `x : Option ι`.

3. The singleton-preimage in `FinPrefix σ ι n` is the set of
   histories on which `A.schedule` returns `x`. For an arbitrary
   `A.schedule`, this set is *not* automatically measurable in
   the natural Pi σ-algebra on `FinPrefix`.

So `[Countable ι]` alone doesn't close the gap. Three sub-options:

   **(2a)** Also require **`[Countable σ]`** plus
   `MeasurableSpace σ := ⊤` on the typeclass (or use
   `MeasurableSingletonClass σ` plus a default discrete
   instance). Then `FinPrefix σ ι n` has a discrete σ-algebra,
   and every function from it is measurable. Accepts the
   restriction that all our state types (Bracha RBC, AVSS, etc.)
   are countable — which is true.

   **(2b)** Require **`Measurable A.schedule`** as a field of
   the `Adversary` type (or via a refined `MeasurableAdversary`
   subtype). Cleaner separation; doesn't restrict σ.

   **(2c)** Require **measurability as a hypothesis on
   `traceDist`**, threaded through the signature.

**Pick whichever gives the cleanest signature for downstream
M2 W3 (`BrachaRBC.lean`).** Document the choice in the file's
header.

### Decidable gates

The gate-conditional branch needs `Decidable ((spec.actions i).gate
(currentState h))`. Three handles:

- Use `Classical.dec` (always works; pulls `Classical.choice`
  axiom which we already use elsewhere).
- Add `[∀ i s, Decidable ((spec.actions i).gate s)]` (cleaner
  type-level constraint).
- Refactor `ProbGatedAction.gate` to be `σ → Bool` instead of
  `σ → Prop` (invasive — affects PR #25's signatures, not
  recommended).

Recommendation: use `Classical.dec`. It's the least invasive.

## Constraints

1. **Don't change PR #25 signatures.** `evals_uniform`,
   `bivariate_evals_uniform`, `shamir_secrecy*` are merged-quality
   and shouldn't be touched.
2. **Allowed paths**: `Leslie/Prob/Trace.lean` (target),
   `Leslie/Prob/Adversary.lean` (if you choose option 2b),
   `Leslie/Prob/Refinement.lean` (signature propagation),
   other `Leslie/Prob/*` for helpers, `docs/randomized-leslie-spike/`.
   Do NOT touch existing main-branch Leslie code.
3. **No new dependencies** in `lakefile.lean`.
4. **Don't push** to origin.

## Acceptance criteria

- `lake build Leslie.Prob.Trace` green with **0 sorries**, with
  the `stepKernel` body actually branching on schedule and gate
  (not the stutter-only realization).
- `lake build` (full project) green; same 4 pre-existing project
  sorries unchanged. The 2 sorries in `Leslie/Prob/Refinement.lean`
  may remain; or may close if the new kernel makes them tractable.
- `bash scripts/check-conservative.sh` passes.
- File header documents which sub-option (2a/2b/2c) was chosen
  and why.
- One commit on `feat/randomized-leslie-m2-w1` describing the
  approach.

## What to do if 2a/2b/2c are all blocked

Document specifically which Mathlib lemma you needed but couldn't
find / which typeclass made the proof go through but had downstream
consequences. Do NOT regress to stutter-only (the current state).
A partial result — e.g., kernel is correct for the `none` schedule
branch + still stutter for the `some i` case — is acceptable
progress if you can't get the full conditional working in budget.

## Reference

- `Leslie/Prob/Trace.lean` — target file with extensive
  documentation of the existing stutter-only realization.
- `Leslie/Prob/Spike/CoinFlip.lean` — working example using
  `Kernel.trajMeasure` with a `Kernel.const` (history-independent)
  kernel; useful for understanding the `Kernel.trajMeasure` API.
- `Mathlib/Probability/Kernel/Basic.lean` — Kernel basics,
  including `Kernel.deterministic`, `Kernel.const`,
  `Kernel.piecewise`, `Kernel.ofFunOfCountable`.
- `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` — the
  Ionescu-Tulcea trajectory.

## Branch state at task start

```
f857f00 feat(M2 W1 polish): close traceDist body with stutter-only stepKernel
8fc5374 feat(M2 W2): probabilistic refinement — Refines + modal predicates
40041d7 docs: spike task brief for traceDist body proof (M2 W1 polish)
0bd6e55 feat(M2 W1): promote Adversary + Trace stubs to first-class
... (older commits)
```

Sorries on `Leslie/Prob/Trace.lean`: 0 (currently — but the
`stepKernel` body is a deliberate stutter-only simplification
documented as such).
Sorries on `Leslie/Prob/Refinement.lean`: 2 (M2 W2 polish).
