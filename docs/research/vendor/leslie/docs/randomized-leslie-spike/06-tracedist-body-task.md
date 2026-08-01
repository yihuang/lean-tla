# M2 W1 polish — close `traceDist` body

This document is the briefing for the focused proving session that
closes the deferred `sorry` in `Leslie/Prob/Trace.lean`'s `traceDist`.
The signatures landed in PR #26; this finishes the construction.

## Goal

Construct the per-step Markov kernel and `traceDist` body. The
public signature is fixed; do not change it.

```lean
noncomputable def traceDist {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) :
    Measure (Trace σ ι)
```

You may need to add `[IsProbabilityMeasure μ₀]` if the construction
requires it.

## Repository state

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `feat/randomized-leslie-m2-w1` (already checked out)
- Mathlib v4.27.0 in `lakefile.lean`
- Build: `lake build Leslie.Prob.Trace`
- Conservativity gate: `bash scripts/check-conservative.sh`
  (must pass)

## Setup context

Read `Leslie/Prob/Trace.lean` first. Key types:

- `Trace σ ι := Π _ : ℕ, σ × Option ι`
- `FinPrefix σ ι n := Π _ : Finset.Iic n, σ × Option ι`
- `FinPrefix.toList`, `FinPrefix.currentState` — helpers for
  feeding `Adversary.schedule` and extracting the current state.
- Local instance `MeasurableSpace (Option α) := ⊤` already declared
  in the file (Mathlib has no instance for `Option`; ⊤ makes
  everything measurable, fine for discrete actions).

The Mathlib Ionescu-Tulcea API (in
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`):

```lean
noncomputable def Kernel.trajMeasure
    (μ₀ : Measure (X 0))
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] :
    Measure (Π n, X n)
```

For our case `X n := σ × Option ι` (constant family).

## Proof strategy

### Phase 1: Define `stepKernel`

```lean
noncomputable def stepKernel (spec : ProbActionSpec σ ι)
    (A : Adversary σ ι) (n : ℕ) :
    Kernel (FinPrefix σ ι n) (σ × Option ι) where
  toFun h :=
    let s_n := h.currentState
    match A.schedule h.toList with
    | none => Measure.dirac (s_n, none)
    | some i =>
        if h_gate : (spec.actions i).gate s_n then
          ((spec.actions i).effect s_n h_gate).toMeasure.map
            (fun s' => (s', some i))
        else
          Measure.dirac (s_n, none)
  measurable' := by
    sorry
```

### Phase 2: Discharge measurability

The function `toFun` decomposes into:

1. `currentState : FinPrefix σ ι n → σ` — measurable as a
   coordinate projection of a finite Pi-product (use
   `measurable_pi_apply` plus `Prod.fst`).
2. `A.schedule ∘ FinPrefix.toList : FinPrefix σ ι n → Option ι` —
   since `MeasurableSpace (Option ι) = ⊤` (locally), every function
   into `Option ι` is measurable.
3. The match/if branches: use `Measurable.piecewise` or build via
   `Kernel.piecewise` (requires `MeasurableSet` of the branch
   conditions, which all hold under ⊤ on `Option ι`).
4. The `effect` branch: `(spec.actions i).effect s_n h_gate` is a
   `PMF`; convert to `Measure` via `.toMeasure` (PMF has the
   instance); pushforward by `(·, some i)` is measurable since
   `(·, some i) : σ → σ × Option ι` has measurable both
   coordinates.

Key fact: with `MeasurableSpace (Option ι) = ⊤`, **every** function
from any measurable space TO `Option ι` is measurable, and **every
set** of `Option ι` is measurable. This makes the schedule and
gate-result branches automatically measurable.

### Phase 3: `IsMarkovKernel` instance

```lean
noncomputable instance : IsMarkovKernel (stepKernel spec A n)
```

Each branch produces a probability measure:
- `Measure.dirac _` — always probability 1 (`IsProbabilityMeasure_dirac`).
- `(PMF._).toMeasure.map _` — `PMF.toMeasure` is a probability
  measure, and `Measure.map f μ` of a probability measure is also
  a probability measure when `f` is measurable.

Use `Kernel.isMarkovKernel_pieces` or build directly.

### Phase 4: `traceDist` body

```lean
noncomputable def traceDist (spec : ProbActionSpec σ ι)
    (A : Adversary σ ι) (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    Measure (Trace σ ι) :=
  let μ₀_full : Measure (σ × Option ι) :=
    μ₀.map (fun s => (s, (none : Option ι)))
  Kernel.trajMeasure μ₀_full (stepKernel spec A)
```

Note: you may need to add `[IsProbabilityMeasure μ₀]` to the
public signature. If so, also propagate to any callers (currently
none — `traceDist` is freshly stated).

## Constraints

1. **Header fence**: `traceDist`'s signature can change to add
   `[IsProbabilityMeasure μ₀]` if needed (no callers yet). Other
   theorem signatures committed in PR #25 must NOT change.
2. **Allowed paths** (per `scripts/check-conservative.sh`):
   - `Leslie/Prob/Trace.lean` (main target)
   - Other `Leslie/Prob/*` if helpers needed
   - `docs/randomized-leslie-spike/` for notes
3. **No new dependencies** in `lakefile.lean`.
4. **Don't push** to origin. Local commit on
   `feat/randomized-leslie-m2-w1` is fine.

## Acceptance criteria

- `lake build Leslie.Prob.Trace` green with **0 sorries**.
- `lake build` (full project) green; same 4 pre-existing project
  sorries unchanged + ASTSanity sorry unchanged.
- `bash scripts/check-conservative.sh` passes.
- One commit on `feat/randomized-leslie-m2-w1` describing the
  construction.

## What to do if you can't close the proof

If after a serious attempt (≥ 60 min, several Mathlib lemma
searches) you can't close `traceDist` cleanly:

1. Do NOT commit a worse state. Current is 1 sorry on `traceDist`.
2. Document specific Mathlib gaps you hit.
3. Make a partial attempt — e.g., prove the `stepKernel`
   measurability for the special case where `A.corrupt = ∅` and
   the spec has decidable gates. That's still progress.
4. Commit your partial result with a clear message.

## Reference

- `Leslie/Prob/Trace.lean` (the target).
- `Leslie/Prob/Spike/CoinFlip.lean` (working example using
  `Kernel.trajMeasure`; the `coinKernel` is the simplest case of
  the general `stepKernel`).
- `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` (the
  Ionescu-Tulcea library).
- `Mathlib/Probability/Kernel/Basic.lean` (Kernel basics).
- `docs/randomized-leslie-spike/01-trace-measure.md` (M0.1 outcome
  document).

## Branch state at task start

```
0bd6e55 feat(M2 W1): promote Adversary + Trace stubs to first-class
1550358 feat(M0.1): close coinTrace_marginal_succ_uniform
... (M0/M1 history)
```

Currently 1 production sorry (target):
`Leslie/Prob/Trace.lean:~115` — `traceDist` body.

Plus 1 spike sorry (`ASTSanity.lean`, M3 W1 work) and 4
pre-existing project sorries (Refinement, LastVoting), all unchanged.
