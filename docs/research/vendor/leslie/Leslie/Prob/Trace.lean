/-
M2 W1 — `Trace`: types + Ionescu-Tulcea trace measure.

Per design plan v2.2 §"`ProbActionSpec` and trace distributions":
trace distributions are `Measure (Π n : ℕ, σ × Option ι)` via
`ProbabilityTheory.Kernel.trajMeasure` (Ionescu-Tulcea kernel
trajectory). Validated by the M0.1 spike (`Spike/CoinFlip.lean`).

This file:

  * Defines the trace type `Trace σ ι := Π n : ℕ, σ × Option ι`.
  * Defines a finite-prefix type alias used as the input to the
    per-step kernel.
  * Defines the per-step Markov kernel `stepKernel` and the
    trace measure `traceDist`, both **sorry-free**.

**M2 W2 polish status — real conditional kernel (option 2a).**

The per-step kernel `stepKernel` realises the full conceptual
definition: it branches on `A.schedule h.toList`, and for the
`some i` branch it further branches on whether `(spec.actions i).gate`
holds at the current state, returning either the effect-PMF
measure (paired with `some i`) or a `Dirac` stutter.

Three sub-options for handling measurability of
`fun h ↦ A.schedule h.toList : FinPrefix σ ι n → Option ι` were
listed in the M2 W1 polish header (now superseded). We took
**option (2a)**: typeclass refinement requiring

  * `[Countable σ]`, `[MeasurableSpace σ]`, `[MeasurableSingletonClass σ]`
  * `[Countable ι]`, `[MeasurableSpace ι]`, `[MeasurableSingletonClass ι]`

These imply `Countable (FinPrefix σ ι n)` (via
`instCountableForallOfFinite` on `Π _ : Finset.Iic n, σ × Option ι`)
and `MeasurableSingletonClass (FinPrefix σ ι n)` (via the Pi
σ-algebra on a finite product of singleton-measurable types).

Together these unlock `Kernel.ofFunOfCountable`: any function
`(FinPrefix σ ι n) → Measure (σ × Option ι)` lifts to a kernel
without an explicit measurability proof, sidestepping the
measurability-of-`A.schedule` blocker entirely.

Why (2a) over (2b/2c)?
  - All concrete state types in M3+ (Bracha RBC node states, AVSS
    polynomial commitments over `ZMod p`, lock-step round counters)
    are countable; the discrete σ-algebra is fine for them.
  - (2b/2c) require either changing `Adversary` to carry a
    measurability witness or threading a hypothesis through every
    `traceDist` call site. The first invades a structure used
    elsewhere; the second clutters every downstream theorem.
  - (2a) is local — it only refines the typeclass list on
    `stepKernel` / `traceDist` without changing any structures.

Decidable gates use `Classical.dec` (not a per-action `Decidable`
typeclass), keeping `ProbGatedAction.gate`'s signature `σ → Prop`
unchanged.

Per implementation plan v2.2 §M2 W1 + M2 W2 polish brief
(`docs/randomized-leslie-spike/07-real-tracedist-kernel-task.md`).
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.PMF
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

namespace Leslie.Prob

open MeasureTheory ProbabilityTheory

/-! ## Local `MeasurableSpace` instance for `Option`

Mathlib does not (as of v4.27.0) provide a `MeasurableSpace (Option α)`
instance. Action labels are typically discrete; we equip `Option ι`
with the maximal σ-algebra (every set is measurable). For continuous
action spaces this would need refinement, but that's not in scope for
M1–M5 (action labels are inductive types throughout). -/

instance instMeasurableSpaceOption {α : Type*} : MeasurableSpace (Option α) := ⊤

/-! ## Trace types

Infinite traces are functions `ℕ → σ × Option ι`. Termination is
encoded as eventual stuttering at a terminal state. -/

/-- An infinite trace: at each step `n`, a pair of (state at step n,
optional action label that fired between step n-1 and n). The 0-th
entry's action component is conventionally `none`. -/
abbrev Trace (σ : Type*) (ι : Type*) := Π _ : ℕ, σ × Option ι

/-- A finite trace prefix of length `n + 1`: the input shape to the
per-step Markov kernel in the Ionescu-Tulcea construction. -/
abbrev FinPrefix (σ : Type*) (ι : Type*) (n : ℕ) :=
  Π _ : Finset.Iic n, σ × Option ι

namespace FinPrefix

variable {σ ι : Type*}

/-- Convert a finite trace prefix to a `List`, in increasing index
order, for feeding to `Adversary.schedule`. -/
def toList {n : ℕ} (h : FinPrefix σ ι n) : List (σ × Option ι) :=
  (List.finRange (n + 1)).map fun k =>
    h ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩

/-- The current state in a finite trace prefix is the last entry's
state component. -/
def currentState {n : ℕ} (h : FinPrefix σ ι n) : σ :=
  (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1

end FinPrefix

/-! ## Per-step kernel (`stepKernel`)

`stepKernel spec A n` is the per-step Markov kernel from the
finite trace prefix at time `n` to the next `(σ × Option ι)` pair.

It realises the conceptual branching definition:

```
match A.schedule h.toList with
| none   => Dirac (currentState h, none)
| some i =>
    if (spec.actions i).gate (currentState h)
    then ((spec.actions i).effect ...).toMeasure.map (·, some i)
    else Dirac (currentState h, none)
```

The function-to-kernel lift uses `Kernel.ofFunOfCountable`, which
sidesteps the measurability-of-`A.schedule` blocker by requiring
the *input* type `FinPrefix σ ι n` to be `Countable` and have
`MeasurableSingletonClass`. Both follow from the typeclass
list `[Countable σ] [Countable ι]
[MeasurableSpace σ] [MeasurableSingletonClass σ]
[MeasurableSpace ι] [MeasurableSingletonClass ι]` plus the
discrete `MeasurableSpace (Option ι)` instance declared above
(`MeasurableSingletonClass (Option ι)` follows from
`Countable ι` plus the discrete instance).

The decidable instance for the gate predicate is supplied by
`Classical.dec` via `open Classical in`. -/

/-- The current state of a finite-prefix history is a measurable
function of the history (a coordinate projection composed with
`Prod.fst`). -/
@[fun_prop]
theorem FinPrefix.measurable_currentState {σ ι : Type*}
    [MeasurableSpace σ] [MeasurableSpace ι] {n : ℕ} :
    Measurable (FinPrefix.currentState (σ := σ) (ι := ι) (n := n)) := by
  unfold FinPrefix.currentState
  fun_prop

section StepKernel

open Classical

/-- The per-step Markov kernel of a `ProbActionSpec`/`Adversary`
pair, branching on the adversary's schedule and the spec's gates.

  * If `A.schedule h.toList = none`, the kernel emits a Dirac at
    `(currentState h, none)` — a stutter step.
  * If `A.schedule h.toList = some i` and `(spec.actions i).gate`
    holds at the current state, the kernel emits the effect's
    PMF measure paired with `some i`.
  * If the gate is unmet, it stutters: Dirac at
    `(currentState h, none)`.

`Kernel.ofFunOfCountable` lifts the per-history measure to a
Markov kernel without requiring an explicit measurability proof
for the schedule, given the typeclass requirements documented in
the file header. Decidability of the gate is via `Classical.dec`
(supplied by `open Classical` for this section). -/
noncomputable def stepKernel {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (n : ℕ) :
    Kernel (FinPrefix σ ι n) (σ × Option ι) :=
  Kernel.ofFunOfCountable fun h =>
    match A.schedule h.toList with
    | none => Measure.dirac (h.currentState, (none : Option ι))
    | some i =>
      if hgate : (spec.actions i).gate h.currentState then
        ((spec.actions i).effect h.currentState hgate).toMeasure.map
          (fun s => (s, some i))
      else Measure.dirac (h.currentState, (none : Option ι))

/-- The per-step kernel is a Markov kernel: each branch produces
a probability measure (Dirac in the `none` and gate-fail cases;
pushforward of a PMF measure in the gate-pass case). -/
instance instIsMarkovKernel_stepKernel {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (n : ℕ) :
    IsMarkovKernel (stepKernel spec A n) := by
  refine ⟨fun h => ?_⟩
  -- `Kernel.ofFunOfCountable f h` is definitionally `f h`, so the
  -- goal reduces to showing the per-history measure is a
  -- probability measure for each branch of the match.
  show IsProbabilityMeasure
    (match A.schedule h.toList with
     | none => Measure.dirac (h.currentState, (none : Option ι))
     | some i =>
       if hgate : (spec.actions i).gate h.currentState then
         ((spec.actions i).effect h.currentState hgate).toMeasure.map
           (fun s => (s, some i))
       else Measure.dirac (h.currentState, (none : Option ι)))
  match A.schedule h.toList with
  | none =>
    show IsProbabilityMeasure (Measure.dirac _)
    infer_instance
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · simp only [hgate, dite_true]
      have : IsProbabilityMeasure
          ((spec.actions i).effect h.currentState hgate).toMeasure := by
        infer_instance
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    · simp only [hgate, dite_false]
      infer_instance

end StepKernel

/-! ## Trace measure (`traceDist`)

`traceDist spec A μ₀` is the measure on infinite traces
obtained by lifting `μ₀` to `σ × Option ι` (pairing with `none`)
and feeding the result, together with `stepKernel spec A`, to
`Kernel.trajMeasure`. We deliberately do *not* require
`[IsProbabilityMeasure μ₀]` here: the construction makes sense
for any initial measure, and the `IsProbabilityMeasure` instance
below recovers the probability-measure status when `μ₀` is one.

This signature is invariant under the M2 W2 callers in
`Refinement.lean`: `Refines` quantifies over `μ₀` with an
`IsProbabilityMeasure μ₀` proposition (not an instance), then
uses `traceDist` directly. -/

/-- The trace measure under `spec`, `A`, and initial state
distribution `μ₀`.

**M2 W2 polish realisation.** The per-step kernel is the real
schedule-and-gate-conditional kernel (see `stepKernel` above),
so this measure faithfully reflects both the adversary's choices
and the spec's effect distributions. -/
noncomputable def traceDist {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) :
    Measure (Trace σ ι) :=
  let μ₀_full : Measure (σ × Option ι) :=
    μ₀.map (fun s ↦ (s, (none : Option ι)))
  Kernel.trajMeasure μ₀_full (stepKernel spec A)

/-- The trace measure is a probability measure when `μ₀` is. -/
instance instIsProbabilityMeasure_traceDist {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (traceDist spec A μ₀) := by
  unfold traceDist
  -- The lift `μ₀.map (·, none)` is a probability measure since the
  -- pairing function is measurable; `Kernel.trajMeasure` then
  -- yields a probability measure since each `stepKernel` is Markov.
  have : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

end Leslie.Prob
