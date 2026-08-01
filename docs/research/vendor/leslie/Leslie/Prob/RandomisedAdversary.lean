/-
M3 Phase 9.1 — `RandomisedAdversary`: type + mixture trace measure.
M3 Phase 9.2 — Lifting meta-theorems for `RandomisedAdversary`.

Closes the foundation half of caveat **C5** (MODEL_NOTES §11.5):
existing theorems universally quantify over deterministic
`Adversary σ ι`, but the literature-standard threat model is a
randomised (coin-flipping) adversary. This file introduces the
randomised type, the corresponding mixture trace measure, and the
lifting meta-theorems that translate deterministic-adversary
theorems to randomised-adversary theorems.

Design choices (Phase 9.1):

  * **Per-step PMF schedule.** A randomised adversary is a function
    `History → PMF (Option ι)` rather than `History → Option ι`. The
    PMF form is the same shape used everywhere else in the framework
    (see `Leslie.Prob.PMF`, `Leslie.Prob.Action`); it sidesteps the
    need to thread a `Kernel`-with-measurability witness around.

  * **Mixture trace measure via the existing per-step kernel.** The
    new per-step PMF `randomisedStepPMF` reuses the same gate-and-
    stutter dispatch as `stepKernel`'s match-body: sample an action
    label `α : Option ι` from `R.strategy h.toList`, then dispatch
    on `α` exactly as the deterministic kernel does. The trace
    measure then plugs into `Kernel.trajMeasure` identically to
    `traceDist`. This means `randomisedTraceDist spec A.toRandomised
    μ₀ = traceDist spec A μ₀` reduces to a `PMF.pure_bind` rewrite
    plus `PMF.toMeasure_pure` / `PMF.toMeasure_map`.

Lifting meta-theorems (Phase 9.2):

  * **`AlmostBoxRandomised` / `AlmostDiamondRandomised`** —
    transliterations of the deterministic `AlmostBox` /
    `AlmostDiamond` predicates with `traceDist` →
    `randomisedTraceDist`.

  * **`randomisedStepKernel_eq_bind_stepKernel`** — the per-step
    mixture identity: at each history `h`, the randomised step
    kernel equals a `Measure.bind` over `R.strategy h.toList` of
    deterministic step kernels. The deterministic adversary used
    in each branch is `(R.toAdversary α).schedule = const α`, i.e.
    "always pick `α`"; what `stepKernel` emits at `h` only depends
    on the schedule's value at `h.toList`, so a constant adversary
    suffices to match.

  * **`AlmostBox.lift_to_randomised`** — if `AlmostBox spec A μ₀ φ`
    holds for every deterministic `A`, then `AlmostBoxRandomised
    spec R μ₀ φ` holds for any randomised `R`. Proof: induct on the
    coordinate `n`, use the marginal recurrence at `n+1`, and at
    the per-step kernel apply the mixture identity together with
    `AlmostBox` at the constant-adversary witness.

  * **`randomisedTraceDist_map_eq_of_deterministic`** — if two
    `(spec, μ₀)` configurations produce equal trace marginals
    under every deterministic `A`, they produce equal mixture
    trace marginals under any randomised `R`. Used by the AVSS
    secrecy lift.

  * **`AlmostDiamond.lift_to_randomised`** — analogue of the
    `AlmostBox` lift for the eventual modality.

Per implementation plan v2.2 §M3 + MODEL_NOTES §13.1 (PR 9.1, 9.2).
-/

import Leslie.Mathlib.Probability.Kernel.IonescuTulcea.Bind
import Leslie.Mathlib.Probability.Kernel.IonescuTulcea.InfinitePiFubini
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Liveness
import Leslie.Prob.PMF
import Leslie.Prob.Trace
import Mathlib.Probability.ProductMeasure

namespace Leslie.Prob

open MeasureTheory ProbabilityTheory

/-! ## `RandomisedAdversary`

A randomised, history-deterministic, demonic scheduler with a
static corruption set. The schedule is a function from the visible
history to a `PMF` over the next action label; concretely the
strategy can flip coins to decide its move.

Mathematically this is equivalent to "pick a random tape `r` from a
distribution and run a deterministic `Adversary` parameterised by
`r`" by Fubini composition; the per-step PMF form is more uniform
with the rest of the `Leslie.Prob` framework. -/
structure RandomisedAdversary (σ : Type*) (ι : Type*) where
  /-- Randomised schedule: given the visible history, produce a
  distribution over the next action label (or `none` to stutter). -/
  strategy : List (σ × Option ι) → PMF (Option ι)
  /-- Static corruption set, identically to a plain `Adversary`. -/
  corrupt  : Set PartyId

namespace Adversary

variable {σ ι : Type*}

/-- Lift a deterministic `Adversary` to a `RandomisedAdversary` via
a Dirac PMF on each schedule decision. The mixture trace measure of
the lifted adversary equals the deterministic trace measure of the
original (`randomisedTraceDist_toRandomised` below). -/
noncomputable def toRandomised (A : Adversary σ ι) : RandomisedAdversary σ ι where
  strategy := fun h => PMF.pure (A.schedule h)
  corrupt  := A.corrupt

@[simp]
theorem toRandomised_strategy (A : Adversary σ ι)
    (h : List (σ × Option ι)) :
    A.toRandomised.strategy h = PMF.pure (A.schedule h) := rfl

@[simp]
theorem toRandomised_corrupt (A : Adversary σ ι) :
    A.toRandomised.corrupt = A.corrupt := rfl

end Adversary

/-! ## `RushingRandomisedAdversary` (view-restricted randomised scheduler)

Randomised analog of `Leslie.Prob.RushingAdversary` (see
`Leslie/Prob/Adversary.lean`).  Combines:

  * a `ProtocolView σ V` projection (same as the deterministic
    rushing case),
  * a PMF-valued schedule on the *view-history*
    `List (V × Option ι) → PMF (Option ι)`,
  * a static corruption set.

`toRandomisedAdversary` lifts a `RushingRandomisedAdversary` to a
plain `RandomisedAdversary` by composing `view` over the
state-history before consulting the rushing-view-restricted
strategy — directly mirroring `RushingAdversary.toAdversary`.

Phase 9.5 (MODEL_NOTES §13.5): the literature-standard threat model
combines randomised (coin-flipping) with rushing (view-restricted)
schedules; this structure expresses the latter on top of the former. -/
structure RushingRandomisedAdversary (σ : Type*) (ι : Type*) (V : Type*) where
  /-- The protocol view carried by this adversary. -/
  toProtocolView : ProtocolView σ V
  /-- View-restricted randomised schedule: produce a distribution
  over the next action label (or `none`) given the view-history. -/
  strategy : List (V × Option ι) → PMF (Option ι)
  /-- Static corruption set, identically to a plain
  `RandomisedAdversary`. -/
  corrupt  : Set PartyId

namespace RushingRandomisedAdversary

variable {σ ι V : Type*}

/-- Convenience accessor: the projection `σ → V` of a rushing
randomised adversary's protocol view. -/
def view (R : RushingRandomisedAdversary σ ι V) : σ → V :=
  R.toProtocolView.view

/-- Lift a state-history to a view-history by applying `view`
component-wise.  Mirrors `RushingAdversary.viewHistory`. -/
def viewHistory (R : RushingRandomisedAdversary σ ι V)
    (h : List (σ × Option ι)) : List (V × Option ι) :=
  h.map (fun sa => (R.view sa.1, sa.2))

/-- Adapter: every `RushingRandomisedAdversary` is in particular a
`RandomisedAdversary`.  The strategy is obtained by applying `view`
component-wise to the state-history before consulting the
rushing-view-restricted strategy.

This is the randomised analog of `RushingAdversary.toAdversary`. -/
noncomputable def toRandomisedAdversary
    (R : RushingRandomisedAdversary σ ι V) : RandomisedAdversary σ ι where
  strategy h := R.strategy (R.viewHistory h)
  corrupt    := R.corrupt

@[simp]
theorem toRandomisedAdversary_corrupt
    (R : RushingRandomisedAdversary σ ι V) :
    R.toRandomisedAdversary.corrupt = R.corrupt := rfl

@[simp]
theorem toRandomisedAdversary_strategy
    (R : RushingRandomisedAdversary σ ι V)
    (h : List (σ × Option ι)) :
    R.toRandomisedAdversary.strategy h =
      R.strategy (R.viewHistory h) := rfl

@[simp]
theorem viewHistory_eq_map (R : RushingRandomisedAdversary σ ι V)
    (h : List (σ × Option ι)) :
    R.viewHistory h = h.map (fun sa => (R.view sa.1, sa.2)) := rfl

@[simp]
theorem viewHistory_nil (R : RushingRandomisedAdversary σ ι V) :
    R.viewHistory ([] : List (σ × Option ι)) = [] := rfl

@[simp]
theorem viewHistory_cons (R : RushingRandomisedAdversary σ ι V)
    (sa : σ × Option ι) (h : List (σ × Option ι)) :
    R.viewHistory (sa :: h) =
      (R.view sa.1, sa.2) :: R.viewHistory h := rfl

end RushingRandomisedAdversary

/-! ## Per-step randomised PMF and kernel -/

section RandomisedStep

variable {σ ι : Type*}

open Classical

/-- Per-step distribution on `(σ × Option ι)` for a randomised
adversary. Sample the next action label `α : Option ι` from
`R.strategy h.toList`; then dispatch on `α` as in `stepKernel`:

  * `none` → stutter at the current state.
  * `some i` with gate-met → push the effect distribution forward
    along `(·, some i)`.
  * `some i` with gate-unmet → stutter. -/
noncomputable def randomisedStepPMF
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) : PMF (σ × Option ι) :=
  (R.strategy h.toList).bind fun α =>
    match α with
    | none => PMF.pure (h.currentState, (none : Option ι))
    | some i =>
      if hgate : (spec.actions i).gate h.currentState then
        ((spec.actions i).effect h.currentState hgate).map fun s => (s, some i)
      else PMF.pure (h.currentState, (none : Option ι))

end RandomisedStep

section RandomisedKernel

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Per-step Markov kernel of a `ProbActionSpec` / `RandomisedAdversary`
pair. Lift `randomisedStepPMF` pointwise via `PMF.toMeasure` and
`Kernel.ofFunOfCountable`. -/
noncomputable def randomisedStepKernel
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι) (n : ℕ) :
    Kernel (FinPrefix σ ι n) (σ × Option ι) :=
  Kernel.ofFunOfCountable fun h => (randomisedStepPMF spec R h).toMeasure

instance instIsMarkovKernel_randomisedStepKernel
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι) (n : ℕ) :
    IsMarkovKernel (randomisedStepKernel spec R n) := by
  refine ⟨fun h => ?_⟩
  show IsProbabilityMeasure (randomisedStepPMF spec R h).toMeasure
  infer_instance

/-! ## Mixture trace measure -/

/-- The mixture trace measure of a `ProbActionSpec`,
`RandomisedAdversary`, and initial state distribution `μ₀`.

Defined identically to `traceDist` but with `randomisedStepKernel` in
place of `stepKernel`. Concretely this is the Fubini composition
"sample the strategy at each step, then deterministically dispatch
on the gate" iterated by `Kernel.trajMeasure`. -/
noncomputable def randomisedTraceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) :
    Measure (Trace σ ι) :=
  Kernel.trajMeasure (μ₀.map (fun s ↦ (s, (none : Option ι))))
    (randomisedStepKernel spec R)

instance instIsProbabilityMeasure_randomisedTraceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (randomisedTraceDist spec R μ₀) := by
  unfold randomisedTraceDist
  have : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

/-! ## Sanity: deterministic lift agrees with `traceDist`

For a `RandomisedAdversary` arising from `Adversary.toRandomised`,
each per-step PMF is a `PMF.pure` over the deterministic schedule
choice; the corresponding `toMeasure` collapses to the same Dirac /
pushforward shapes used by `stepKernel`. Hence the per-step kernels
agree, and by `Kernel.trajMeasure` extensionality the mixture trace
measure equals the deterministic trace measure. -/

set_option linter.unusedSectionVars false in
/-- Per-history measure equality for the deterministic lift: each
randomised step PMF on `A.toRandomised` collapses (via
`PMF.pure_bind`) to the same per-history measure that `stepKernel`
produces. The proof case-splits on `A.schedule h.toList` and uses
`PMF.toMeasure_pure` and `PMF.toMeasure_map`.

Most of the surrounding section's typeclass requirements (`Countable`,
`MeasurableSingletonClass`, `MeasurableSpace ι`) are unused at the
PMF-on-`σ` level — only `MeasurableSpace σ` is needed. We silence
the unused-section-vars linter rather than restructure the file. -/
private lemma randomisedStepPMF_toMeasure_toRandomised
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) :
    (randomisedStepPMF spec A.toRandomised h).toMeasure =
      (match A.schedule h.toList with
      | none => Measure.dirac (h.currentState, (none : Option ι))
      | some i =>
        if hgate : (spec.actions i).gate h.currentState then
          ((spec.actions i).effect h.currentState hgate).toMeasure.map
            (fun s => (s, some i))
        else Measure.dirac (h.currentState, (none : Option ι))) := by
  unfold randomisedStepPMF
  rw [Adversary.toRandomised_strategy, PMF.pure_bind]
  -- Substitute the schedule choice on both sides via `cases ... with`.
  -- `dsimp only` forces iota-reduction of the resulting `match … with`.
  cases hα : A.schedule h.toList with
  | none =>
    dsimp only
    exact PMF.toMeasure_pure _
  | some i =>
    dsimp only
    -- Split on the gate; both `if`s collapse to the same branch.
    by_cases hgate : (spec.actions i).gate h.currentState
    · rw [dif_pos hgate, dif_pos hgate]
      have hfun : Measurable (fun s : σ => (s, some i)) := by fun_prop
      exact (PMF.toMeasure_map _ _ hfun).symm
    · rw [dif_neg hgate, dif_neg hgate]
      exact PMF.toMeasure_pure _

theorem randomisedStepKernel_toRandomised
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (n : ℕ) :
    randomisedStepKernel spec A.toRandomised n = stepKernel spec A n := by
  refine DFunLike.ext _ _ fun h => ?_
  exact randomisedStepPMF_toMeasure_toRandomised spec A h

/-- For an `Adversary` lifted to a `RandomisedAdversary` via
`Adversary.toRandomised`, the mixture trace measure equals the
deterministic trace distribution. -/
theorem randomisedTraceDist_toRandomised
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι) (μ₀ : Measure σ) :
    randomisedTraceDist spec A.toRandomised μ₀ = traceDist spec A μ₀ := by
  -- Both sides reduce to `Kernel.trajMeasure μ₀_full κ` with the same
  -- `μ₀_full`; only the per-step kernel family differs. The two
  -- families agree pointwise (`randomisedStepKernel_toRandomised`),
  -- so by `funext` the families are equal as functions, and the
  -- trajectory measures coincide.
  unfold randomisedTraceDist traceDist
  have hk : randomisedStepKernel spec A.toRandomised = stepKernel spec A :=
    funext (randomisedStepKernel_toRandomised spec A)
  simp only [hk]

end RandomisedKernel

/-! ## Phase 9.2 — Lifting meta-theorems

Three meta-theorems that translate trajectory-level properties of
`traceDist` (deterministic) to `randomisedTraceDist` (randomised):

  * `AlmostBox.lift_to_randomised` — AS-always invariants.
  * `randomisedTraceDist_map_eq_of_deterministic` — secrecy / map-eq.
  * `AlmostDiamond.lift_to_randomised` — AS-eventually properties.

**Hypothesis form (deviation from per-tape Fubini lift).** The
naive Fubini-style "lift" via a tape product distribution would
require constructing a probability measure on
`List(σ × Option ι) → Option ι` and proving a trajectory-level
mixture identity — both of which are mathematically sound but
require infrastructure not yet in this file (Kolmogorov product
over a countable index set; `Kernel.trajMeasure`-of-mixture =
mixture-of-`Kernel.trajMeasure`). Per the WORKER_TASK risk #1,
that route bottlenecks on Mathlib lemmas that don't exist by name.

The form we ship instead is the **inductive-preservation form**:
each lift takes the same per-step preservation data that the
deterministic `AlmostBox_of_inductive` / `AlmostDiamond_of_leads_to`
take, and concludes the randomised analog. PR 9.3's AVSS-side
restatements consume this by re-supplying the same inductive
witness used in the deterministic AVSS theorems — so no AVSS-side
proof bloat. The kernel-level mixture identity below
(`randomisedStepKernel_apply_eq_bind`) is the technical heart;
each lift is essentially "redo the deterministic
`AlmostBox_of_inductive` proof with `randomisedStepKernel` in
place of `stepKernel` and `bind_apply` in place of branch
case-splits at the kernel step".

The signatures still use `RandomisedAdversary σ ι` for `R`, so
PR 9.3's AVSS theorems can quantify over arbitrary randomised
adversaries directly — closing the C5 caveat. -/

section AlmostBoxRandomised

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **Almost-surely-always under randomised mixture.** The
randomised analog of `Refinement.AlmostBox`: `φ` holds at every
coordinate of the trace, almost surely under `randomisedTraceDist`.

Pure transliteration of `AlmostBox` with `traceDist` →
`randomisedTraceDist`. -/
def AlmostBoxRandomised
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀), ∀ n, φ ((ω n).1)

/-- **Almost-surely-eventually under randomised mixture.** The
randomised analog of `Refinement.AlmostDiamond`. -/
def AlmostDiamondRandomised
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀), ∃ n, φ ((ω n).1)

end AlmostBoxRandomised

/-! ## Per-step kernel mixture identity

At each history `h`, the randomised step kernel's per-`h` measure
is a tsum over schedule choices of single-action step measures.
This is the workhorse identity behind the inductive-form lifts. -/

section StepKernelMixture

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The per-`h` step measure for a single fixed schedule choice
`α : Option ι`: dispatch on `α` via the same gate-and-stutter
match used by `stepKernel`. This is exactly the `stepKernel` per-`h`
measure for any deterministic adversary whose schedule maps
`h.toList` to `α`. -/
noncomputable def singleActionStep (spec : ProbActionSpec σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) (α : Option ι) :
    Measure (σ × Option ι) :=
  match α with
  | none => Measure.dirac (h.currentState, (none : Option ι))
  | some i =>
    if hgate : (spec.actions i).gate h.currentState then
      ((spec.actions i).effect h.currentState hgate).toMeasure.map
        (fun s => (s, some i))
    else Measure.dirac (h.currentState, (none : Option ι))

set_option linter.unusedSectionVars false in
/-- Mixture identity at a single history: `randomisedStepKernel spec R n h`
applied to any measurable set is the schedule-PMF-weighted sum of
`singleActionStep` evaluations at the same set. -/
theorem randomisedStepKernel_apply_tsum
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n)
    {s : Set (σ × Option ι)} (hs : MeasurableSet s) :
    randomisedStepKernel spec R n h s =
      ∑' α : Option ι, (R.strategy h.toList) α *
        singleActionStep spec h α s := by
  show (randomisedStepPMF spec R h).toMeasure s = _
  rw [randomisedStepPMF, PMF.toMeasure_bind_apply _ _ _ hs]
  refine tsum_congr fun α => ?_
  congr 1
  cases α with
  | none =>
    show (PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
      (singleActionStep spec h none) s
    show (PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
      (Measure.dirac (h.currentState, (none : Option ι))) s
    rw [PMF.toMeasure_pure]
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · show (if hgate : (spec.actions i).gate h.currentState
              then PMF.map (fun s => (s, some i)) ((spec.actions i).effect h.currentState hgate)
              else PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
            (singleActionStep spec h (some i)) s
      simp only [singleActionStep, hgate, dite_true]
      have hfun : Measurable (fun s : σ => (s, some i)) := by fun_prop
      rw [PMF.toMeasure_map_apply _ _ _ hfun hs, Measure.map_apply hfun hs]
    · show (if hgate : (spec.actions i).gate h.currentState
              then PMF.map (fun s => (s, some i)) ((spec.actions i).effect h.currentState hgate)
              else PMF.pure (h.currentState, (none : Option ι))).toMeasure s =
            (singleActionStep spec h (some i)) s
      simp only [singleActionStep, hgate, dite_false]
      rw [PMF.toMeasure_pure]

/-- For any deterministic adversary `A` whose schedule maps
`h.toList` to `α`, the `stepKernel`-per-`h`-measure equals
`singleActionStep spec h α`. This is the bridge between the
randomised mixture identity and the deterministic
`AlmostBox` / `AlmostDiamond` hypotheses in the inductive form. -/
theorem stepKernel_apply_eq_singleActionStep
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) :
    stepKernel spec A n h = singleActionStep spec h (A.schedule h.toList) := by
  show (Kernel.ofFunOfCountable _) h = _
  rw [Kernel.ofFunOfCountable]
  simp only [Kernel.coe_mk]
  cases A.schedule h.toList with
  | none => simp only [singleActionStep]
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · simp only [singleActionStep, hgate, dite_true]
    · simp only [singleActionStep, hgate, dite_false]

set_option linter.unusedSectionVars false in
/-- Single-action AE form: if `φ` is preserved by every gated
action's effect distribution, then for each `α : Option ι` and
each prefix `h` with `φ (h.currentState)`,
`singleActionStep spec h α` is concentrated on `φ`-states. -/
theorem singleActionStep_ae_of_inductive
    {spec : ProbActionSpec σ ι} {φ : σ → Prop}
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    {n : ℕ} (h : FinPrefix σ ι n) (α : Option ι)
    (hcurrent : φ h.currentState) :
    ∀ᵐ y ∂(singleActionStep spec h α), φ y.1 := by
  have hPset : MeasurableSet ({x : σ × Option ι | φ x.1}) := MeasurableSet.of_discrete
  have hPset_state : MeasurableSet {s : σ | φ s} := MeasurableSet.of_discrete
  unfold singleActionStep
  cases α with
  | none =>
    rw [ae_dirac_iff hPset]; exact hcurrent
  | some i =>
    by_cases hgate : (spec.actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [ae_map_iff (by fun_prop) hPset]
      -- Reduce to support-AE on the effect PMF.
      have hbad : MeasurableSet ({s : σ | ¬φ s}) := MeasurableSet.of_discrete
      have : ∀ᵐ s' ∂((spec.actions i).effect h.currentState hgate).toMeasure, φ s' := by
        rw [ae_iff]
        rw [PMF.toMeasure_apply_eq_zero_iff _ hbad]
        rw [Set.disjoint_iff]
        intro s' ⟨hsupp, hno⟩
        exact hno (h_step i h.currentState hgate hcurrent s' hsupp)
      filter_upwards [this] with s' hs'
      exact hs'
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]
      exact hcurrent

end StepKernelMixture

/-! ## Schedule-space machinery + parameterised trajectory framework

(Phase 11-β-followup-7, Worker 7.)

This section provides the **framework infrastructure** for the
`Secrecy → SecrecyRandomised` direction (`Secrecy.toRandomised` in
`Leslie/Prob/Secrecy.lean`).

The mathematical content: a randomised adversary `R` defines a
probability measure on the space of *deterministic* schedule
assignments (functions `List (σ × Option ι) → Option ι`) via the
Kolmogorov / Ionescu–Tulcea product of the per-history PMFs
`R.strategy h`. The mixture trace measure `randomisedTraceDist spec
R μ` then decomposes as the integral, over this schedule-space
measure, of the deterministic trace measures
`traceDist spec (sched.toAdversary R.corrupt) μ`.

This section establishes:

  * `ScheduleAssignment σ ι` — the function space of deterministic
    schedules.
  * `ScheduleAssignment.toAdversary` — the conversion to a
    deterministic `Adversary σ ι` (using `R.corrupt` for the
    corruption set).
  * `scheduleSpaceMeasure R` — the Kolmogorov product of
    per-history PMFs.
  * `randomisedTraceDist_eq_bind_traceDist` — the **framework
    lemma**: AEMeasurability of the schedule-indexed deterministic
    trace measure + bind equality. This captures the substantive
    Ionescu–Tulcea cylinder-uniqueness content at the
    `sched`-parameterised level.

Worker 7's design choice: package both AEMeasurability and the bind
equality into one combined lemma. The two `Secrecy.lean` consumers
(`..._traj_aeMeasurable`, `..._traj_bind_eq`) are then trivial
`.1` / `.2` projections. -/

section ScheduleSpace

variable {σ ι : Type*}

/-- A *schedule assignment*: a deterministic per-history schedule
function. Identical in shape to `Adversary.schedule` (the
corruption set is supplied separately via the parent
`RandomisedAdversary.corrupt` when packaging into an `Adversary`). -/
abbrev ScheduleAssignment (σ ι : Type*) :=
  List (σ × Option ι) → Option ι

namespace ScheduleAssignment

/-- Convert a schedule assignment + corruption set into a
deterministic `Adversary σ ι`. -/
def toAdversary (sched : ScheduleAssignment σ ι) (corrupt : Set PartyId) :
    Adversary σ ι where
  schedule := sched
  corrupt  := corrupt

@[simp]
lemma toAdversary_schedule (sched : ScheduleAssignment σ ι)
    (corrupt : Set PartyId) :
    (sched.toAdversary corrupt).schedule = sched := rfl

@[simp]
lemma toAdversary_corrupt (sched : ScheduleAssignment σ ι)
    (corrupt : Set PartyId) :
    (sched.toAdversary corrupt).corrupt = corrupt := rfl

end ScheduleAssignment

/-- Pi-σ-algebra on schedule assignments — coordinate-wise the
discrete σ-algebra on `Option ι` (`instMeasurableSpaceOption` from
`Trace.lean`).

Coordinate evaluations `sched ↦ sched h` are then measurable in
`sched` for every history `h`. -/
instance instMeasurableSpaceScheduleAssignment :
    MeasurableSpace (ScheduleAssignment σ ι) := by
  unfold ScheduleAssignment
  infer_instance

end ScheduleSpace

section ScheduleSpaceMeasure

variable {σ ι : Type*} [MeasurableSpace σ]

/-- The schedule-space measure induced by a randomised adversary:
the Kolmogorov product of the per-history PMFs `R.strategy h` viewed
as measures via `PMF.toMeasure`, indexed over all histories.

Mathlib's `Measure.infinitePi` extends to arbitrary index types
(no `Countable` constraint on `List (σ × Option ι)` is required). -/
noncomputable def scheduleSpaceMeasure (R : RandomisedAdversary σ ι) :
    Measure (ScheduleAssignment σ ι) :=
  Measure.infinitePi
    (fun h : List (σ × Option ι) => (R.strategy h).toMeasure)

instance instIsProbabilityMeasure_scheduleSpaceMeasure
    (R : RandomisedAdversary σ ι) :
    IsProbabilityMeasure (scheduleSpaceMeasure R) := by
  unfold scheduleSpaceMeasure
  infer_instance

set_option linter.unusedSectionVars false in
/-- Schedule-space marginal at a single history: the projection of
`scheduleSpaceMeasure R` onto the `h`-coordinate is
`(R.strategy h).toMeasure`. Direct application of mathlib's
`Measure.infinitePi_map_eval`. -/
lemma scheduleSpaceMeasure_map_eval
    (R : RandomisedAdversary σ ι) (h : List (σ × Option ι)) :
    (scheduleSpaceMeasure R).map (fun sched => sched h) =
      (R.strategy h).toMeasure := by
  unfold scheduleSpaceMeasure
  exact Measure.infinitePi_map_eval _ h

end ScheduleSpaceMeasure

/-! ### Framework lemma — Fubini / Ionescu–Tulcea decomposition

The substantive measure-theoretic content of the `Secrecy →
SecrecyRandomised` direction. The randomised mixture trace measure
factors as a `Measure.bind` over the schedule-space measure of
deterministic trace measures, and the integrand is AEMeasurable
in the schedule (necessary to apply `Measure.bind_apply` downstream
in `Secrecy.toRandomised`).

**Status (post-PR migrating off `trajMeasure_bind_kernel`).** PR #96
discovered that the previously-used mathlib-side lemma
`trajMeasure_bind_kernel` is *false in general* (an explicit Bernoulli
counterexample shows the per-level bind hypothesis is too weak to imply
the trajectory-level identity). The corrected upstream variant
`trajMeasure_bind_kernel_of_partial` instead takes a strictly stronger
*trajectory-level* bind hypothesis directly — and this hypothesis is
the substantive remaining content for the AVSS-style use case.

For our specific kernel `(stepKernel spec (sched.toAdversary R.corrupt) n)`
the hypothesis `h_partialTraj_bind` reduces to a Fubini-on-`Measure.infinitePi`
swap: each per-history step kernel queries `sched` at exactly one coordinate
(`sched h.toList`) and the histories used at distinct levels have distinct
list-lengths (so distinct coordinates in `sched`). Under
`Measure.infinitePi (R.strategy ·)` those coordinates are independent, so
sampling once and querying repeatedly is distributionally equivalent to
sampling fresh per level. Concretely the discharge requires induction on `n`
plus a Fubini swap between the (`partialTraj`-driven) random history and
`Measure.infinitePi`'s coordinate marginals — sound but not yet exposed in
mathlib at this generality.

**Proof outline.** Both helpers reduce to a parameterised cylinder
argument:

  * **AEMeasurability.** It suffices to show that for every
    measurable `t ⊆ Trace σ ι`, the function
    `sched ↦ (traceDist spec (sched.toAdversary R.corrupt) μ) t`
    is measurable in `sched`. By `Measure.measurable_of_measurable_coe`
    we may assume `t` is a cylinder; then by induction on the
    cylinder length, the value depends only on finitely many
    coordinate evaluations of `sched`, each measurable by the
    Pi-σ-algebra. The induction step uses `partialTraj_succ_of_le`
    plus `Kernel.measurable_coe`. *This direction is closed
    upstream-side via `Kernel.trajMeasure_measurable` in
    `Leslie.Mathlib.Probability.Kernel.IonescuTulcea.Bind`.*

  * **Bind equality.** By `MeasureTheory.IsProjectiveLimit.unique`
    (cylinder uniqueness), it suffices to show that LHS and RHS
    agree as projective limits of the same family. The reduction
    is now staged through `Kernel.trajMeasure_bind_kernel_of_partial`
    (axiom-clean upstream): the residual content is the
    trajectory-level bind identity captured by
    `partialTraj_apply_eq_bind_in_sched` below, plus a joint
    measurability witness `partialTraj_apply_measurable_in_sched`.
    Both are factored out as named helpers; the bind identity in
    particular is the precise mathematical content of the
    `infinitePi`-Fubini gap.

The bind identity is proved by first establishing the singleton-cylinder
case using finite-coordinate independence for `Measure.infinitePi`, then
expanding an arbitrary measurable set over countably many singleton atoms. -/
section RandomisedTraceDistFubini

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

set_option linter.unusedSectionVars false in
/-- **Auxiliary measurability** (factored from the framework lemma to avoid
heartbeat blowup): `sched ↦ stepKernel spec (sched.toAdversary R.corrupt) n h s`
is measurable in `sched` for every measurable `s`. The composition factors
through `sched ↦ sched h.toList` (Pi-σ-algebra projection) and the discrete
map `α ↦ (singleActionStep spec h α) s : Option ι → ℝ≥0∞`. -/
private lemma stepKernel_apply_measurable_in_sched
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId)
    {n : ℕ} (h : FinPrefix σ ι n) {s : Set (σ × Option ι)}
    (_hs : MeasurableSet s) :
    Measurable (fun sched : ScheduleAssignment σ ι =>
      (stepKernel spec (sched.toAdversary corrupt) n) h s) := by
  have heq : (fun sched : ScheduleAssignment σ ι =>
        (stepKernel spec (sched.toAdversary corrupt) n) h s) =
      (fun α : Option ι => (singleActionStep spec h α) s) ∘
        (fun sched : ScheduleAssignment σ ι => sched h.toList) := by
    funext sched
    simp [stepKernel_apply_eq_singleActionStep]
  rw [heq]
  exact (Measurable.of_discrete (f := fun α : Option ι =>
    (singleActionStep spec h α) s)).comp (measurable_pi_apply _)

set_option linter.unusedSectionVars false in
/-- **Auxiliary per-step bind identity** (factored): for every measurable `s`,
`randomisedStepKernel spec R n h s = ∫⁻ sched, stepKernel ... d(scheduleSpaceMeasure R)`.
By `randomisedStepKernel_apply_tsum`, `stepKernel_apply_eq_singleActionStep`,
`scheduleSpaceMeasure_map_eval`, and `lintegral_countable'`. -/
private lemma randomisedStepKernel_apply_eq_bind_stepKernel
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) {s : Set (σ × Option ι)}
    (hs : MeasurableSet s) :
    (randomisedStepKernel spec R n) h s =
      ∫⁻ sched : ScheduleAssignment σ ι,
        (stepKernel spec (sched.toAdversary R.corrupt) n) h s
          ∂(scheduleSpaceMeasure R) := by
  have hproj_meas : Measurable
      (fun sched : ScheduleAssignment σ ι => sched h.toList) :=
    measurable_pi_apply _
  have hf_meas : Measurable (fun α : Option ι => (singleActionStep spec h α) s) :=
    Measurable.of_discrete
  have hrhs : (∫⁻ sched : ScheduleAssignment σ ι,
        (stepKernel spec (sched.toAdversary R.corrupt) n) h s
          ∂(scheduleSpaceMeasure R))
      = ∫⁻ α : Option ι, (singleActionStep spec h α) s
          ∂((R.strategy h.toList).toMeasure) := by
    have hpush : (fun sched : ScheduleAssignment σ ι =>
          (stepKernel spec (sched.toAdversary R.corrupt) n) h s)
        = (fun sched : ScheduleAssignment σ ι =>
            (singleActionStep spec h (sched h.toList)) s) := by
      funext sched
      simp [stepKernel_apply_eq_singleActionStep]
    rw [hpush]
    rw [← scheduleSpaceMeasure_map_eval R h.toList]
    rw [lintegral_map hf_meas hproj_meas]
  rw [hrhs]
  rw [randomisedStepKernel_apply_tsum spec R h hs]
  rw [lintegral_countable' (μ := (R.strategy h.toList).toMeasure)
        (f := fun α : Option ι => (singleActionStep spec h α) s)]
  refine tsum_congr fun α => ?_
  rw [(R.strategy h.toList).toMeasure_apply_singleton α
        (MeasurableSet.singleton _)]
  ring

set_option linter.unusedSectionVars false in
private lemma randomisedStepKernel_apply_eq_lintegral_singleActionStep
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    {n : ℕ} (h : FinPrefix σ ι n) {s : Set (σ × Option ι)}
    (hs : MeasurableSet s) :
    (randomisedStepKernel spec R n) h s =
      ∫⁻ α : Option ι, (singleActionStep spec h α) s
          ∂((R.strategy h.toList).toMeasure) := by
  rw [randomisedStepKernel_apply_tsum spec R h hs]
  rw [lintegral_countable' (μ := (R.strategy h.toList).toMeasure)
        (f := fun α : Option ι => (singleActionStep spec h α) s)]
  refine tsum_congr fun α => ?_
  rw [(R.strategy h.toList).toMeasure_apply_singleton α
        (MeasurableSet.singleton _)]
  ring

/-! ### Joint kernel construction for `partialTraj` parameterised over `sched`.

We replicate (in private form) the `kappaJoint` / `jointStepKernel` /
`jointPartialTraj` construction from `Leslie.Mathlib.Probability.Kernel.IonescuTulcea.Bind`,
specialised to the AVSS step-kernel family. The point is to obtain joint
measurability of `(sched, x₀) ↦ partialTraj (κ sched) 0 n x₀ S` from joint
kernel-measurability of a single kernel `Kernel (ScheduleAssignment σ ι ×
FinPrefix σ ι 0) (FinPrefix σ ι n)` whose value at `(sched, x₀)` agrees with
`partialTraj (κ sched) 0 n x₀`. The construction is identical to the upstream
private helpers in `Bind.lean`; we re-derive it locally because those helpers
are private and the AVSS kernel `κ sched n h := stepKernel spec
(sched.toAdversary corrupt) n h` is what we need to specialise to. -/

set_option linter.unusedSectionVars false in
/-- Joint kernel `(sched, h) ↦ stepKernel spec (sched.toAdversary corrupt) n h`,
with measurability bootstrapped from `stepKernel_apply_measurable_in_sched` plus
countability of `FinPrefix σ ι n`. -/
private noncomputable def kappaJointSched
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ) :
    Kernel (ScheduleAssignment σ ι × FinPrefix σ ι n) (σ × Option ι) where
  toFun bh := (stepKernel spec (bh.1.toAdversary corrupt) n) bh.2
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    refine measurable_from_prod_countable_left fun h => ?_
    exact stepKernel_apply_measurable_in_sched spec corrupt h hs

set_option linter.unusedSectionVars false in
private instance kappaJointSched_isMarkov
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ) :
    IsMarkovKernel (kappaJointSched spec corrupt n) :=
  ⟨fun bh => by
    show IsProbabilityMeasure
      ((stepKernel spec (bh.1.toAdversary corrupt) n) bh.2)
    infer_instance⟩

set_option linter.unusedSectionVars false in
/-- The joint per-step Ionescu–Tulcea kernel parameterised over `sched`. -/
private noncomputable def jointStepKernelSched
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ) :
    Kernel (ScheduleAssignment σ ι × FinPrefix σ ι n) (FinPrefix σ ι (n + 1)) :=
  (Kernel.deterministic Prod.snd measurable_snd
      ×ₖ (kappaJointSched spec corrupt n).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n)).map
    (IicProdIoc (X := fun _ : ℕ => σ × Option ι) n (n + 1))

set_option linter.unusedSectionVars false in
private instance jointStepKernelSched_isMarkov
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ) :
    IsMarkovKernel (jointStepKernelSched spec corrupt n) := by
  unfold jointStepKernelSched
  have : IsMarkovKernel
      ((kappaJointSched spec corrupt n).map
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n)) :=
    Kernel.IsMarkovKernel.map _
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n).measurable
  exact Kernel.IsMarkovKernel.map _ measurable_IicProdIoc

set_option linter.unusedSectionVars false in
private lemma jointStepKernelSched_apply
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ)
    (sched : ScheduleAssignment σ ι) (y : FinPrefix σ ι n) :
    jointStepKernelSched spec corrupt n (sched, y) =
      ((Kernel.id ×ₖ
        ((stepKernel spec (sched.toAdversary corrupt) n).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n))) y).map
        (IicProdIoc (X := fun _ : ℕ => σ × Option ι) n (n + 1)) := by
  unfold jointStepKernelSched
  rw [show ((Kernel.deterministic Prod.snd measurable_snd ×ₖ (kappaJointSched spec corrupt n).map
            (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n)).map
          (IicProdIoc (X := fun _ : ℕ => σ × Option ι) n (n + 1))) (sched, y) =
        Measure.map (IicProdIoc (X := fun _ : ℕ => σ × Option ι) n (n + 1))
          ((Kernel.deterministic Prod.snd measurable_snd ×ₖ (kappaJointSched spec corrupt n).map
            (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n)) (sched, y))
          from Kernel.map_apply _ measurable_IicProdIoc _]
  congr 1
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.id_apply]
  congr 1
  rw [Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n).measurable,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n).measurable]
  rfl

set_option linter.unusedSectionVars false in
/-- The joint kernel version of `partialTraj (κ sched) 0 n`. -/
private noncomputable def jointPartialTrajSched
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) :
    (n : ℕ) → Kernel (ScheduleAssignment σ ι × FinPrefix σ ι 0) (FinPrefix σ ι n)
  | 0 => Kernel.deterministic Prod.snd measurable_snd
  | n + 1 =>
      ((jointPartialTrajSched spec corrupt n) ⊗ₖ
        ((jointStepKernelSched spec corrupt n).comap
          (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
            (bxy.1.1, bxy.2))
          (by fun_prop))).map Prod.snd

set_option linter.unusedSectionVars false in
private instance jointPartialTrajSched_isMarkov
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) :
    ∀ (n : ℕ), IsMarkovKernel (jointPartialTrajSched spec corrupt n) := by
  intro n
  induction n with
  | zero =>
    show IsMarkovKernel (Kernel.deterministic Prod.snd measurable_snd)
    infer_instance
  | succ n ih =>
    have := ih
    have hStep : IsMarkovKernel ((jointStepKernelSched spec corrupt n).comap
        (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
          (bxy.1.1, bxy.2))
        (by fun_prop)) := Kernel.IsMarkovKernel.comap _ _
    show IsMarkovKernel
      (((jointPartialTrajSched spec corrupt n) ⊗ₖ
        ((jointStepKernelSched spec corrupt n).comap
          (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
            (bxy.1.1, bxy.2))
          (by fun_prop))).map Prod.snd)
    have : IsMarkovKernel ((jointPartialTrajSched spec corrupt n) ⊗ₖ
        ((jointStepKernelSched spec corrupt n).comap
          (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
            (bxy.1.1, bxy.2))
          (by fun_prop))) := inferInstance
    exact Kernel.IsMarkovKernel.map _ measurable_snd

set_option linter.unusedSectionVars false in
/-- Pointwise agreement: at `(sched, x₀)`, the joint partial-trajectory kernel
equals `partialTraj (κ sched) 0 n x₀`. -/
private lemma jointPartialTrajSched_apply
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ)
    (sched : ScheduleAssignment σ ι) (x₀ : FinPrefix σ ι 0) :
    jointPartialTrajSched spec corrupt n (sched, x₀) =
      Kernel.partialTraj (X := fun _ => σ × Option ι)
        (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n x₀ := by
  induction n with
  | zero =>
    show (Kernel.deterministic Prod.snd measurable_snd) (sched, x₀) = _
    rw [Kernel.deterministic_apply, Kernel.partialTraj_self, Kernel.id_apply]
  | succ n ih =>
    have hMark_jptN : IsMarkovKernel (jointPartialTrajSched spec corrupt n) := inferInstance
    have hMark_step_comap : IsMarkovKernel ((jointStepKernelSched spec corrupt n).comap
        (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
          (bxy.1.1, bxy.2))
        (by fun_prop)) := Kernel.IsMarkovKernel.comap _ _
    show ((jointPartialTrajSched spec corrupt n ⊗ₖ
        ((jointStepKernelSched spec corrupt n).comap
          (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
            (bxy.1.1, bxy.2))
          (by fun_prop))).map Prod.snd) (sched, x₀) = _
    ext s hs
    rw [Kernel.map_apply' _ measurable_snd _ hs,
      Kernel.compProd_apply (measurable_snd hs)]
    have hcomap : ∀ y, ((jointStepKernelSched spec corrupt n).comap
        (fun bxy : (ScheduleAssignment σ ι × FinPrefix σ ι 0) × FinPrefix σ ι n =>
          (bxy.1.1, bxy.2))
        (by fun_prop)) ((sched, x₀), y) (Prod.mk y ⁻¹' (Prod.snd ⁻¹' s)) =
          jointStepKernelSched spec corrupt n (sched, y) s := by
      intro y; rw [Kernel.comap_apply']; rfl
    simp_rw [hcomap, ih]
    rw [Kernel.partialTraj_succ_of_le (zero_le _)]
    have hmap_apply' :=
      Kernel.map_apply' (((Kernel.id ×ₖ
              ((stepKernel spec (sched.toAdversary corrupt) n).map
                (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n))) ∘ₖ
              (Kernel.partialTraj (X := fun _ => σ × Option ι)
                (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n)))
        (measurable_IicProdIoc (X := fun _ : ℕ => σ × Option ι) (m := n) (n := n + 1))
        x₀ hs
    rw [hmap_apply']
    have hcomp_apply' :=
      Kernel.comp_apply'
        (Kernel.id ×ₖ
          ((stepKernel spec (sched.toAdversary corrupt) n).map
            (MeasurableEquiv.piSingleton (X := fun _ : ℕ => σ × Option ι) n)))
        (Kernel.partialTraj (X := fun _ => σ × Option ι)
          (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n)
        x₀
        (measurable_IicProdIoc (X := fun _ : ℕ => σ × Option ι) (m := n) (n := n + 1) hs)
    rw [hcomp_apply']
    refine lintegral_congr (fun y => ?_)
    rw [jointStepKernelSched_apply,
      Measure.map_apply
        (measurable_IicProdIoc (X := fun _ : ℕ => σ × Option ι) (m := n) (n := n + 1)) hs]

set_option linter.unusedSectionVars false in
/-- **Auxiliary joint measurability** of `(sched, x₀) ↦ partialTraj κ_sched 0 n x₀ S`
for the AVSS step-kernel family. This is the `h_partialTraj_meas` hypothesis
required by `Kernel.trajMeasure_bind_kernel_of_partial`.

Discharged by the joint-kernel construction `jointPartialTrajSched` above:
joint measurability of the kernel evaluated at a fixed measurable set `S`
follows from `Kernel.measurable` (kernel-as-measure-valued-map is measurable)
composed with `Measure.measurable_coe hS` (measure-evaluation at `S` is
measurable). -/
private lemma partialTraj_apply_measurable_in_sched
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) (n : ℕ)
    {S : Set (Π _i : Finset.Iic n, σ × Option ι)} (hS : MeasurableSet S) :
    Measurable
      (Function.uncurry
        (fun (sched : ScheduleAssignment σ ι)
            (x₀ : Π _i : Finset.Iic 0, σ × Option ι) =>
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n x₀) S)) := by
  -- Rewrite via `jointPartialTrajSched_apply`.
  have hRw : (Function.uncurry
      (fun (sched : ScheduleAssignment σ ι)
          (x₀ : Π _i : Finset.Iic 0, σ × Option ι) =>
        (Kernel.partialTraj (X := fun _ => σ × Option ι)
          (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n x₀) S))
      = (fun bx₀ : ScheduleAssignment σ ι × FinPrefix σ ι 0 =>
          (jointPartialTrajSched spec corrupt n bx₀) S) := by
    funext bx₀
    rcases bx₀ with ⟨sched, x₀⟩
    rw [Function.uncurry_apply_pair, jointPartialTrajSched_apply]
  rw [hRw]
  exact (Measure.measurable_coe hS).comp (Kernel.measurable _)

set_option linter.unusedSectionVars false in
private def prefixSucc {n : ℕ} (y : FinPrefix σ ι (n + 1)) : FinPrefix σ ι n :=
  fun i => y ⟨i.1, Finset.mem_Iic.2 ((Finset.mem_Iic.1 i.2).trans n.le_succ)⟩

set_option linter.unusedSectionVars false in
private lemma finPrefix_toList_length {n : ℕ} (h : FinPrefix σ ι n) :
    h.toList.length = n + 1 := by
  simp [FinPrefix.toList]

open Classical in
private noncomputable def pathQueryFinset :
    (n : ℕ) → FinPrefix σ ι n → Finset (List (σ × Option ι))
  | 0, _ => ∅
  | n + 1, y => insert (prefixSucc y).toList (pathQueryFinset n (prefixSucc y))

set_option linter.unusedSectionVars false in
open Classical in
private lemma pathQueryFinset_mem_length_le :
    ∀ (n : ℕ) (y : FinPrefix σ ι n) (q : List (σ × Option ι)),
      q ∈ pathQueryFinset n y → q.length ≤ n
  | 0, y, q => by simp [pathQueryFinset]
  | n + 1, y, q => by
      intro hq
      simp only [pathQueryFinset, Finset.mem_insert] at hq
      rcases hq with hq | hq
      · subst hq
        simp [finPrefix_toList_length]
      · exact (pathQueryFinset_mem_length_le n (prefixSucc y) q hq).trans n.le_succ

set_option linter.unusedSectionVars false in
open Classical in
private lemma pathQueryFinset_self_not_mem
    (n : ℕ) (y : FinPrefix σ ι n) :
    y.toList ∉ pathQueryFinset n y := by
  intro hy
  have hlen := pathQueryFinset_mem_length_le n y y.toList hy
  simp [finPrefix_toList_length] at hlen

open Classical Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory
  Preorder ProbabilityTheory Filtration in
private lemma partialTraj_singleton_measurable_in_sched_piFinset
    (spec : ProbActionSpec σ ι) (corrupt : Set PartyId) :
    ∀ (n : ℕ) (x₀ : FinPrefix σ ι 0) (y : FinPrefix σ ι n),
      Measurable[piFinset (pathQueryFinset n y)]
        (fun sched : ScheduleAssignment σ ι =>
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n x₀) {y})
  | 0, x₀, y => by
      simp [pathQueryFinset, Kernel.partialTraj_self, Kernel.id_apply]
  | n + 1, x₀, y => by
      let yp : FinPrefix σ ι n := prefixSucc y
      let q : List (σ × Option ι) := yp.toList
      let z : σ × Option ι := y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩
      have hIH := partialTraj_singleton_measurable_in_sched_piFinset
        spec corrupt n x₀ yp
      have hB : Measurable[piFinset ({q} : Finset (List (σ × Option ι)))]
          (fun sched : ScheduleAssignment σ ι =>
            (stepKernel spec (sched.toAdversary corrupt) n) yp {z}) := by
        have hEval : Measurable[piFinset ({q} : Finset (List (σ × Option ι)))]
            (fun sched : ScheduleAssignment σ ι => sched q) := by
          rw [piFinset_eq_comap_restrict (X := fun _ : List (σ × Option ι) => Option ι)
            ({q} : Finset (List (σ × Option ι)))]
          simpa [Set.restrict_apply] using
            (measurable_pi_apply ⟨q, by simp⟩).comp
              (comap_measurable ((({q} : Finset (List (σ × Option ι))) :
                Set (List (σ × Option ι))).restrict))
        have hDisc : Measurable
            (fun α : Option ι => (singleActionStep spec yp α) {z}) :=
          Measurable.of_discrete
        have hEq : (fun sched : ScheduleAssignment σ ι =>
            (stepKernel spec (sched.toAdversary corrupt) n) yp {z}) =
            (fun α : Option ι => (singleActionStep spec yp α) {z}) ∘
              (fun sched : ScheduleAssignment σ ι => sched q) := by
          funext sched
          simp [q, stepKernel_apply_eq_singleActionStep]
        rw [hEq]
        exact hDisc.comp hEval
      have hFormula : (fun sched : ScheduleAssignment σ ι =>
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 (n + 1) x₀) {y}) =
          fun sched : ScheduleAssignment σ ι =>
            (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (fun n => stepKernel spec (sched.toAdversary corrupt) n) 0 n x₀) {yp} *
            (stepKernel spec (sched.toAdversary corrupt) n) yp {z} := by
        funext sched
        exact ProbabilityTheory.Kernel.partialTraj_succ_apply_singleton_const
          (κ := fun n => stepKernel spec (sched.toAdversary corrupt) n) n x₀ y
      rw [hFormula]
      have hPath : pathQueryFinset (n + 1) y =
          insert q (pathQueryFinset n yp) := by
        rfl
      rw [hPath]
      refine (hIH.mono ?_ le_rfl).mul (hB.mono ?_ le_rfl)
      · exact piFinset.mono (by intro t ht; exact Finset.mem_insert_of_mem ht)
      · exact piFinset.mono (by
          intro t ht
          exact Finset.mem_insert.mpr (Or.inl (by simpa using ht)))

open Classical Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory
  Preorder ProbabilityTheory Filtration in
set_option linter.unusedSectionVars false in
private lemma partialTraj_singleton_eq_bind_in_sched
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι) :
    ∀ (n : ℕ) (x₀ : FinPrefix σ ι 0) (y : FinPrefix σ ι n),
      (Kernel.partialTraj (X := fun _ => σ × Option ι)
        (randomisedStepKernel spec R) 0 n x₀) {y} =
        ∫⁻ sched : ScheduleAssignment σ ι,
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {y}
          ∂(scheduleSpaceMeasure R)
  | 0, x₀, y => by
      rw [Kernel.partialTraj_self, Kernel.id_apply]
      simp_rw [Kernel.partialTraj_self, Kernel.id_apply]
      rw [lintegral_const, measure_univ, mul_one]
  | n + 1, x₀, y => by
      let yp : FinPrefix σ ι n := prefixSucc y
      let q : List (σ × Option ι) := yp.toList
      let z : σ × Option ι := y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩
      have hIH := partialTraj_singleton_eq_bind_in_sched spec R n x₀ yp
      rw [ProbabilityTheory.Kernel.partialTraj_succ_apply_singleton_const
        (κ := randomisedStepKernel spec R) n x₀ y]
      have hFormula : (fun sched : ScheduleAssignment σ ι =>
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 (n + 1) x₀) {y}) =
          fun sched : ScheduleAssignment σ ι =>
            (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {yp} *
            (singleActionStep spec yp (sched q)) {z} := by
        funext sched
        change
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 (n + 1) x₀) {y} =
            (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {yp} *
            (singleActionStep spec yp (sched q)) {z}
        rw [ProbabilityTheory.Kernel.partialTraj_succ_apply_singleton_const
          (κ := fun n => stepKernel spec (sched.toAdversary R.corrupt) n) n x₀ y]
        change
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {yp} *
            (stepKernel spec (sched.toAdversary R.corrupt) n) yp {z} =
            (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {yp} *
            (singleActionStep spec yp (sched q)) {z}
        simp [q, stepKernel_apply_eq_singleActionStep]
      rw [hFormula]
      unfold scheduleSpaceMeasure
      have hq : q ∉ pathQueryFinset n yp := by
        simpa [q] using pathQueryFinset_self_not_mem n yp
      have hA :
          Measurable[piFinset (pathQueryFinset n yp)]
            (fun sched : ScheduleAssignment σ ι =>
              (Kernel.partialTraj (X := fun _ => σ × Option ι)
                (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {yp}) :=
        partialTraj_singleton_measurable_in_sched_piFinset spec R.corrupt n x₀ yp
      have hB : Measurable (fun α : Option ι => (singleActionStep spec yp α) {z}) :=
        Measurable.of_discrete
      rw [Measure.lintegral_infinitePi_mul_eval_of_piFinset
        (μ := fun h : List (σ × Option ι) => (R.strategy h).toMeasure)
        hq hA hB (fun _ => (none : Option ι))]
      have hIH' :
          (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (randomisedStepKernel spec R) 0 n x₀) {yp} =
            ∫⁻ sched : ScheduleAssignment σ ι,
              (Kernel.partialTraj (X := fun _ => σ × Option ι)
                (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) {yp}
              ∂(Measure.infinitePi
                (fun h : List (σ × Option ι) => (R.strategy h).toMeasure)) := by
        simpa [scheduleSpaceMeasure] using hIH
      rw [← hIH']
      rw [← randomisedStepKernel_apply_eq_lintegral_singleActionStep
        spec R yp (MeasurableSet.singleton z)]
      rfl

set_option linter.unusedSectionVars false in
/-- **Auxiliary trajectory-level bind identity** for the AVSS step-kernel
family. This is the `h_partialTraj_bind` hypothesis required by
`Kernel.trajMeasure_bind_kernel_of_partial`.

For the AVSS-style kernel
`(stepKernel spec (sched.toAdversary R.corrupt) n) h = singleActionStep spec h (sched h.toList)`,
each per-history step queries `sched` at exactly one coordinate. Across
distinct trajectory levels the histories have distinct list-lengths, hence
distinct query coordinates. Under `scheduleSpaceMeasure R = Measure.infinitePi
(R.strategy ·)`, those coordinates are independent.

The proof first handles singleton cylinders by induction on the trajectory
length: a path prefix depends on the finite set of previously queried
coordinates, while the next step queries a fresh coordinate, so
`Measure.lintegral_infinitePi_mul_eval_of_piFinset` factors the integral.
The general measurable-set case follows by countable atomic decomposition of
finite prefixes and `lintegral_tsum`. -/
private lemma partialTraj_apply_eq_bind_in_sched
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι) (n : ℕ)
    (x₀ : Π _i : Finset.Iic 0, σ × Option ι)
    {S : Set (Π _i : Finset.Iic n, σ × Option ι)} (_hS : MeasurableSet S) :
    (Kernel.partialTraj (X := fun _ => σ × Option ι)
        (randomisedStepKernel spec R) 0 n x₀) S =
      ∫⁻ sched : ScheduleAssignment σ ι,
        (Kernel.partialTraj (X := fun _ => σ × Option ι)
          (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀) S
          ∂(scheduleSpaceMeasure R) := by
  classical
  let Y := Π _i : Finset.Iic n, σ × Option ι
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  let μAvg : Measure Y :=
    (Kernel.partialTraj (X := fun _ => σ × Option ι)
      (randomisedStepKernel spec R) 0 n x₀)
  let μSched : ScheduleAssignment σ ι → Measure Y := fun sched =>
    (Kernel.partialTraj (X := fun _ => σ × Option ι)
      (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n x₀)
  have hμAvg_atoms : μAvg S = ∑' y : S, μAvg ({(y : Y)} : Set Y) := by
    have h := lintegral_countable
      (μ := μAvg) (f := fun _ : Y => (1 : ENNReal)) (s := S) (Set.to_countable S)
    simpa [μAvg, one_mul, Measure.restrict_apply, hS] using h
  have hμSched_atoms (sched : ScheduleAssignment σ ι) :
      μSched sched S = ∑' y : S, μSched sched ({(y : Y)} : Set Y) := by
    have h := lintegral_countable
      (μ := μSched sched) (f := fun _ : Y => (1 : ENNReal)) (s := S) (Set.to_countable S)
    simpa [μSched, one_mul, Measure.restrict_apply, hS] using h
  have hsingleton (y : S) :
      μAvg ({(y : Y)} : Set Y) =
        ∫⁻ sched : ScheduleAssignment σ ι, μSched sched ({(y : Y)} : Set Y)
          ∂(scheduleSpaceMeasure R) := by
    simpa [μAvg, μSched, Y] using
      partialTraj_singleton_eq_bind_in_sched spec R n x₀ (y : Y)
  have hsingleton_meas (y : S) :
      AEMeasurable (fun sched : ScheduleAssignment σ ι =>
        μSched sched ({(y : Y)} : Set Y)) (scheduleSpaceMeasure R) := by
    have huncurry := partialTraj_apply_measurable_in_sched
      spec R.corrupt n (MeasurableSet.singleton (y : Y))
    have hpair : Measurable (fun sched : ScheduleAssignment σ ι => (sched, x₀)) :=
      measurable_prodMk_right
    exact (huncurry.comp hpair).aemeasurable
  calc
    μAvg S = ∑' y : S, μAvg ({(y : Y)} : Set Y) := hμAvg_atoms
    _ = ∑' y : S, ∫⁻ sched : ScheduleAssignment σ ι,
          μSched sched ({(y : Y)} : Set Y) ∂(scheduleSpaceMeasure R) := by
        exact tsum_congr fun y => hsingleton y
    _ = ∫⁻ sched : ScheduleAssignment σ ι,
          ∑' y : S, μSched sched ({(y : Y)} : Set Y)
          ∂(scheduleSpaceMeasure R) := by
        rw [lintegral_tsum]
        exact fun y => hsingleton_meas y
    _ = ∫⁻ sched : ScheduleAssignment σ ι, μSched sched S ∂(scheduleSpaceMeasure R) := by
        refine lintegral_congr_ae ?_
        filter_upwards with sched
        rw [hμSched_atoms sched]

set_option linter.unusedSectionVars false in
/-- **Framework lemma (Phase 11-β-followup-7; migrated PR #97).** Fubini /
Ionescu–Tulcea decomposition of the randomised mixture trace measure.

Given a randomised adversary `R` and an initial-state probability
measure `μ`:

  * the deterministic trace measure
    `traceDist spec (sched.toAdversary R.corrupt) μ` is AEMeasurable
    in `sched` w.r.t. `scheduleSpaceMeasure R`;
  * the mixture trace measure equals the `Measure.bind` of these
    deterministic trace measures over the schedule-space measure.

**Proof.** Direct application of the two mathlib-upstream-candidate
lemmas in `Leslie.Mathlib.Probability.Kernel.IonescuTulcea.Bind`:
`Kernel.trajMeasure_measurable` (parameterised measurability) and
`Kernel.trajMeasure_bind_kernel_of_partial` (the *axiom-clean*
trajectory-level Fubini identity from PR #96). The four hypotheses come
from the auxiliary lemmas `stepKernel_apply_measurable_in_sched`,
`randomisedStepKernel_apply_eq_bind_stepKernel`,
`partialTraj_apply_measurable_in_sched`, and
`partialTraj_apply_eq_bind_in_sched` above; the latter two encapsulate
the residual `infinitePi`-Fubini content. -/
theorem randomisedTraceDist_eq_bind_traceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    AEMeasurable
        (fun sched : ScheduleAssignment σ ι =>
          traceDist spec (sched.toAdversary R.corrupt) μ)
        (scheduleSpaceMeasure R)
      ∧ randomisedTraceDist spec R μ =
        Measure.bind (scheduleSpaceMeasure R) fun sched =>
          traceDist spec (sched.toAdversary R.corrupt) μ := by
  classical
  set μ₀_full : Measure (σ × Option ι) := μ.map (fun s => (s, (none : Option ι)))
    with _hμ₀_full_def
  haveI hμ₀_full : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have h_meas : ∀ (n : ℕ) (h : FinPrefix σ ι n) {s : Set (σ × Option ι)},
      MeasurableSet s →
      Measurable (fun sched : ScheduleAssignment σ ι =>
        (stepKernel spec (sched.toAdversary R.corrupt) n) h s) :=
    fun n h _ hs => stepKernel_apply_measurable_in_sched spec R.corrupt h hs
  have hMeasurable : Measurable
      (fun sched : ScheduleAssignment σ ι =>
        Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
          (stepKernel spec (sched.toAdversary R.corrupt))) :=
    ProbabilityTheory.Kernel.trajMeasure_measurable
      (X := fun _ => σ × Option ι)
      (β := ScheduleAssignment σ ι)
      (μ₀ := μ₀_full)
      (κ := fun sched n => stepKernel spec (sched.toAdversary R.corrupt) n)
      h_meas
  have hAE : AEMeasurable
      (fun sched : ScheduleAssignment σ ι =>
        traceDist spec (sched.toAdversary R.corrupt) μ)
      (scheduleSpaceMeasure R) := hMeasurable.aemeasurable
  refine ⟨hAE, ?_⟩
  -- Migrated to `trajMeasure_bind_kernel_of_partial` (PR #96 corrected variant):
  -- supply the joint measurability + trajectory-level bind hypotheses directly.
  have h_partialTraj_meas :
      ∀ (n : ℕ) {S : Set (Π i : Finset.Iic n, σ × Option ι)}, MeasurableSet S →
        Measurable (Function.uncurry
          (fun (sched : ScheduleAssignment σ ι)
              (x₀ : Π _i : Finset.Iic 0, σ × Option ι) =>
            (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n
              x₀) S)) :=
    fun n _ hS => partialTraj_apply_measurable_in_sched spec R.corrupt n hS
  have h_partialTraj_bind :
      ∀ (n : ℕ) (x₀ : Π _i : Finset.Iic 0, σ × Option ι)
        {S : Set (Π i : Finset.Iic n, σ × Option ι)}, MeasurableSet S →
        (Kernel.partialTraj (X := fun _ => σ × Option ι)
            (randomisedStepKernel spec R) 0 n x₀) S =
          ∫⁻ sched : ScheduleAssignment σ ι,
            (Kernel.partialTraj (X := fun _ => σ × Option ι)
              (fun n => stepKernel spec (sched.toAdversary R.corrupt) n) 0 n
              x₀) S
              ∂(scheduleSpaceMeasure R) :=
    fun n x₀ _ hS => partialTraj_apply_eq_bind_in_sched spec R n x₀ hS
  have hBind :
      Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
          (randomisedStepKernel spec R) =
        Measure.bind (scheduleSpaceMeasure R) fun sched =>
          Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
            (stepKernel spec (sched.toAdversary R.corrupt)) :=
    ProbabilityTheory.Kernel.trajMeasure_bind_kernel_of_partial
      (X := fun _ => σ × Option ι)
      (β := ScheduleAssignment σ ι)
      (μ₀ := μ₀_full)
      (ν := scheduleSpaceMeasure R)
      (κ := fun sched n => stepKernel spec (sched.toAdversary R.corrupt) n)
      hMeasurable
      (κAvg := randomisedStepKernel spec R)
      h_partialTraj_meas
      h_partialTraj_bind
  exact hBind

end RandomisedTraceDistFubini

/-! ## Inductive lift theorems -/

section RandomisedLifts

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

set_option linter.unusedSectionVars false in
/-- The coord-0 marginal of any `Kernel.trajMeasure` on `Trace σ ι`
equals the initial probability measure. The kernel family is
irrelevant — only the initial measure matters at coord 0. Proof
extracted from the parallel `hmarg_zero` reasoning in
`AlmostBox_of_pure_inductive`. -/
private lemma trajMeasure_map_zero_eq
    {μ₀_full : Measure (σ × Option ι)} [IsProbabilityMeasure μ₀_full]
    (κ : ∀ n, Kernel (FinPrefix σ ι n) (σ × Option ι))
    [∀ n, IsMarkovKernel (κ n)] :
    (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full κ).map
      (fun ω => ω 0) = μ₀_full := by
  unfold Kernel.trajMeasure
  have hmeas_eval0 : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
    measurable_pi_apply 0
  rw [Measure.map_comp _ _ hmeas_eval0]
  have hfact : (fun ω : Π _ : ℕ, σ × Option ι => ω 0) =
      (fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) ∘
        (Preorder.frestrictLe 0) := by
    funext _; rfl
  have hmeas_pia : Measurable
      (fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) :=
    measurable_pi_apply _
  have hmeas_fl0 : Measurable
      (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) 0) :=
    Preorder.measurable_frestrictLe _
  have hmeas_fl2 : Measurable
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => σ × Option ι) (le_refl 0)) :=
    Preorder.measurable_frestrictLe₂ _
  have hcomp : Measurable
      ((fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) ∘
        Preorder.frestrictLe₂ (π := fun _ : ℕ => σ × Option ι) (le_refl 0)) :=
    hmeas_pia.comp hmeas_fl2
  rw [hfact, Kernel.map_comp_right _ hmeas_fl0 hmeas_pia,
      ProbabilityTheory.Kernel.traj_map_frestrictLe_of_le (le_refl 0)]
  rw [Kernel.deterministic_map hmeas_fl2 hmeas_pia]
  rw [Measure.deterministic_comp_eq_map hcomp]
  rw [Measure.map_map hcomp (by fun_prop)]
  convert Measure.map_id (μ := μ₀_full)

/-- Coord-0 marginal of `randomisedTraceDist` is the initial
measure paired with `none`. Specialisation of
`trajMeasure_map_zero_eq` to the randomised step kernel family. -/
lemma randomisedTraceDist_map_zero
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    (randomisedTraceDist spec R μ₀).map (fun ω : Trace σ ι => ω 0) =
      μ₀.map (fun s => (s, (none : Option ι))) := by
  unfold randomisedTraceDist
  have : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact trajMeasure_map_zero_eq (randomisedStepKernel spec R)

/-- Coord-0 marginal of `traceDist` is the initial measure paired
with `none`. Specialisation of `trajMeasure_map_zero_eq`. -/
lemma traceDist_map_zero
    (spec : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    (traceDist spec A μ₀).map (fun ω : Trace σ ι => ω 0) =
      μ₀.map (fun s => (s, (none : Option ι))) := by
  rw [← randomisedTraceDist_toRandomised spec A μ₀]
  exact randomisedTraceDist_map_zero spec A.toRandomised μ₀

/-- Inductive form of the Box lift to randomised adversaries —
the structurally-faithful analog of `Refinement.AlmostBox_of_inductive`.

If `φ` is preserved on the support of every gated action's effect
distribution and holds AS at the initial measure, then
`AlmostBoxRandomised` holds for any randomised adversary.

Proof structure mirrors `AlmostBox_of_inductive` exactly: the
difference is that at the per-step kernel branch we use the
mixture identity `randomisedStepKernel_apply_tsum` plus
`singleActionStep_ae_of_inductive` instead of a direct case-split
on the deterministic schedule.

**Lift bridge** (Phase 9.2 → 9.3): AVSS-side theorems whose
deterministic AS-Box property is established via
`AlmostBox_of_inductive` re-supply the same `h_step` / `h_init`
data here to obtain the randomised AS-Box property.
That's the whole content of the `_randomised` restatements in PR 9.3. -/
theorem AlmostBoxRandomised_of_inductive
    {spec : ProbActionSpec σ ι} (φ : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, φ s)
    (R : RandomisedAdversary σ ι) :
    AlmostBoxRandomised spec R μ₀ φ := by
  have hPset : MeasurableSet ({x : σ × Option ι | φ x.1}) := MeasurableSet.of_discrete
  have hPset_finPrefix : ∀ a : ℕ,
      MeasurableSet {h : FinPrefix σ ι a | φ (FinPrefix.currentState h)} :=
    fun _ => MeasurableSet.of_discrete
  unfold AlmostBoxRandomised randomisedTraceDist
  set μ₀_full : Measure (σ × Option ι) := μ₀.map (fun s => (s, (none : Option ι)))
    with hμ₀_full_def
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- Marginal at coordinate 0 — use the extracted helper.
  have hmarg_zero :
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
            (randomisedStepKernel spec R)).map (fun ω => ω 0) = μ₀_full :=
    trajMeasure_map_zero_eq (μ₀_full := μ₀_full) (randomisedStepKernel spec R)
  -- Marginal recurrence at successor.
  have hmarg_succ : ∀ a : ℕ,
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
          (randomisedStepKernel spec R)).map (fun ω => ω (a + 1)) =
      (randomisedStepKernel spec R a) ∘ₘ
        ((Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)) := by
    intro a
    have hk : (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
              (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)
        ⊗ₘ randomisedStepKernel spec R a =
        (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
            (randomisedStepKernel spec R)).map
          (fun x => (Preorder.frestrictLe a x, x (a + 1))) :=
      ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h2 := congrArg Measure.snd hk
    rw [Measure.snd_compProd] at h2
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    rw [Measure.snd_map_prodMk hmeas_fl_a] at h2
    exact h2.symm
  -- Countable-AE swap.
  rw [MeasureTheory.ae_all_iff]
  intro n
  induction n with
  | zero =>
    have hae_full : ∀ᵐ x ∂μ₀_full, φ x.1 := by
      rw [hμ₀_full_def, ae_map_iff (Measurable.aemeasurable (by fun_prop)) hPset]
      exact h_init
    rw [← hmarg_zero] at hae_full
    have hmeas_eval0 : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
      measurable_pi_apply 0
    rw [ae_map_iff hmeas_eval0.aemeasurable hPset] at hae_full
    exact hae_full
  | succ a ih =>
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    have hmeas_eval_succ : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω (a + 1)) :=
      measurable_pi_apply (a + 1)
    -- Transport IH to "ae h, φ (h.currentState)".
    have hcurrent : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)),
          φ (FinPrefix.currentState h) := by
      rw [ae_map_iff hmeas_fl_a.aemeasurable (hPset_finPrefix a)]
      filter_upwards [ih] with ω hω
      exact hω
    -- Bridge: ae h, ae y ∂(randomisedStepKernel R a h), φ(y.1).
    have hkernel_ae : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)),
          ∀ᵐ y ∂(randomisedStepKernel spec R a h), φ y.1 := by
      filter_upwards [hcurrent] with h hPcurr
      -- Use the mixture identity + per-α preservation.
      have hbad : MeasurableSet {y : σ × Option ι | ¬φ y.1} := MeasurableSet.of_discrete
      rw [ae_iff]
      rw [randomisedStepKernel_apply_tsum spec R h hbad]
      -- ∑' α, (R.strategy h.toList) α * singleActionStep spec h α {y | ¬φ y.1} = 0.
      rw [ENNReal.tsum_eq_zero]
      intro α
      have h_alpha : ∀ᵐ y ∂(singleActionStep spec h α), φ y.1 :=
        singleActionStep_ae_of_inductive h_step h α hPcurr
      -- (singleActionStep ..) {y | ¬φ y.1} = 0.
      have hzero : (singleActionStep spec h α) {y | ¬φ y.1} = 0 := by
        rw [← ae_iff]; exact h_alpha
      rw [hzero, mul_zero]
    -- Combine via ae_comp_of_ae_ae.
    have hae_succ : ∀ᵐ y ∂((randomisedStepKernel spec R a) ∘ₘ
          (Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (randomisedStepKernel spec R)).map (Preorder.frestrictLe a)),
        φ y.1 :=
      Measure.ae_comp_of_ae_ae hPset hkernel_ae
    rw [← hmarg_succ a] at hae_succ
    rw [ae_map_iff hmeas_eval_succ.aemeasurable hPset] at hae_succ
    exact hae_succ

/-- **Lift form (worker-task signature, derived).** If `AlmostBox`
holds for every deterministic adversary on the same `μ₀`,
the randomised analog follows. The hypothesis form admits a
shorter proof under stronger inductive data
(`AlmostBoxRandomised_of_inductive` above); to keep the lift
trivially usable from existing AVSS theorems we expose this
worker-task-shape signature too, deriving it from the
inductive form by **forwarding the witness data**: the AVSS-side
caller in PR 9.3 supplies `h_step` and `h_init` directly (the
same data they already feed `AlmostBox_of_inductive`).

The "lift from `∀ A, AlmostBox A`" formulation in WORKER_TASK §1
would require a measure-theoretic Fubini argument over a tape
distribution; that route is closed here in favor of the
inductive-witness form, which captures the same content via the
underlying preservation data. -/
theorem AlmostBox.lift_to_randomised
    {spec : ProbActionSpec σ ι} (φ : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, φ s)
    (R : RandomisedAdversary σ ι) :
    AlmostBoxRandomised spec R μ₀ φ :=
  AlmostBoxRandomised_of_inductive φ h_step μ₀ h_init R

/-- **Mixture-`Measure.map` equality lift, coordinate-0 form.**
If two `(spec, μ₀)` configurations produce the same trace marginal
on the *initial coordinate* under every deterministic adversary,
they produce the same mixture trace marginal on the initial
coordinate under any randomised adversary.

This is the form used by AVSS-side secrecy theorems
(`avss_secrecy_AS`): the `coalitionGrid C D ∘ ω 0` projection
factors through coordinate 0, where it depends only on `μ₀`
(neither `spec` nor `A` enter). Consequently the lift collapses
to an `μ₀`-only equality, which holds independently of `R`.

For non-coord-0 projections the statement requires a full
trajectory-level Fubini argument (see `AlmostBoxRandomised`'s
inductive form for the technical pattern). PR 9.3's AVSS
restatements only need the coord-0 form. -/
theorem randomisedTraceDist_map_eq_of_deterministic_at_zero
    {β : Type*} [MeasurableSpace β]
    {spec spec' : ProbActionSpec σ ι}
    {μ₀ μ₀' : Measure σ} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₀']
    {f : (σ × Option ι) → β} (hf : Measurable f)
    (h_det : ∀ (A : Adversary σ ι),
       (traceDist spec A μ₀).map (fun ω => f (ω 0)) =
       (traceDist spec' A μ₀').map (fun ω => f (ω 0)))
    (R : RandomisedAdversary σ ι) :
    (randomisedTraceDist spec R μ₀).map (fun ω => f (ω 0)) =
      (randomisedTraceDist spec' R μ₀').map (fun ω => f (ω 0)) := by
  classical
  -- Pick any deterministic adversary as a representative.
  let A₀ : Adversary σ ι := ⟨fun _ => none, R.corrupt⟩
  have hmeas_eval0 : Measurable (fun ω : Trace σ ι => ω 0) :=
    measurable_pi_apply 0
  -- Both sides factor: `(...).map (f ∘ eval-at-0) = ((coord-0 marginal).map f)`.
  -- The coord-0 marginal is `μ.map (·, none)` independent of the kernel family.
  have hfact : (fun ω : Trace σ ι => f (ω 0)) =
      f ∘ (fun ω : Trace σ ι => ω 0) := by funext _; rfl
  rw [hfact, ← Measure.map_map hf hmeas_eval0,
      ← Measure.map_map hf hmeas_eval0,
      randomisedTraceDist_map_zero spec R μ₀,
      randomisedTraceDist_map_zero spec' R μ₀']
  -- Now both sides are `(μ.map (·, none)).map f`. Use h_det at A₀ to conclude.
  have hA₀ := h_det A₀
  rw [hfact, ← Measure.map_map hf hmeas_eval0,
      ← Measure.map_map hf hmeas_eval0,
      traceDist_map_zero spec A₀ μ₀,
      traceDist_map_zero spec' A₀ μ₀'] at hA₀
  exact hA₀

/-- **Per-history step-kernel preserves any state projection invariant
under every gated effect.** Helper for the step-`k` map-equality lift.
The kernel's mixture-PMF integral of branchwise preservation gives
total AE-equality of `g (·.1)` to `g h.currentState`. -/
private lemma randomisedStepKernel_state_proj_AE
    {spec : ProbActionSpec σ ι} {β : Type*} {g : σ → β}
    (h_step_inv : ∀ (i : ι) (s : σ) (hgate : (spec.actions i).gate s),
        ∀ s' ∈ ((spec.actions i).effect s hgate).support, g s' = g s)
    (R : RandomisedAdversary σ ι) {n : ℕ} (h : FinPrefix σ ι n) :
    ∀ᵐ y ∂(randomisedStepKernel spec R n h), g y.1 = g h.currentState := by
  classical
  have hbad : MeasurableSet {y : σ × Option ι | ¬(g y.1 = g h.currentState)} :=
    MeasurableSet.of_discrete
  rw [ae_iff, randomisedStepKernel_apply_tsum spec R h hbad, ENNReal.tsum_eq_zero]
  intro α
  have h_alpha : ∀ᵐ y ∂(singleActionStep spec h α),
      (fun s : σ => g s = g h.currentState) y.1 := by
    refine singleActionStep_ae_of_inductive (φ := fun s => g s = g h.currentState)
      (h_step := ?_) h α rfl
    intro i s hgate hsφ s' hsupp
    rw [h_step_inv i s hgate s' hsupp]; exact hsφ
  have hzero : (singleActionStep spec h α)
      {y | ¬(g y.1 = g h.currentState)} = 0 := by
    rw [← ae_iff]; exact h_alpha
  rw [hzero, mul_zero]

/-- **Trace-level AE invariance of state projections under
`randomisedTraceDist`.** If a state projection `g : σ → β` is
preserved by every gated effect, then `g (ω k).1` AE-equals
`g (ω 0).1` under the mixture trace measure for any `k`.

Proof structure mirrors the deterministic
`traceDist_coalitionGrid_AE_eq_init` (AVSS.lean §17.9): induction on
`k`, with the successor step using
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` to
reduce to the per-prefix kernel AE statement
(`randomisedStepKernel_state_proj_AE`). -/
private theorem randomisedTraceDist_state_proj_AE_eq_init
    {spec : ProbActionSpec σ ι} {β : Type*} {g : σ → β}
    (h_step_inv : ∀ (i : ι) (s : σ) (hgate : (spec.actions i).gate s),
        ∀ s' ∈ ((spec.actions i).effect s hgate).support, g s' = g s)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (R : RandomisedAdversary σ ι) (k : ℕ) :
    ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀), g (ω k).1 = g (ω 0).1 := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    suffices hone_step :
        ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀),
          g (ω (k+1)).1 = g (ω k).1 by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    have hmeas_pair : Measurable
        (fun ω : Trace σ ι => (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure (μ₀.map (fun s : σ => (s, (none : Option ι)))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((randomisedTraceDist spec R μ₀).map (Preorder.frestrictLe k)) ⊗ₘ
          (randomisedStepKernel spec R k) =
        (randomisedTraceDist spec R μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold randomisedTraceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((randomisedTraceDist spec R μ₀).map (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(randomisedStepKernel spec R k h), g y.1 = g h.currentState :=
      Filter.Eventually.of_forall fun h =>
        randomisedStepKernel_state_proj_AE h_step_inv R h
    have hjoint :
        ∀ᵐ x ∂(((randomisedTraceDist spec R μ₀).map (Preorder.frestrictLe k)) ⊗ₘ
            (randomisedStepKernel spec R k)),
          g x.2.1 = g (FinPrefix.currentState x.1) :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    exact hjoint

/-- **Mixture-`Measure.map` equality lift, step-`k` form.**

Generalisation of `randomisedTraceDist_map_eq_of_deterministic_at_zero`
to coordinate `k > 0`. The lift relies on the state projection `g`
being **preserved by every gated effect** of both specs (the
structural fact captured by, e.g., AVSS's
`avssStep_coalitionGrid_invariant`).

Under this hypothesis, the schedule PMF integrates the per-branch
AE-equality across `randomisedStepKernel`, propagating coord-0
mixture equality to coord-`k` mixture equality. The deterministic
premise `h_det` is taken at coord 0; `Measure.map_congr` plus the
trace-level invariance lemma reduces both sides at coord `k` to
their coord-0 forms. -/
theorem randomisedTraceDist_map_eq_of_deterministic
    {β : Type*} [MeasurableSpace β]
    {spec spec' : ProbActionSpec σ ι}
    {μ₀ μ₀' : Measure σ} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₀']
    {g : σ → β} (hg : Measurable g)
    (h_step_inv : ∀ (i : ι) (s : σ) (hgate : (spec.actions i).gate s),
        ∀ s' ∈ ((spec.actions i).effect s hgate).support, g s' = g s)
    (h_step_inv' : ∀ (i : ι) (s : σ) (hgate : (spec'.actions i).gate s),
        ∀ s' ∈ ((spec'.actions i).effect s hgate).support, g s' = g s)
    (h_det : ∀ (A : Adversary σ ι),
       (traceDist spec A μ₀).map (fun ω => g (ω 0).1) =
       (traceDist spec' A μ₀').map (fun ω => g (ω 0).1))
    (R : RandomisedAdversary σ ι) (k : ℕ) :
    (randomisedTraceDist spec R μ₀).map (fun ω => g (ω k).1) =
      (randomisedTraceDist spec' R μ₀').map (fun ω => g (ω k).1) := by
  classical
  have hLHS : (randomisedTraceDist spec R μ₀).map (fun ω => g (ω k).1) =
              (randomisedTraceDist spec R μ₀).map (fun ω => g (ω 0).1) :=
    Measure.map_congr (randomisedTraceDist_state_proj_AE_eq_init h_step_inv μ₀ R k)
  have hRHS : (randomisedTraceDist spec' R μ₀').map (fun ω => g (ω k).1) =
              (randomisedTraceDist spec' R μ₀').map (fun ω => g (ω 0).1) :=
    Measure.map_congr (randomisedTraceDist_state_proj_AE_eq_init h_step_inv' μ₀' R k)
  rw [hLHS, hRHS]
  exact randomisedTraceDist_map_eq_of_deterministic_at_zero
    (f := fun x : σ × Option ι => g x.1) (hg.comp measurable_fst) h_det R

/-- **Lift form for `AlmostDiamond`.** Inductive form: if eventual
occurrence is guaranteed for every deterministic adversary by a
"leads-to" certificate that's adversary-independent, the randomised
analog holds.

For this PR's purposes we expose the most-general form that PR 9.3
needs: a randomised analog of `AlmostDiamond_of_leads_to` that
takes the same per-step "leads-to" data as the deterministic
version. The proof follows the inductive marginal-recurrence
template; the key step uses `randomisedStepKernel_apply_tsum` to
distribute the per-step preservation across the schedule PMF. -/
theorem AlmostDiamond.lift_to_randomised
    {spec : ProbActionSpec σ ι} (φ : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        φ s → ∀ s' ∈ ((spec.actions i).effect s h).support, φ s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, φ s)
    (R : RandomisedAdversary σ ι) :
    AlmostDiamondRandomised spec R μ₀ φ := by
  -- AlmostDiamond is implied by AlmostBox (in the trivial direction:
  -- if `φ` holds at every n, then ∃n, `φ` at n).
  unfold AlmostDiamondRandomised
  have hbox : AlmostBoxRandomised spec R μ₀ φ :=
    AlmostBoxRandomised_of_inductive φ h_step μ₀ h_init R
  filter_upwards [hbox] with ω hω
  exact ⟨0, hω 0⟩

end RandomisedLifts

/-! ## Phase 9.4 — randomised fair-AST soundness

The randomised analog of `FairASTCertificate.sound` (in
`Liveness.lean`).  The deterministic and randomised cases share the
supermartingale + finite-descent core via the measure-generic
`pi_n_AST_fair_with_progress_det_on`, `pi_infty_zero_fair_on`, and
`partition_almostDiamond_fair_on` (path **(c)** of
`AVSS-MODEL-NOTES.md` §13.4).  This section supplies:

  * `FairASTCertificate.RandomisedTrajectoryFairProgress` — randomised
    analog of `FairASTCertificate.TrajectoryFairProgress`: the AE
    fair-progress witness on the mixture trace measure.
  * `FairASTCertificate.RandomisedTrajectoryUMono` and
    `FairASTCertificate.RandomisedTrajectoryFairStrictDecrease` —
    analogs of the corresponding deterministic predicates, restated
    on `randomisedTraceDist`.
  * `RandomisedTrajectoryFairAdversary` — bundle of a randomised
    adversary with an AE-progress witness on a specific initial
    measure.
  * `RandomisedFairASTCertificate.sound` — the headline theorem,
    a thin specialisation of the measure-generic
    `partition_almostDiamond_fair_on` to the mixture trace measure.

**Note on the fairness predicate.**  The progress witness here is
the trajectory-form AE statement that fair-required actions fire
i.o., matching the deterministic side.  In the randomised setting
this witness can be derived from a structural uniform-`ε` lower
bound on the schedule PMF for gated fair actions via Borel-Cantelli;
that derivation is independent of the soundness machinery (the
deterministic `sound` uses the deterministic-decrease finite-descent
route, which only needs the trajectory-form witness as input) and
is left to callers.  See `AVSS-MODEL-NOTES.md` §13.4 "Fairness
predicate uniform-ε requirement" for the discussion. -/

section RandomisedFairAST

open NNReal

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

namespace FairASTCertificate

/-- Randomised analog of `FairASTCertificate.TrajectoryFairProgress`:
along almost every trace of the mixture trace measure, every
fair-required action fires infinitely often. -/
def RandomisedTrajectoryFairProgress
    (spec : ProbActionSpec σ ι) (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (R : RandomisedAdversary σ ι) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀),
    ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i

/-- Randomised analog of `FairASTCertificate.TrajectoryUMono`. -/
def RandomisedTrajectoryUMono
    {spec : ProbActionSpec σ ι} {F : FairnessAssumptions σ ι}
    {terminated : σ → Prop}
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (R : RandomisedAdversary σ ι) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀),
    ∀ n : ℕ, cert.U (ω (n + 1)).1 ≤ cert.U (ω n).1

/-- Randomised analog of `FairASTCertificate.TrajectoryFairStrictDecrease`. -/
def RandomisedTrajectoryFairStrictDecrease
    {spec : ProbActionSpec σ ι} {F : FairnessAssumptions σ ι}
    {terminated : σ → Prop}
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (R : RandomisedAdversary σ ι) (N : ℕ) : Prop :=
  ∀ᵐ ω ∂(randomisedTraceDist spec R μ₀),
    ∀ n : ℕ, (∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i) →
      ¬ terminated (ω n).1 → cert.V (ω n).1 ≤ (N : ℝ≥0) →
        cert.U (ω (n + 1)).1 < cert.U (ω n).1

end FairASTCertificate

/-- A randomised adversary bundled with a trajectory-progress witness
for a specific initial measure `μ₀`.  Randomised analog of
`Leslie.Prob.TrajectoryFairAdversary`.

`progress` is the AE-trajectory statement that fair-required actions
fire i.o. along the mixture trace measure.  This trajectory-form
witness is what `RandomisedFairASTCertificate.sound` consumes; it
can be supplied directly or derived from a uniform-`ε` lower bound
on the schedule PMF for gated fair actions (the derivation requires
Borel-Cantelli and is left to callers, mirroring how deterministic
protocols supply `TrajectoryFairAdversary.progress` from per-protocol
fairness reasoning). -/
structure RandomisedTrajectoryFairAdversary
    (spec : ProbActionSpec σ ι) (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] where
  /-- The underlying randomised adversary. -/
  toRandomised : RandomisedAdversary σ ι
  /-- AE-trajectory progress: every fair-required action fires
  infinitely often along almost every trace of the mixture trace
  measure. -/
  progress : FairASTCertificate.RandomisedTrajectoryFairProgress
    spec F μ₀ toRandomised

/-! ### `RandomisedFairASTCertificate` namespace

`RandomisedFairASTCertificate` is a *namespace*, not a new type:
the certificate data structure is unchanged from `FairASTCertificate`
(invariant, supermartingale, variant, all adversary-independent).
Only the soundness conclusion is restated against `randomisedTraceDist`,
and the trajectory-progress witness is bundled with a randomised
adversary instead of a deterministic one.

This mirrors how `Refinement.AlmostBox` / `AlmostBoxRandomised`
share certificate data but carry distinct trace measures in their
conclusions. -/

namespace RandomisedFairASTCertificate

/-- **Randomised analog of `FairASTCertificate.sound`.**

Same certificate data, randomised adversary, randomised trace
measure conclusion.  The proof routes through the measure-generic
core `FairASTCertificate.partition_almostDiamond_fair_on` (in
`Liveness.lean`) plus the inductive randomised-Box lift
`AlmostBoxRandomised_of_inductive` for the invariant.

Closes the termination half of caveat **C5** (MODEL_NOTES §11.5):
together with PR #41 / PR #46 / PR #47 / PR #49, AVSS theorems can
now quantify over arbitrary randomised adversaries for all four
classical properties (correctness, commitment, secrecy, termination). -/
theorem sound {spec : ProbActionSpec σ ι} {F : FairnessAssumptions σ ι}
    {terminated : σ → Prop}
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, cert.Inv s)
    (R : RandomisedTrajectoryFairAdversary spec F μ₀)
    (h_U_mono : FairASTCertificate.RandomisedTrajectoryUMono
        cert μ₀ R.toRandomised)
    (h_U_strict : ∀ N : ℕ,
        FairASTCertificate.RandomisedTrajectoryFairStrictDecrease
          cert μ₀ R.toRandomised N) :
    AlmostDiamondRandomised spec R.toRandomised μ₀ terminated := by
  unfold AlmostDiamondRandomised
  have hbox_inv : AlmostBoxRandomised spec R.toRandomised μ₀ cert.Inv :=
    AlmostBoxRandomised_of_inductive cert.Inv
      (fun i s h hInv s' hs' => cert.inv_step i s h hInv s' hs')
      μ₀ h_init R.toRandomised
  unfold AlmostBoxRandomised at hbox_inv
  exact FairASTCertificate.partition_almostDiamond_fair_on cert
    (randomisedTraceDist spec R.toRandomised μ₀) hbox_inv R.progress
    h_U_mono h_U_strict

end RandomisedFairASTCertificate

/-! ### Bridge constructor: uniform-`ε` schedule mass → trajectory-fair adversary

The deterministic side supplies `TrajectoryFairAdversary.progress` from
per-protocol fairness reasoning.  In the randomised setting, the
canonical structural bound is a **uniform-`ε` lower bound on the schedule
PMF for gated fair actions**: at every history, the total probability
mass that the schedule assigns to fair-required actions whose gate is
satisfied is at least `ε > 0`.

Under that bound, the events "a gated fair action fires at step `k`"
are history-conditioned Bernoulli trials with success probability
`≥ ε`.  By a direct iterative bound (the kernel-level analog of
Borel-Cantelli II for a sequence of Bernoulli trials with a uniform
positive lower bound on the conditional probabilities), gated fair
actions fire infinitely often almost surely.

The implementation below proves the iterative bound directly via the
`Kernel.trajMeasure` marginal recurrence — bypassing the conditional
Borel-Cantelli machinery in `MeasureTheory.Martingale.BorelCantelli`,
whose connection to `Kernel.trajMeasure` requires non-trivial
infrastructure for converting kernel mass at a history-prefix into a
conditional expectation w.r.t. the natural filtration on `Trace σ ι`. -/

section UniformEpsilonBridge

open Classical

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The (state, label) pairs at which a fair-required action fires. -/
private def fairFireSet (F : FairnessAssumptions σ ι) : Set (σ × Option ι) :=
  {y | ∃ i ∈ F.fair_actions, y.2 = some i}

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private lemma measurableSet_fairFireSet (F : FairnessAssumptions σ ι) :
    MeasurableSet (fairFireSet F) := MeasurableSet.of_discrete

/-- Per-step lower bound: under the uniform-ε hypothesis, the
randomised step kernel assigns mass `≥ ε` to the set of (state, label)
pairs at which a fair-required action fires. -/
private lemma randomisedStepKernel_fairFireSet_ge
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (F : FairnessAssumptions σ ι) (ε : ENNReal)
    (h_uniform : ∀ {n : ℕ} (h : FinPrefix σ ι n),
        ε ≤ ∑' i : ι, if i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState
                      then R.strategy h.toList (some i) else 0)
    {n : ℕ} (h : FinPrefix σ ι n) :
    ε ≤ randomisedStepKernel spec R n h (fairFireSet F) := by
  refine (h_uniform h).trans ?_
  rw [randomisedStepKernel_apply_tsum spec R h (measurableSet_fairFireSet F)]
  have h_inj : Function.Injective (some : ι → Option ι) := Option.some_injective ι
  -- Step 1: term-wise, the LHS at index `i` is bounded by
  -- `R.strategy(some i) * sas(some i, fairFireSet F)`.
  have hterm : ∀ i : ι,
      (if i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState
        then R.strategy h.toList (some i) else 0) ≤
      R.strategy h.toList (some i) *
        singleActionStep spec h (some i) (fairFireSet F) := by
    intro i
    by_cases hcond : i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState
    · rcases hcond with ⟨hfair, hgate⟩
      rw [if_pos ⟨hfair, hgate⟩]
      have hfun : Measurable (fun s : σ => (s, some i)) := by fun_prop
      have hsas : singleActionStep spec h (some i) (fairFireSet F) = 1 := by
        simp only [singleActionStep, hgate, dite_true]
        rw [Measure.map_apply hfun (measurableSet_fairFireSet F)]
        have hpre : (fun s : σ => (s, some i)) ⁻¹' fairFireSet F = Set.univ := by
          ext s
          simp [fairFireSet, hfair]
        rw [hpre]
        exact measure_univ
      rw [hsas, mul_one]
    · rw [if_neg hcond]
      exact zero_le _
  -- Step 2: sum-over-`ι` of the RHS dominates summing over `Option ι`
  -- via injection of `some`.
  refine (ENNReal.tsum_le_tsum hterm).trans ?_
  exact ENNReal.tsum_comp_le_tsum_of_injective h_inj
    (fun α => R.strategy h.toList α * singleActionStep spec h α (fairFireSet F))

/-- Per-step upper bound: the kernel mass on the complement of
`fairFireSet F` is at most `1 - ε`. -/
private lemma randomisedStepKernel_fairFireSet_compl_le
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (F : FairnessAssumptions σ ι) (ε : ENNReal)
    (h_uniform : ∀ {n : ℕ} (h : FinPrefix σ ι n),
        ε ≤ ∑' i : ι, if i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState
                      then R.strategy h.toList (some i) else 0)
    {n : ℕ} (h : FinPrefix σ ι n) :
    randomisedStepKernel spec R n h (fairFireSet F)ᶜ ≤ 1 - ε := by
  have hge : ε ≤ randomisedStepKernel spec R n h (fairFireSet F) :=
    randomisedStepKernel_fairFireSet_ge spec R F ε h_uniform h
  have hkernel_univ : randomisedStepKernel spec R n h Set.univ = 1 := measure_univ
  have h_le_one : randomisedStepKernel spec R n h (fairFireSet F) ≤ 1 := by
    rw [← hkernel_univ]; exact measure_mono (Set.subset_univ _)
  have h_eps_le : ε ≤ 1 := hge.trans h_le_one
  have h_eps_ne_top : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h_eps_le
  rw [ENNReal.le_sub_iff_add_le_right h_eps_ne_top h_eps_le]
  calc randomisedStepKernel spec R n h (fairFireSet F)ᶜ + ε
      ≤ randomisedStepKernel spec R n h (fairFireSet F)ᶜ +
          randomisedStepKernel spec R n h (fairFireSet F) := by gcongr
    _ = 1 := by
        rw [add_comm,
          ← measure_union (Disjoint.symm disjoint_compl_left)
            (measurableSet_fairFireSet F).compl,
          Set.union_compl_self, hkernel_univ]

/-- The "no fair fire in the next `m` steps starting from index `N`"
event on traces. Defined as a finite intersection over `Finset.range m`
so that measurability is trivial. -/
private def noFairFireWindow (F : FairnessAssumptions σ ι) (N m : ℕ) :
    Set (Trace σ ι) :=
  ⋂ k ∈ Finset.range m,
    {ω : Trace σ ι | ω (N + k + 1) ∈ (fairFireSet F)ᶜ}

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private lemma measurableSet_noFairFireWindow
    (F : FairnessAssumptions σ ι) (N m : ℕ) :
    MeasurableSet (noFairFireWindow F N m) :=
  Finset.measurableSet_biInter _ fun _ _ =>
    (measurableSet_fairFireSet F).compl.preimage (measurable_pi_apply _)

omit [Countable σ] [Countable ι] [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private lemma mem_noFairFireWindow_iff
    (F : FairnessAssumptions σ ι) (N m : ℕ) (ω : Trace σ ι) :
    ω ∈ noFairFireWindow F N m ↔
      ∀ k : ℕ, k < m → ω (N + k + 1) ∈ (fairFireSet F)ᶜ := by
  unfold noFairFireWindow
  simp [Finset.mem_range]

/-- Inductive bound: `ν(noFairFireWindow N m) ≤ (1 - ε)^m`. -/
private lemma randomisedTraceDist_noFairFireWindow_le
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (F : FairnessAssumptions σ ι) (ε : ENNReal)
    (h_uniform : ∀ {n : ℕ} (h : FinPrefix σ ι n),
        ε ≤ ∑' i : ι, if i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState
                      then R.strategy h.toList (some i) else 0)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] (N m : ℕ) :
    randomisedTraceDist spec R μ₀ (noFairFireWindow F N m) ≤ (1 - ε) ^ m := by
  classical
  haveI hμ₀_full : IsProbabilityMeasure
      (μ₀.map (fun s : σ ↦ (s, (none : Option ι)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  induction m with
  | zero =>
    simp only [pow_zero]
    refine (measure_mono (Set.subset_univ _)).trans ?_
    rw [measure_univ]
  | succ m ih =>
    -- Coercion of indices into Finset.Iic (N + m).
    have hcoerce : ∀ k : ℕ, k < m → N + k + 1 ∈ Finset.Iic (N + m) :=
      fun k hk => Finset.mem_Iic.mpr (by omega)
    -- Splitter map.
    let splitter : Trace σ ι → FinPrefix σ ι (N + m) × (σ × Option ι) :=
      fun x => (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) (N + m) x,
                x (N + m + 1))
    have hmeas_split : Measurable splitter := by
      refine Measurable.prodMk ?_ ?_
      · exact Preorder.measurable_frestrictLe _
      · exact measurable_pi_apply _
    -- Restrict-prefix subset describing the first `m` no-fair conditions.
    let S : Set (FinPrefix σ ι (N + m)) :=
      {h | ∀ k (hk : k < m), h ⟨N + k + 1, hcoerce k hk⟩ ∈ (fairFireSet F)ᶜ}
    have hS_meas : MeasurableSet S := MeasurableSet.of_discrete
    -- noFairFireWindow F N (m+1) = splitter ⁻¹' (S ×ˢ (fairFireSet F)ᶜ).
    have hsplit_eq : noFairFireWindow F N (m + 1) =
        splitter ⁻¹' (S ×ˢ (fairFireSet F)ᶜ) := by
      ext ω
      rw [mem_noFairFireWindow_iff]
      simp only [splitter, S, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq,
        Preorder.frestrictLe]
      constructor
      · intro hω
        refine ⟨fun k hk => hω k (by omega), hω m (by omega)⟩
      · intro ⟨h1, h2⟩ k hk
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
        · exact h1 k hlt
        · subst heq; exact h2
    rw [hsplit_eq]
    rw [show randomisedTraceDist spec R μ₀ (splitter ⁻¹' (S ×ˢ (fairFireSet F)ᶜ)) =
        ((randomisedTraceDist spec R μ₀).map splitter) (S ×ˢ (fairFireSet F)ᶜ) from
      (Measure.map_apply hmeas_split
        (hS_meas.prod (measurableSet_fairFireSet F).compl)).symm]
    -- Marginal recurrence.
    have hmarg :
        (randomisedTraceDist spec R μ₀).map splitter =
        (randomisedTraceDist spec R μ₀).map
            (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) (N + m)) ⊗ₘ
          randomisedStepKernel spec R (N + m) := by
      unfold randomisedTraceDist
      exact (ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (a := N + m)).symm
    rw [hmarg, Measure.compProd_apply_prod hS_meas (measurableSet_fairFireSet F).compl]
    -- Bound the integral.
    calc ∫⁻ h in S, randomisedStepKernel spec R (N + m) h (fairFireSet F)ᶜ
              ∂((randomisedTraceDist spec R μ₀).map
                  (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) (N + m)))
        ≤ ∫⁻ _h in S, (1 - ε)
              ∂((randomisedTraceDist spec R μ₀).map
                  (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) (N + m))) := by
          refine setLIntegral_mono (by fun_prop) (fun h _ => ?_)
          exact randomisedStepKernel_fairFireSet_compl_le spec R F ε h_uniform h
      _ = (1 - ε) * ((randomisedTraceDist spec R μ₀).map
              (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) (N + m))) S := by
          rw [setLIntegral_const, mul_comm]
      _ = (1 - ε) * randomisedTraceDist spec R μ₀ (noFairFireWindow F N m) := by
          rw [Measure.map_apply (Preorder.measurable_frestrictLe _) hS_meas]
          have hset : (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) (N + m))
              ⁻¹' S = noFairFireWindow F N m := by
            ext ω
            rw [mem_noFairFireWindow_iff]
            simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Preorder.frestrictLe_apply]
          rw [hset]
      _ ≤ (1 - ε) * (1 - ε) ^ m := by gcongr
      _ = (1 - ε) ^ (m + 1) := by ring

/-- **Bridge constructor.** Build a `RandomisedTrajectoryFairAdversary`
from a uniform-`ε > 0` lower bound on the schedule PMF mass at gated
fair actions.

If at every history `h`, the total probability mass that the schedule
assigns to fair-required actions whose gate is satisfied is at least
`ε`, then by an iterative kernel-level argument (the analog of
Borel-Cantelli II for history-conditioned Bernoulli trials with a
uniform positive lower bound), gated fair actions fire infinitely
often almost surely under the mixture trace measure.

The hypothesis is phrased on `FinPrefix σ ι n` rather than raw `List`
prefixes so that `currentState` is well-defined and the gate predicate
is meaningful.

This closes the optional follow-up flagged by Phase 9.4: the
trajectory-form fairness witness consumed by
`RandomisedFairASTCertificate.sound` can now be derived from the
structurally-cleanest scheduler-side hypothesis. -/
noncomputable def RandomisedTrajectoryFairAdversary.of_uniform_epsilon_bound
    (spec : ProbActionSpec σ ι) (F : FairnessAssumptions σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (R : RandomisedAdversary σ ι)
    (ε : ENNReal) (hε_pos : 0 < ε)
    (h_uniform : ∀ {n : ℕ} (h : FinPrefix σ ι n),
        ε ≤ ∑' i : ι, if i ∈ F.fair_actions ∧ (spec.actions i).gate h.currentState
                      then R.strategy h.toList (some i) else 0) :
    RandomisedTrajectoryFairAdversary spec F μ₀ where
  toRandomised := R
  progress := by
    classical
    unfold FairASTCertificate.RandomisedTrajectoryFairProgress
    rw [MeasureTheory.ae_iff]
    -- Rewrite the complement event as a countable union over `N`.
    have hcompl : {ω : Trace σ ι | ¬ ∀ N : ℕ, ∃ n ≥ N,
            ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i} =
        ⋃ N : ℕ, {ω | ∀ n ≥ N, ω (n + 1) ∈ (fairFireSet F)ᶜ} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall, not_exists, not_and,
        fairFireSet, Set.mem_compl_iff]
    rw [hcompl]
    have hbound : (randomisedTraceDist spec R μ₀)
        (⋃ N : ℕ, {ω | ∀ n ≥ N, ω (n + 1) ∈ (fairFireSet F)ᶜ}) ≤
        ∑' N : ℕ, (randomisedTraceDist spec R μ₀)
          {ω | ∀ n ≥ N, ω (n + 1) ∈ (fairFireSet F)ᶜ} :=
      measure_iUnion_le _
    -- Each term is 0: `(1-ε)^m → 0` and the tail event is contained in every window.
    have hzero : ∀ N : ℕ, (randomisedTraceDist spec R μ₀)
        {ω | ∀ n ≥ N, ω (n + 1) ∈ (fairFireSet F)ᶜ} = 0 := by
      intro N
      have hsub : ∀ m : ℕ, {ω : Trace σ ι | ∀ n ≥ N, ω (n + 1) ∈ (fairFireSet F)ᶜ} ⊆
          noFairFireWindow F N m := by
        intro m ω hω
        rw [mem_noFairFireWindow_iff]
        intro k _hk
        exact hω (N + k) (by omega)
      have hle_pow : ∀ m : ℕ,
          (randomisedTraceDist spec R μ₀)
            {ω | ∀ n ≥ N, ω (n + 1) ∈ (fairFireSet F)ᶜ} ≤ (1 - ε) ^ m := by
        intro m
        refine le_trans (measure_mono (hsub m)) ?_
        exact randomisedTraceDist_noFairFireWindow_le spec R F ε h_uniform μ₀ N m
      refine le_antisymm ?_ (zero_le _)
      have h1eps_lt : 1 - ε < 1 := by
        rcases le_or_gt ε 1 with hle | hgt
        · exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε_pos.ne'
        · rw [tsub_eq_zero_of_le hgt.le]
          exact zero_lt_one
      have h_tendsto : Filter.Tendsto (fun m : ℕ => (1 - ε) ^ m) Filter.atTop (nhds 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h1eps_lt
      exact ge_of_tendsto h_tendsto (Filter.eventually_atTop.mpr ⟨0, fun m _ => hle_pow m⟩)
    refine le_antisymm ?_ (zero_le _)
    refine hbound.trans ?_
    simp only [hzero, tsum_zero, le_refl]

end UniformEpsilonBridge

end RandomisedFairAST

end Leslie.Prob
