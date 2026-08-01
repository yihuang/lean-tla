/-
M3 W4 (Phase 11-α + 11-β) — Secrecy framework abstraction.

Phase 11-α (PR #71) introduced two predicates over deterministic
adversaries:

  * `Secrecy spec μ₀ proj` — under any deterministic adversary, the
    projected trace distribution doesn't depend on the secret. The
    protocol-independent notion of operational view-secrecy.
  * `SecrecyRushing` — view-restricted variant: the adversary's
    schedule depends only on a `ProtocolView` projection. Mirrors
    Canetti–Rabin '93 / Goldwasser–Lindell '02.

Phase 11-β (this PR) adds the **randomised** counterparts, mirroring
the deterministic stack against `RandomisedAdversary` and
`RushingRandomisedAdversary`:

  * `SecrecyRandomised spec μ₀ proj` — universal over randomised
    schedules, on the mixture trace measure (`randomisedTraceDist`).
  * `SecrecyRushingRandomised` — view-restricted randomised variant.

The "easy" direction `SecrecyRandomised → Secrecy` (specialise
through `Adversary.toRandomised`) is proven inline.  The converse
`Secrecy → SecrecyRandomised` is the **hard direction** —
established in `Secrecy.toRandomised` via Fubini over deterministic
schedules: the randomised mixture trace measure decomposes into an
integral over deterministic schedules induced by `R`, the
deterministic `Secrecy` hypothesis applies pointwise, and the
projected equality lifts under the integral.

After Phase 11-β-followup-7 (Worker 7), the chain is **closed**:
`Secrecy.toRandomised` is sorry-free in this file, and the entire
`Secrecy ↔ SecrecyRandomised` correspondence reduces to a single
named framework sorry in `Leslie.Prob.RandomisedAdversary`
(`randomisedTraceDist_eq_bind_traceDist`), which captures the
parameterised Ionescu–Tulcea cylinder-uniqueness content that
mathlib does not currently expose.

Each example protocol (AVSS, BivariateShamir, ...) instantiates
`Secrecy` / `SecrecyRushing` / `SecrecyRandomised` /
`SecrecyRushingRandomised` with its specific projection. This file
is purely abstract; protocol-specific theorems live in
`Leslie/Examples/Prob/`.

Per implementation plan v2.2 §M3 W4 + design plan v2.2
§"Secrecy framework abstraction", Phase 11-α (PR #71) + Phase 11-β
(this PR).
-/

import Leslie.Prob.Trace
import Leslie.Prob.Adversary
import Leslie.Prob.RandomisedAdversary
import Mathlib.Probability.ProductMeasure

namespace Leslie.Prob

open MeasureTheory

/-! ## Definitions -/

variable {σ ι : Type*}
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A protocol satisfies **operational secrecy** with respect to a
secret-indexed initial-measure family `μ₀ : Sec → Measure σ` and a
coalition projection `proj : Trace σ ι → V` if every two secrets
produce the same projected trace distribution under any
deterministic adversary.

The secret is encoded in the initial state (via `μ₀`); the
adversary's view of the trace through `proj` (typically the
corrupt-coalition view + schedule prefix) is the only operational
quantity that matters for secrecy. The claim says: this view is
distributed identically across secrets. -/
def Secrecy
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (A : Adversary σ ι),
    (traceDist spec A (μ₀ sec)).map proj =
    (traceDist spec A (μ₀ sec')).map proj

/-- View-restricted (rushing) secrecy: the rushing adversary's
schedule depends only on the `ProtocolView W` projection of the
state-history. Quantifies over `RushingAdversary σ ι W` whose
attached `ProtocolView` matches `view`.

This is strictly weaker than `Secrecy spec μ₀ proj` (the universal
adversary class is a strict superset of the rushing-adversary
image), so plain secrecy implies rushing-secrecy
(`Secrecy.toRushing`). The converse requires a separate factorisation
argument and is protocol-specific. -/
def SecrecyRushing
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V W : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (view : ProtocolView σ W)
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (R : RushingAdversary σ ι W),
    R.toProtocolView = view →
    (traceDist spec R.toAdversary (μ₀ sec)).map proj =
    (traceDist spec R.toAdversary (μ₀ sec')).map proj

/-! ## Structural lemmas -/

/-- Secrecy is **monotone in the projection**: applying a
measurable map `f` after `proj₁` yields a coarser projection
that still preserves secrecy. Proof is by `Measure.map_map`
followed by the original equality.

For the more general factorisation form (`proj₂ = f ∘ proj₁`),
`rw` against the factorisation and then apply this lemma. -/
theorem Secrecy.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : Secrecy spec μ₀ proj₁) :
    Secrecy spec μ₀ (f ∘ proj₁) := by
  intro sec sec' A
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' A]

/-- Rushing-secrecy is monotone in the projection, mirroring
`Secrecy.mono_proj`. -/
theorem SecrecyRushing.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ W : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {view : ProtocolView σ W}
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : SecrecyRushing spec μ₀ view proj₁) :
    SecrecyRushing spec μ₀ view (f ∘ proj₁) := by
  intro sec sec' R hR
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' R hR]

/-- Plain secrecy implies rushing-secrecy (for any view). The
universal claim over all deterministic adversaries specialises to
the image of `RushingAdversary.toAdversary`, so any
`R : RushingAdversary σ ι W` can be plugged in directly.

The hypothesis `R.toProtocolView = view` is irrelevant on this
side: `Secrecy` doesn't constrain the view at all, so the
rushing-secrecy conclusion holds for the requested view (or any
other) trivially. -/
theorem Secrecy.toRushing
    {spec : ProbActionSpec σ ι}
    {Sec V W : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (view : ProtocolView σ W)
    (h : Secrecy spec μ₀ proj) :
    SecrecyRushing spec μ₀ view proj := by
  intro sec sec' R _hR
  exact h sec sec' R.toAdversary

/-! ## Phase 11-β — Randomised counterparts -/

/-- **Randomised operational secrecy.**  Under any *randomised*
adversary `R : RandomisedAdversary σ ι` (kernel-mixture schedule),
the projected mixture trace distribution doesn't depend on the
secret.

This is the literature-standard threat model for AVSS-style
secrecy claims (Canetti–Rabin '93, Backes-Pfitzmann-Waidner): the
adversary may flip coins to choose the schedule, but the corrupt
coalition's view distribution is identical across secrets.

Defined identically to `Secrecy` but with `randomisedTraceDist` in
place of `traceDist`. -/
def SecrecyRandomised
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (R : RandomisedAdversary σ ι),
    (randomisedTraceDist spec R (μ₀ sec)).map proj =
    (randomisedTraceDist spec R (μ₀ sec')).map proj

/-- **Randomised rushing operational secrecy.**  View-restricted
randomised analog of `SecrecyRushing`: quantifies over
`RushingRandomisedAdversary σ ι W` (PMF-valued schedules on view-
histories).  The adversary's randomised schedule sees only the
`ProtocolView W` projection of the state-history.

This is the most literature-faithful threat model in the framework:
randomised + rushing combines the two literature-standard adversarial
powers.  It is strictly weaker than `SecrecyRandomised`, which
quantifies over the full universal class of randomised schedulers
(state-history visible). -/
def SecrecyRushingRandomised
    (spec : ProbActionSpec σ ι)
    {Sec : Type*}
    {V W : Type*} [MeasurableSpace V]
    (μ₀ : Sec → Measure σ) [∀ s, IsProbabilityMeasure (μ₀ s)]
    (view : ProtocolView σ W)
    (proj : Trace σ ι → V) : Prop :=
  ∀ (sec sec' : Sec) (R : RushingRandomisedAdversary σ ι W),
    R.toProtocolView = view →
    (randomisedTraceDist spec R.toRandomisedAdversary (μ₀ sec)).map proj =
    (randomisedTraceDist spec R.toRandomisedAdversary (μ₀ sec')).map proj

/-- `SecrecyRandomised` is monotone in the projection, mirroring
`Secrecy.mono_proj`. -/
theorem SecrecyRandomised.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : SecrecyRandomised spec μ₀ proj₁) :
    SecrecyRandomised spec μ₀ (f ∘ proj₁) := by
  intro sec sec' R
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' R]

/-- `SecrecyRushingRandomised` is monotone in the projection,
mirroring `SecrecyRushing.mono_proj`. -/
theorem SecrecyRushingRandomised.mono_proj
    {spec : ProbActionSpec σ ι}
    {Sec V₁ V₂ W : Type*}
    [MeasurableSpace V₁] [MeasurableSpace V₂]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {view : ProtocolView σ W}
    {proj₁ : Trace σ ι → V₁} (hproj₁ : Measurable proj₁)
    (f : V₁ → V₂) (hf : Measurable f)
    (h : SecrecyRushingRandomised spec μ₀ view proj₁) :
    SecrecyRushingRandomised spec μ₀ view (f ∘ proj₁) := by
  intro sec sec' R hR
  rw [← Measure.map_map hf hproj₁, ← Measure.map_map hf hproj₁, h sec sec' R hR]

/-- Randomised secrecy implies plain (deterministic) secrecy: the
universal claim over `RandomisedAdversary` specialises to the image
of `Adversary.toRandomised`, and `randomisedTraceDist_toRandomised`
shows the mixture trace at a deterministic-lift adversary equals
the deterministic trace.

This is the **easy direction** of the
`Secrecy ↔ SecrecyRandomised` correspondence; the converse requires
Fubini over deterministic schedules and is queued for a follow-up
PR (see file docstring). -/
theorem SecrecyRandomised.toSecrecy
    {spec : ProbActionSpec σ ι}
    {Sec V : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (h : SecrecyRandomised spec μ₀ proj) :
    Secrecy spec μ₀ proj := by
  intro sec sec' A
  have hsec  := h sec sec' A.toRandomised
  rw [randomisedTraceDist_toRandomised, randomisedTraceDist_toRandomised] at hsec
  exact hsec

/-- Randomised secrecy implies rushing-randomised secrecy (for any
view).  The universal claim over `RandomisedAdversary` specialises
to the image of `RushingRandomisedAdversary.toRandomisedAdversary`,
so any `R : RushingRandomisedAdversary σ ι W` plugs in directly.

The view hypothesis is irrelevant on this side, mirroring
`Secrecy.toRushing`. -/
theorem SecrecyRandomised.toRushingRandomised
    {spec : ProbActionSpec σ ι}
    {Sec V W : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V}
    (view : ProtocolView σ W)
    (h : SecrecyRandomised spec μ₀ proj) :
    SecrecyRushingRandomised spec μ₀ view proj := by
  intro sec sec' R _hR
  exact h sec sec' R.toRandomisedAdversary

/-! ## Phase 11-β-followup — `Secrecy → SecrecyRandomised`

The **hard direction** of the `Secrecy ↔ SecrecyRandomised`
correspondence: deterministic secrecy implies randomised secrecy.

**Mathematical content.**  Given a randomised adversary
`R : RandomisedAdversary σ ι`, the mixture trace measure
`randomisedTraceDist spec R μ` decomposes as a Fubini integral of
deterministic trace measures over a probability measure on
deterministic schedules.  Concretely, R's per-history PMFs
`R.strategy : List (σ × Option ι) → PMF (Option ι)` induce a
probability measure on the function space
`List (σ × Option ι) → Option ι` of "schedule assignments" via the
Kolmogorov / Ionescu-Tulcea construction.  Each such assignment
defines a deterministic `Adversary σ ι`; the mixture trace measure
is then the integral of deterministic trace measures over this
schedule-assignment measure.

Once the factorisation is established, the deterministic `Secrecy`
hypothesis applies pointwise under the integral, swapping the secret
and yielding the randomised conclusion via congruence of integrals.

**Sorry inventory (Phase 11-β-followup-7, Worker 7 — chain finale).**

  * `Phase 11-β-followup-2` — ✅ closed (Worker 2). `scheduleSpaceMeasure`
    + its `IsProbabilityMeasure` instance use mathlib's
    `MeasureTheory.Measure.infinitePi`.
  * `Phase 11-β-followup-3` — ✅ closed (Worker 3). Per-step
    factorisation + schedule-space marginal.
  * `Phase 11-β-followup-4` — ✅ closed (Worker 4). `Secrecy.toRandomised`
    fully proved modulo the trajectory-level Fubini sub-claim.
  * `Phase 11-β-followup-6` — ✅ closed (Worker 6). Chain split into
    two independent helpers `_traj_aeMeasurable` / `_traj_bind_eq`.
  * `Phase 11-β-followup-7` — ✅ closed (Worker 7, this PR).
    The schedule-space machinery (`ScheduleAssignment`,
    `scheduleSpaceMeasure`) and the framework lemma
    `randomisedTraceDist_eq_bind_traceDist` were promoted from this
    file to `Leslie.Prob.RandomisedAdversary` so that the chain has a
    *single* named framework sorry. Both `_traj_aeMeasurable` and
    `_traj_bind_eq` in this file are now trivial projections of the
    framework lemma, eliminating every sorry from `Secrecy.lean`.

The single remaining `sorryAx` is in
`Leslie.Prob.randomisedTraceDist_eq_bind_traceDist`, capturing the
parameterised Ionescu–Tulcea cylinder-uniqueness content that mathlib
does not expose. See its docstring for the proof outline. -/

/-! ### Schedule-space machinery

Re-exported from `Leslie.Prob.RandomisedAdversary` for legibility.
The `ScheduleAssignment σ ι` type, `scheduleSpaceMeasure`, and the
framework lemma `randomisedTraceDist_eq_bind_traceDist` all live in
that file (Phase 11-β-followup-7 promotion). -/

set_option linter.unusedSectionVars false in
/-- **Phase 11-β-followup-3a-i (closed, Worker 7).**
AEMeasurability of the trajectory-distribution integrand
`sched ↦ traceDist spec (sched.toAdversary R.corrupt) μ` w.r.t. the
schedule-space measure.

A trivial `.1` projection of the framework lemma
`randomisedTraceDist_eq_bind_traceDist` (in
`Leslie.Prob.RandomisedAdversary`). -/
private lemma randomisedTraceDist_eq_integral_traceDist_traj_aeMeasurable
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    AEMeasurable
        (fun sched : ScheduleAssignment σ ι =>
          traceDist spec (sched.toAdversary R.corrupt) μ)
        (scheduleSpaceMeasure R) :=
  (randomisedTraceDist_eq_bind_traceDist spec R μ).1

set_option linter.unusedSectionVars false in
/-- **Phase 11-β-followup-3a-ii (closed, Worker 7).** Bind equality
for the trajectory-level Fubini factorisation.

The randomised mixture trace measure equals the `Measure.bind` of
the deterministic trace measures over the schedule-space measure.

A trivial `.2` projection of the framework lemma
`randomisedTraceDist_eq_bind_traceDist` (in
`Leslie.Prob.RandomisedAdversary`). -/
private lemma randomisedTraceDist_eq_integral_traceDist_traj_bind_eq
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    randomisedTraceDist spec R μ =
      Measure.bind (scheduleSpaceMeasure R) fun sched =>
        traceDist spec (sched.toAdversary R.corrupt) μ :=
  (randomisedTraceDist_eq_bind_traceDist spec R μ).2

set_option linter.unusedSectionVars false in
/-- Trajectory-level Fubini for the mixture trace measure: the
conjunction of AEMeasurability of the integrand (`-3a-i`) and the
bind equality (`-3a-ii`). Re-export of the framework lemma. -/
private theorem randomisedTraceDist_eq_integral_traceDist_traj
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    AEMeasurable
        (fun sched : ScheduleAssignment σ ι =>
          traceDist spec (sched.toAdversary R.corrupt) μ)
        (scheduleSpaceMeasure R)
      ∧ randomisedTraceDist spec R μ =
        Measure.bind (scheduleSpaceMeasure R) fun sched =>
          traceDist spec (sched.toAdversary R.corrupt) μ :=
  randomisedTraceDist_eq_bind_traceDist spec R μ

/-- **Fubini factorisation of the mixture trace measure** (the heart
of `Secrecy.toRandomised`).

The randomised mixture trace measure equals the *integral* of
deterministic trace measures over the schedule-space measure.

For our `Secrecy` use-case, the integrand `g` is the indicator of a
`Measure.map proj`-measurable set — Fubini moves the projection
outside the integral and leaves the deterministic equality to
discharge.

**Phase 11-β-followup-7 status.** This is now a one-liner forwarding
to the framework lemma `randomisedTraceDist_eq_bind_traceDist` in
`Leslie.Prob.RandomisedAdversary`. The conclusion bundles the bind
equality with an `AEMeasurable` witness for the inner family — both
are needed by `Secrecy.toRandomised` to push `Measure.map proj` past
the bind via `bind_apply`. -/
private theorem randomisedTraceDist_eq_integral_traceDist
    (spec : ProbActionSpec σ ι) (R : RandomisedAdversary σ ι)
    (μ : Measure σ) [IsProbabilityMeasure μ] :
    AEMeasurable
        (fun sched : ScheduleAssignment σ ι =>
          traceDist spec (sched.toAdversary R.corrupt) μ)
        (scheduleSpaceMeasure R)
      ∧ randomisedTraceDist spec R μ =
        Measure.bind (scheduleSpaceMeasure R) fun sched =>
          traceDist spec (sched.toAdversary R.corrupt) μ :=
  randomisedTraceDist_eq_bind_traceDist spec R μ

/-- **Hard direction** of the `Secrecy ↔ SecrecyRandomised`
correspondence: deterministic secrecy implies randomised secrecy.

Proof outline (Fubini over deterministic schedules).  Given
`R : RandomisedAdversary σ ι`, the randomised mixture trace measure
`randomisedTraceDist spec R μ` equals the integral, over the
schedule-space measure, of the deterministic trace measure for the
schedule sampled.  Applying `Secrecy` under the integral yields the
conclusion.

Concretely:
  * factor both sides via `randomisedTraceDist_eq_integral_traceDist`,
  * push `Measure.map proj` inside the bind by reducing to set-equality
    via `Measure.bind_apply` + `Measure.map_apply`,
  * apply the deterministic hypothesis `h sec sec' (sched.toAdversary R.corrupt)`
    pointwise inside the integral,
  * conclude by `lintegral_congr`.

The hypothesis `Measurable proj` (mirroring `mono_proj`) is necessary
to push `Measure.map proj` past the `Measure.bind`. It is satisfied in
all standard caller contexts: framework projections are typically
discrete (coalition views, schedule prefixes) where measurability is
automatic from `MeasurableSpace`-discreteness of the codomain. -/
theorem Secrecy.toRandomised
    {spec : ProbActionSpec σ ι}
    {Sec V : Type*} [MeasurableSpace V]
    {μ₀ : Sec → Measure σ} [∀ s, IsProbabilityMeasure (μ₀ s)]
    {proj : Trace σ ι → V} (hproj : Measurable proj)
    (h : Secrecy spec μ₀ proj) :
    SecrecyRandomised spec μ₀ proj := by
  intro sec sec' R
  -- Step 1: extract the factorisation + AEMeasurable witnesses for
  -- both secrets.
  obtain ⟨hAE_sec,  heq_sec⟩  :=
    randomisedTraceDist_eq_integral_traceDist spec R (μ₀ sec)
  obtain ⟨hAE_sec', heq_sec'⟩ :=
    randomisedTraceDist_eq_integral_traceDist spec R (μ₀ sec')
  -- Step 2: substitute the bind form into the goal.
  rw [heq_sec, heq_sec']
  -- Step 3: reduce to set-equality and unfold both `map` and `bind`.
  ext t ht
  have ht' : MeasurableSet (proj ⁻¹' t) := hproj ht
  rw [Measure.map_apply hproj ht, Measure.map_apply hproj ht,
      Measure.bind_apply ht' hAE_sec, Measure.bind_apply ht' hAE_sec']
  -- Step 4: pointwise equality under the integral via `h`.
  refine lintegral_congr fun sched => ?_
  -- For each fixed deterministic schedule, `h` gives the projected
  -- trace measures equal — apply at preimage `proj ⁻¹' t`.
  have hpoint :=
    congrArg (fun ν : Measure V => ν t)
      (h sec sec' (sched.toAdversary R.corrupt))
  -- `Measure.map_apply` on each side reduces `(traceDist ...).map proj t`
  -- to `traceDist ... (proj ⁻¹' t)`.
  simpa [Measure.map_apply hproj ht] using hpoint

end Leslie.Prob
