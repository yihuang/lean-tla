/-
M2 W2 — Probabilistic refinement.

Lifts Abadi–Lamport refinement to the probabilistic setting:
`Π ⊑ₚ Σ via proj` says that for every initial distribution and
adversary on `Π`, there exist matching ones on `Σ` such that
`Σ`'s trace measure projects (via `proj`) to `Π`'s trace measure.

This is the trace-level analogue of `Leslie.Refinement`'s
deterministic refinement, lifted to Mathlib `Measure`s under the
cylinder σ-algebra (per design plan v2.2 §"Composition combinators").

Status (M2 W3 polish — sorry-free):

  * `Refines Π Σ proj` — the refinement predicate, parameterized
    by a trace-level projection function.
  * `Refines.id` — every spec refines itself via the identity
    projection.
  * `Refines.comp` — composition of refinements (requires
    measurability of both projections to compose pushforwards
    via `Measure.map_map`).
  * `AlmostBox`, `AlmostDiamond` — modal predicates on
    `traceDist`.
  * `AlmostBox_of_pure_inductive` — deterministic-step bridge
    closing AE-always invariants for specs whose effects are all
    Dirac (`PMF.pure`). Body proved by countable-AE swap +
    coordinate induction using the joint-marginal lemma
    `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`.
  * `AlmostBox_of_inductive` — non-pure-effect generalisation: lifts
    an inductive predicate `P` along trajectories given preservation
    on the *support* of every gated action's effect distribution.
    Uses the same induction skeleton as the pure version, with the
    gate-pass branch handled via a small `pmf_ae_of_forall_support`
    helper instead of `ae_dirac_iff`.
  * `Refines_safe` — invariant lift along refinement: a safety
    property `φ` that holds Σ-AE under any abstract execution
    lifts to a Π-AE invariant via `ae_map_iff` on the pushforward.
    Requires measurability of `proj` and of `{s | φ s}`; both
    are satisfied for our discrete protocol settings.

Per implementation plan v2.2 §M2 W2 + M2 W3 polish. The real
`traceDist` body (M2 W1 polish + M2 W2 polish) is now a real
schedule-and-gate-conditional Markov-kernel measure; both
`Refines.comp` and `Refines_safe` are proved by composing it with
Mathlib's measure pushforward / AE machinery, and
`AlmostBox_of_pure_inductive` derives the per-coordinate marginal
recurrence from Mathlib's joint-marginal lemma.
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Trace

namespace Leslie.Prob

open MeasureTheory ProbabilityTheory

variable {σ σ' σ'' : Type*} {ι ι' ι'' : Type*}

/-! ## Trace-level projection

A trace projection translates an "abstract" trace
(`Trace σ' ι'`) to a "concrete" trace (`Trace σ ι`). For pure
state-translation refinements, this is `fun ω n => (f (ω n).1, ?)`
for some `f : σ' → σ`. For refinements that also collapse
stuttering steps, the projection is more involved. -/

/-- Identity trace projection (when source and target traces have
the same shape). -/
def Trace.idProj : Trace σ ι → Trace σ ι := id

/-- Composition of trace projections. -/
def Trace.compProj (g : Trace σ' ι' → Trace σ ι)
    (f : Trace σ'' ι'' → Trace σ' ι') :
    Trace σ'' ι'' → Trace σ ι :=
  g ∘ f

@[simp] theorem Trace.idProj_apply (ω : Trace σ ι) :
    Trace.idProj ω = ω := rfl

@[simp] theorem Trace.compProj_apply
    (g : Trace σ' ι' → Trace σ ι) (f : Trace σ'' ι'' → Trace σ' ι')
    (ω : Trace σ'' ι'') :
    Trace.compProj g f ω = g (f ω) := rfl

/-! ## Refinement -/

/-- Probabilistic refinement under a trace-level projection.

`Refines Π Σ proj` says: for every initial-state distribution `μ₀`
and adversary `A` on the concrete spec `Π`, there exist a matching
initial distribution `μ₀'` and adversary `A'` on the abstract
spec `Σ` such that `Σ`'s trace measure pushed through `proj`
equals `Π`'s trace measure.

This is the probabilistic Abadi–Lamport, parametric in `proj`
(typically a state-translation + stutter-collapse function).

For the special case where `Σ` and `Π` have the same trace shape,
use `Trace.idProj` for `proj`; this gives the simple "Π ⊑ Σ at
the same trace shape" relation (no refinement mapping). -/
def Refines
    [Countable σ] [Countable σ']
    [Countable ι] [Countable ι']
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace σ'] [MeasurableSingletonClass σ']
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace ι'] [MeasurableSingletonClass ι']
    (spec₁ : ProbActionSpec σ ι) (spec₂ : ProbActionSpec σ' ι')
    (proj : Trace σ' ι' → Trace σ ι) : Prop :=
  ∀ (μ₀ : Measure σ), IsProbabilityMeasure μ₀ →
    ∀ (A : Adversary σ ι),
      ∃ (μ₀' : Measure σ') (_ : IsProbabilityMeasure μ₀')
        (A' : Adversary σ' ι'),
        Measure.map proj (traceDist spec₂ A' μ₀') = traceDist spec₁ A μ₀

/-! ### Identity, composition

The structural lemmas: every spec refines itself via the identity
projection, and refinements compose. These hold without unfolding
`traceDist`. -/

/-- Every spec refines itself under the identity projection. -/
theorem Refines.id
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec₁ : ProbActionSpec σ ι) :
    Refines spec₁ spec₁ Trace.idProj := by
  intro μ₀ hμ₀ A
  refine ⟨μ₀, hμ₀, A, ?_⟩
  -- Goal: Measure.map Trace.idProj (traceDist spec₁ A μ₀) = traceDist spec₁ A μ₀
  -- Trace.idProj is the identity, so the map is identity.
  unfold Trace.idProj
  exact Measure.map_id

/-- Composition of refinements. If `Π ⊑ Σ` via `g` and `Σ ⊑ Τ` via
`f`, then `Π ⊑ Τ` via `g ∘ f`. -/
theorem Refines.comp
    [Countable σ] [Countable σ'] [Countable σ'']
    [Countable ι] [Countable ι'] [Countable ι'']
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace σ'] [MeasurableSingletonClass σ']
    [MeasurableSpace σ''] [MeasurableSingletonClass σ'']
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace ι'] [MeasurableSingletonClass ι']
    [MeasurableSpace ι''] [MeasurableSingletonClass ι'']
    {spec₁ : ProbActionSpec σ ι} {spec₂ : ProbActionSpec σ' ι'}
    {spec₃ : ProbActionSpec σ'' ι''}
    {g : Trace σ' ι' → Trace σ ι}
    {f : Trace σ'' ι'' → Trace σ' ι'}
    (h_g : Refines spec₁ spec₂ g) (h_f : Refines spec₂ spec₃ f)
    (h_g_meas : Measurable g) (h_f_meas : Measurable f) :
    Refines spec₁ spec₃ (Trace.compProj g f) := by
  intro μ₀ hμ₀ A
  -- From h_g: ∃ μ₀₂, A₂ such that map g (traceDist spec₂ A₂ μ₀₂) = traceDist spec₁ A μ₀
  obtain ⟨μ₀₂, hμ₀₂, A₂, h_eq_g⟩ := h_g μ₀ hμ₀ A
  -- From h_f: ∃ μ₀₃, A₃ such that map f (traceDist spec₃ A₃ μ₀₃) = traceDist spec₂ A₂ μ₀₂
  obtain ⟨μ₀₃, hμ₀₃, A₃, h_eq_f⟩ := h_f μ₀₂ hμ₀₂ A₂
  refine ⟨μ₀₃, hμ₀₃, A₃, ?_⟩
  -- Goal: map (g ∘ f) (traceDist spec₃ A₃ μ₀₃) = traceDist spec₁ A μ₀
  -- = map g (map f (traceDist spec₃ A₃ μ₀₃))   [by Measure.map_map]
  -- = map g (traceDist spec₂ A₂ μ₀₂)            [by h_eq_f]
  -- = traceDist spec₁ A μ₀                        [by h_eq_g]
  show Measure.map (Trace.compProj g f) (traceDist spec₃ A₃ μ₀₃) = traceDist spec₁ A μ₀
  rw [show Trace.compProj g f = g ∘ f from rfl,
      ← Measure.map_map h_g_meas h_f_meas, h_eq_f, h_eq_g]

/-! ### Modal predicates on `traceDist`

Probabilistic analogues of `□` and `◇` against a `traceDist`. -/

/-- Almost-surely-always: `φ` holds at every step of the trace. -/
def AlmostBox
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec₁ : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(traceDist spec₁ A μ₀), ∀ n, φ ((ω n).1)

/-- Almost-surely-eventually: there exists a step at which `φ`
holds, almost surely. -/
def AlmostDiamond
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (spec₁ : ProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (φ : σ → Prop) : Prop :=
  ∀ᵐ ω ∂(traceDist spec₁ A μ₀), ∃ n, φ ((ω n).1)

/-! ### `AlmostBox_of_pure_inductive` — deterministic-step bridge

When every action's effect is a Dirac (`PMF.pure (det_step i s)`), the
`stepKernel` collapses to a deterministic kernel: in the `none`-schedule
branch and the gate-fail branch it is already a Dirac (stutter), and in
the gate-pass branch the `PMF.pure` measure is also a Dirac. With a
deterministic-everywhere kernel, an inductive predicate `P` that is
preserved by the deterministic step transfers from the initial measure
to every coordinate of the trace, hence `AlmostBox` holds.

**M2 W3 polish status — closed.** The proof derives the per-coordinate
marginal recurrence directly from Mathlib's joint-marginal lemma
`map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` by taking
`.snd` on both sides (turning a `compProd` into a `Measure.bind`).
Combined with `MeasureTheory.ae_all_iff` for the countable-AE swap and
`PMF.toMeasure_pure` for the Dirac form of the gate-pass branch, the
inductive transport from coordinate `a` to coordinate `a + 1` reduces
to a `filter_upwards`-style argument over the four kernel branches.

Mathlib lemmas used:
  * `MeasureTheory.ae_all_iff` — countable-AE swap.
  * `MeasureTheory.ae_map_iff` — pull AE through a pushforward.
  * `MeasureTheory.Measure.ae_comp_of_ae_ae` — AE through a kernel
    composition `κ ∘ₘ μ`.
  * `MeasureTheory.ae_dirac_iff` — AE on a Dirac.
  * `PMF.toMeasure_pure` — `(PMF.pure x).toMeasure = Measure.dirac x`.
  * `ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
    — joint marginal of `Kernel.trajMeasure` over `(frestrictLe a, eval (a+1))`.
  * `MeasureTheory.Measure.snd_compProd` — `(μ ⊗ₘ κ).snd = κ ∘ₘ μ`.
  * `MeasureTheory.Measure.snd_map_prodMk` — `.snd` of a paired pushforward.
  * `ProbabilityTheory.Kernel.traj_map_frestrictLe_of_le` (and
    `Kernel.deterministic_map`, `Measure.deterministic_comp_eq_map`)
    — to pin down the coordinate-`0` marginal as `μ₀_full`. -/

/-- When all effects are Dirac on a deterministic step function and
the deterministic step preserves an inductive predicate `P`, the
predicate holds AE-always on the trace measure.

The proof proceeds by countable-AE swap, then induction on the
coordinate `n`:

  * Base `n = 0`: the `0`-th marginal of `Kernel.trajMeasure μ₀_full κ`
    is `μ₀_full = μ₀.map (·, none)`, so AE-`P` on `μ₀` transports.
  * Step `n + 1`: the `(a + 1)`-th marginal equals
    `(stepKernel spec A a) ∘ₘ ((trajMeasure ..).map (frestrictLe a))`
    (snd of the joint marginal). Under `h_pure`, every per-history
    branch of `stepKernel a h` is a Dirac, so AE-`P` at coordinate
    `a + 1` reduces to `P (h.currentState)` plus `h_step`. -/
theorem AlmostBox_of_pure_inductive
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (P : σ → Prop)
    (det_step : ι → σ → σ)
    (h_pure : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        (spec.actions i).effect s h = PMF.pure (det_step i s))
    (h_step : ∀ (i : ι) (s : σ),
        (spec.actions i).gate s → P s → P (det_step i s))
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, P s)
    (A : Adversary σ ι) :
    AlmostBox spec A μ₀ P := by
  -- Predicate measurability: under `Countable + MeasurableSingletonClass`,
  -- every set is measurable.
  have hPset : MeasurableSet ({x : σ × Option ι | P x.1}) := MeasurableSet.of_discrete
  have hPset_finPrefix : ∀ a : ℕ,
      MeasurableSet {h : FinPrefix σ ι a | P (FinPrefix.currentState h)} :=
    fun _ => MeasurableSet.of_discrete
  -- Unfold to expose the underlying `Kernel.trajMeasure`.
  unfold AlmostBox traceDist
  set μ₀_full : Measure (σ × Option ι) := μ₀.map (fun s => (s, (none : Option ι)))
    with hμ₀_full_def
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- Marginal at coordinate 0: `(trajMeasure μ₀_full κ).map (eval 0) = μ₀_full`.
  -- The `0`-th coordinate of `Kernel.trajMeasure` is the initial measure, since
  -- `traj κ 0` is concentrated on the `Iic 0`-prefix at the input.
  have hmarg_zero :
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)).map
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
  -- Marginal recurrence at successor: `(trajMeasure ..).map (eval (a+1)) =
  -- (stepKernel a) ∘ₘ (trajMeasure ..).map (frestrictLe a)`.
  -- Derived from the joint marginal lemma by taking `.snd` of both sides.
  have hmarg_succ : ∀ a : ℕ,
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)).map
        (fun ω => ω (a + 1)) =
      (stepKernel spec A a) ∘ₘ
        ((Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)) := by
    intro a
    have hk : (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
              (stepKernel spec A)).map (Preorder.frestrictLe a) ⊗ₘ stepKernel spec A a =
        (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)).map
          (fun x => (Preorder.frestrictLe a x, x (a + 1))) :=
      ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h2 := congrArg Measure.snd hk
    rw [Measure.snd_compProd] at h2
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    rw [Measure.snd_map_prodMk hmeas_fl_a] at h2
    exact h2.symm
  -- Countable-AE swap: prove `∀ n, ∀ᵐ ω, P (ω n).1` instead.
  rw [MeasureTheory.ae_all_iff]
  intro n
  -- Induction on `n`.
  induction n with
  | zero =>
    -- Transport `h_init` along `μ₀_full`'s definition, then through `hmarg_zero`.
    have hae_full : ∀ᵐ x ∂μ₀_full, P x.1 := by
      rw [hμ₀_full_def, ae_map_iff (Measurable.aemeasurable (by fun_prop)) hPset]
      exact h_init
    rw [← hmarg_zero] at hae_full
    have hmeas_eval0 : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
      measurable_pi_apply 0
    rw [ae_map_iff hmeas_eval0.aemeasurable hPset] at hae_full
    exact hae_full
  | succ a ih =>
    -- IH `ih : ∀ᵐ ω, P (ω a).1`.
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    have hmeas_eval_succ : Measurable (fun ω : Π _ : ℕ, σ × Option ι => ω (a + 1)) :=
      measurable_pi_apply (a + 1)
    -- Transport IH along `frestrictLe a`: `∀ᵐ h, P h.currentState`.
    have hcurrent : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)),
          P (FinPrefix.currentState h) := by
      rw [ae_map_iff hmeas_fl_a.aemeasurable (hPset_finPrefix a)]
      filter_upwards [ih] with ω hω
      exact hω
    -- Bridge: `∀ᵐ h, ∀ᵐ y ∂(stepKernel a h), P y.1`.
    -- Under `h_pure`, every kernel branch is a Dirac (stutter or `det_step`).
    have hkernel_ae : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)),
          ∀ᵐ y ∂(stepKernel spec A a h), P y.1 := by
      filter_upwards [hcurrent] with h hPcurr
      show ∀ᵐ y ∂(stepKernel spec A a h), P y.1
      unfold stepKernel
      rw [Kernel.ofFunOfCountable]
      simp only [Kernel.coe_mk]
      rcases h_sched : A.schedule h.toList with _ | i
      · -- Stutter case: `Dirac (h.currentState, none)`.
        rw [ae_dirac_iff hPset]
        exact hPcurr
      · by_cases hgate : (spec.actions i).gate h.currentState
        · -- Gate-pass case: `(PMF.pure (det_step i ..)).toMeasure.map (·, some i)`.
          simp only [hgate, dite_true]
          rw [h_pure i h.currentState hgate, PMF.toMeasure_pure,
              Measure.map_dirac (by fun_prop)]
          rw [ae_dirac_iff hPset]
          exact h_step i h.currentState hgate hPcurr
        · -- Gate-fail case: stutter again.
          simp only [hgate, dite_false]
          rw [ae_dirac_iff hPset]
          exact hPcurr
    -- Combine via `ae_comp_of_ae_ae` and the marginal recurrence.
    have hae_succ : ∀ᵐ y ∂((stepKernel spec A a) ∘ₘ
          (Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)),
        P y.1 :=
      Measure.ae_comp_of_ae_ae hPset hkernel_ae
    rw [← hmarg_succ a] at hae_succ
    rw [ae_map_iff hmeas_eval_succ.aemeasurable hPset] at hae_succ
    exact hae_succ

/-! ### `AlmostBox_of_inductive` — non-pure-effect inductive bridge

Generalises `AlmostBox_of_pure_inductive` to arbitrary `PMF` effects:
instead of requiring every action's effect to be a Dirac, we require
that an inductive predicate `P` is preserved on the *support* of the
effect distribution. This is the form needed by
`FairASTCertificate.pi_infty_zero_fair` (where `P` is the
certificate's `Inv`).

Proof structure mirrors `AlmostBox_of_pure_inductive` exactly: the
only divergence is in the gate-pass branch of the per-step kernel,
where we use `PMF.toMeasure_apply_eq_zero_iff` (via a small support-
AE helper `pmf_ae_of_forall_support`) instead of `PMF.toMeasure_pure`
+ `ae_dirac_iff`. -/

/-- Helper: if `P` holds on the support of a PMF, then `P` holds
AE on its `toMeasure`. -/
private theorem pmf_ae_of_forall_support
    {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (P : α → Prop) (hP : ∀ x ∈ p.support, P x) :
    ∀ᵐ x ∂p.toMeasure, P x := by
  rw [ae_iff]
  have hms : MeasurableSet {a : α | ¬ P a} := MeasurableSet.of_discrete
  rw [PMF.toMeasure_apply_eq_zero_iff _ hms, Set.disjoint_left]
  intro x hxsup hxnot
  exact hxnot (hP x hxsup)

/-- Inductive `P` is preserved AE-along-trajectory under any spec
and adversary, given `P` is preserved on the support of every gated
action's effect distribution.

This is the non-pure-effect generalisation of
`AlmostBox_of_pure_inductive`. The proof structure is identical;
the only change is in the gate-pass kernel branch, where we use
`pmf_ae_of_forall_support` instead of `PMF.toMeasure_pure` +
`ae_dirac_iff`. -/
theorem AlmostBox_of_inductive
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (P : σ → Prop)
    (h_step : ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        P s → ∀ s' ∈ ((spec.actions i).effect s h).support, P s')
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, P s)
    (A : Adversary σ ι) :
    AlmostBox spec A μ₀ P := by
  -- Predicate measurability via `Countable + MeasurableSingletonClass`.
  have hPset : MeasurableSet ({x : σ × Option ι | P x.1}) := MeasurableSet.of_discrete
  have hPset_finPrefix : ∀ a : ℕ,
      MeasurableSet {h : FinPrefix σ ι a | P (FinPrefix.currentState h)} :=
    fun _ => MeasurableSet.of_discrete
  have hPset_state : MeasurableSet {s : σ | P s} := MeasurableSet.of_discrete
  unfold AlmostBox traceDist
  set μ₀_full : Measure (σ × Option ι) := μ₀.map (fun s => (s, (none : Option ι)))
    with hμ₀_full_def
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- Marginal at coordinate 0 (same proof as in the pure version).
  have hmarg_zero :
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)).map
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
  -- Marginal recurrence at successor.
  have hmarg_succ : ∀ a : ℕ,
      (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)).map
        (fun ω => ω (a + 1)) =
      (stepKernel spec A a) ∘ₘ
        ((Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)) := by
    intro a
    have hk : (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full
              (stepKernel spec A)).map (Preorder.frestrictLe a) ⊗ₘ stepKernel spec A a =
        (Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)).map
          (fun x => (Preorder.frestrictLe a x, x (a + 1))) :=
      ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h2 := congrArg Measure.snd hk
    rw [Measure.snd_compProd] at h2
    have hmeas_fl_a : Measurable
        (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) a) :=
      Preorder.measurable_frestrictLe _
    rw [Measure.snd_map_prodMk hmeas_fl_a] at h2
    exact h2.symm
  rw [MeasureTheory.ae_all_iff]
  intro n
  induction n with
  | zero =>
    have hae_full : ∀ᵐ x ∂μ₀_full, P x.1 := by
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
    have hcurrent : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)),
          P (FinPrefix.currentState h) := by
      rw [ae_map_iff hmeas_fl_a.aemeasurable (hPset_finPrefix a)]
      filter_upwards [ih] with ω hω
      exact hω
    have hkernel_ae : ∀ᵐ h ∂((Kernel.trajMeasure (X := fun _ => σ × Option ι)
          μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)),
          ∀ᵐ y ∂(stepKernel spec A a h), P y.1 := by
      filter_upwards [hcurrent] with h hPcurr
      show ∀ᵐ y ∂(stepKernel spec A a h), P y.1
      unfold stepKernel
      rw [Kernel.ofFunOfCountable]
      simp only [Kernel.coe_mk]
      rcases h_sched : A.schedule h.toList with _ | i
      · -- Stutter (no schedule): Dirac at current state.
        rw [ae_dirac_iff hPset]
        exact hPcurr
      · by_cases hgate : (spec.actions i).gate h.currentState
        · -- Gate-pass: pushforward of `(spec.actions i).effect`'s PMF measure.
          simp only [hgate, dite_true]
          rw [ae_map_iff (by fun_prop) hPset]
          -- Reduce to `∀ᵐ s ∂(effect ..).toMeasure, P s` via the support-AE helper.
          exact pmf_ae_of_forall_support _ (fun s => P s)
            (fun s' hs' => h_step i h.currentState hgate hPcurr s' hs')
        · -- Gate-fail: stutter.
          simp only [hgate, dite_false]
          rw [ae_dirac_iff hPset]
          exact hPcurr
    have hae_succ : ∀ᵐ y ∂((stepKernel spec A a) ∘ₘ
          (Kernel.trajMeasure (X := fun _ => σ × Option ι)
            μ₀_full (stepKernel spec A)).map (Preorder.frestrictLe a)),
        P y.1 :=
      Measure.ae_comp_of_ae_ae hPset hkernel_ae
    rw [← hmarg_succ a] at hae_succ
    rw [ae_map_iff hmeas_eval_succ.aemeasurable hPset] at hae_succ
    exact hae_succ

/-! ### `traceDist_kernel_step_bound` — kernel-step lower bound

Specialises the disintegration identity
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
(used in `AlmostBox_of_inductive`) to a per-step kernel-conditional
probability bound. Used by the chain-of-conditional-probabilities
closure of `pi_n_AST_fair_with_progress` (Liveness.lean).

Statement: if a "good history" set `S ⊆ FinPrefix σ ι n` puts each
prefix in a state where the per-step kernel `stepKernel spec A n`
puts mass ≥ `p` on a successor event `T h` (parameterised by the
history `h`), then the joint trajectory measure satisfies

  `p · (traceDist) {ω | frestrictLe n ω ∈ S} ≤
   (traceDist) {ω | frestrictLe n ω ∈ S ∧ ω (n+1) ∈ T (frestrictLe n ω)}`.

This is the "general cylinder" form: `T h` may depend on the history
`h`, allowing the successor event to be defined by a predicate on
`(history, next-state)` pairs (e.g., "U decreased at step n+1
relative to the current state"). The chain argument in
`pi_n_AST_fair_with_progress` consumes this lemma at each step `k`
to relate `μ(C_{k+1}) ≤ (1-p) μ(C_k)`. -/

/-- Kernel-step lower bound for `traceDist`: if every history in `S`
gives the per-step kernel `stepKernel spec A n` mass `≥ p` on the
history-indexed successor event `T h`, then the joint trajectory
measure on `{ω | frestrictLe n ω ∈ S ∧ ω (n+1) ∈ T (frestrictLe n ω)}`
is at least `p` times the trajectory measure on `{ω | frestrictLe n ω ∈ S}`.

Proved via the joint-marginal identity
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`,
`Measure.compProd_apply`, and `setLIntegral_mono'` for the
constant-lower-bound integral. -/
theorem traceDist_kernel_step_bound
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (n : ℕ)
    (S : Set (FinPrefix σ ι n))
    (T : FinPrefix σ ι n → Set (σ × Option ι))
    (p : ENNReal)
    (h_step : ∀ h ∈ S, p ≤ (stepKernel spec A n h) (T h)) :
    p * (traceDist spec A μ₀)
        {ω : Trace σ ι | Preorder.frestrictLe n ω ∈ S} ≤
      (traceDist spec A μ₀)
        {ω : Trace σ ι | Preorder.frestrictLe n ω ∈ S ∧
          ω (n + 1) ∈ T (Preorder.frestrictLe n ω)} := by
  classical
  have hSset : MeasurableSet S := MeasurableSet.of_discrete
  set μ₀_full : Measure (σ × Option ι) := μ₀.map (fun s => (s, (none : Option ι)))
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  set μtraj := Kernel.trajMeasure (X := fun _ => σ × Option ι) μ₀_full (stepKernel spec A)
  set ν : Measure (FinPrefix σ ι n) := μtraj.map (Preorder.frestrictLe n)
  -- Joint marginal at (frestrictLe n, eval (n+1)) factors as ν ⊗ₘ stepKernel.
  have hjoint_eq :
      ν ⊗ₘ (stepKernel spec A n) =
        μtraj.map (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hmeas_pair : Measurable (fun ω : Π _ : ℕ, σ × Option ι =>
      (Preorder.frestrictLe (π := fun _ : ℕ => σ × Option ι) n ω, ω (n + 1))) := by
    fun_prop
  -- Pull events back as preimages of joint cylinders.
  set ES : Set (Trace σ ι) := {ω | Preorder.frestrictLe n ω ∈ S}
  set EJ : Set (Trace σ ι) := {ω | Preorder.frestrictLe n ω ∈ S ∧
      ω (n + 1) ∈ T (Preorder.frestrictLe n ω)}
  set CylS : Set (FinPrefix σ ι n × (σ × Option ι)) := S ×ˢ Set.univ
  set Joint : Set (FinPrefix σ ι n × (σ × Option ι)) :=
    {x | x.1 ∈ S ∧ x.2 ∈ T x.1}
  have hCylS_meas : MeasurableSet CylS := hSset.prod MeasurableSet.univ
  have hJoint_meas : MeasurableSet Joint := MeasurableSet.of_discrete
  have hES_eq : ES = (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹' CylS := by
    ext ω; simp [ES, CylS]
  have hEJ_eq : EJ = (fun ω => (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹' Joint := by
    ext ω; simp [EJ, Joint]
  show p * μtraj ES ≤ μtraj EJ
  rw [hES_eq, hEJ_eq]
  rw [← Measure.map_apply hmeas_pair hCylS_meas,
      ← Measure.map_apply hmeas_pair hJoint_meas]
  rw [← hjoint_eq]
  -- Evaluate compProd via `Measure.compProd_apply` (using preimages of cylinders).
  rw [Measure.compProd_apply hCylS_meas, Measure.compProd_apply hJoint_meas]
  -- Inner integrals: collapse via `Prod.mk h ⁻¹' (S ×ˢ univ) = univ` on S, `∅` off S;
  -- and `Prod.mk h ⁻¹' Joint = T h` on S, `∅` off S.
  have hint_S : (∫⁻ h, (stepKernel spec A n h) (Prod.mk h ⁻¹' CylS) ∂ν) = ν S := by
    have heq : (fun h => (stepKernel spec A n h) (Prod.mk h ⁻¹' CylS)) =
        S.indicator 1 := by
      funext h
      by_cases hh : h ∈ S
      · have hpre : Prod.mk h ⁻¹' CylS = Set.univ := by
          ext y; simp [CylS, hh]
        rw [hpre, Set.indicator_of_mem hh]
        show (stepKernel spec A n h) Set.univ = _
        simp [measure_univ]
      · have hpre : Prod.mk h ⁻¹' CylS = ∅ := by
          ext y; simp [CylS, hh]
        rw [hpre, Set.indicator_of_notMem hh]
        simp
    rw [heq, MeasureTheory.lintegral_indicator_one hSset]
  have hint_J : (∫⁻ h, (stepKernel spec A n h) (Prod.mk h ⁻¹' Joint) ∂ν) =
      ∫⁻ h in S, (stepKernel spec A n h) (T h) ∂ν := by
    rw [← MeasureTheory.lintegral_indicator hSset]
    congr 1; funext h
    by_cases hh : h ∈ S
    · have hpre : Prod.mk h ⁻¹' Joint = T h := by
        ext y; simp [Joint, hh]
      rw [hpre, Set.indicator_of_mem hh]
    · have hpre : Prod.mk h ⁻¹' Joint = ∅ := by
        ext y; simp [Joint, hh]
      rw [hpre, Set.indicator_of_notMem hh]
      simp
  rw [hint_S, hint_J]
  -- Constant-lower-bound integral: ∫⁻ _ in S, p ∂ν = p * ν S ≤ ∫⁻ h in S, kernel.h(T h) ∂ν.
  have h_const : (∫⁻ _ in S, (p : ENNReal) ∂ν) ≤
      ∫⁻ h in S, (stepKernel spec A n h) (T h) ∂ν :=
    MeasureTheory.setLIntegral_mono' hSset h_step
  rw [MeasureTheory.setLIntegral_const] at h_const
  exact h_const

/-! ### Stopping-time kernel lower bound

A "for-every-fixed-m" packaging of `traceDist_kernel_step_bound`.
Given a per-fiber prefix set family `S : (m : ℕ) → Set (FinPrefix σ ι m)`
and a per-fiber target family `T : (m : ℕ) → FinPrefix σ ι m → Set (σ × Option ι)`,
plus a uniform per-step kernel lower bound `p`, the trace measure
satisfies the per-`m` kernel bound at every step.

This is the input to fiber-sum reductions (see
`Leslie.Prob.FairASTCertificate.measure_selector_fiber_lower_bound`
and `traceDist_selector_fiber_lower_bound` in `Liveness.lean`)
which sum over a measurable stopping time `τ : Trace σ ι → ℕ` to
obtain the conditional-form lower bound used in the Borel-Cantelli
proof of general fair AST.

Concretely, callers wanting a stopping-time-form bound can:

1. Use this lemma per-`m` to populate `traceDist_selector_fiber_lower_bound`'s
   `h_step` hypothesis (intersecting with the τ-fiber `{τ = m}` as needed).
2. Sum across `m` via the fiber-sum lemma.

The mechanical form is just iterating `traceDist_kernel_step_bound` —
this lemma is exposed as a named convenience so downstream
Borel-Cantelli code doesn't have to re-derive the per-fiber bound at
each call site. -/

/-- **Stopping-time kernel lower bound (per-fiber form).**

For each step index `m`, the trace-measure kernel-disintegration bound
applies: assuming `p ≤ (stepKernel spec A m h)(T m h)` for every
prefix `h ∈ S m`, the joint event "prefix in `S m` and the next
coordinate falls in `T m`" has at least `p`-fraction of the
prefix-in-`S m` mass.

This is the "fiber" input to summation arguments used in the
Borel-Cantelli proof of general fair AST. The fiber-sum lemma
in `Liveness.lean` (`measure_selector_fiber_lower_bound`) takes
these per-fiber bounds and produces a stopping-time-conditional
lower bound on the union over fibers `{τ = m}`. -/
theorem traceDist_kernel_stoppingTime_bound
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (S : (m : ℕ) → Set (FinPrefix σ ι m))
    (T : (m : ℕ) → FinPrefix σ ι m → Set (σ × Option ι))
    (p : ENNReal)
    (h_step : ∀ m, ∀ h ∈ S m, p ≤ (stepKernel spec A m h) (T m h))
    (m : ℕ) :
    p * (traceDist spec A μ₀)
        {ω : Trace σ ι | Preorder.frestrictLe m ω ∈ S m} ≤
      (traceDist spec A μ₀)
        {ω : Trace σ ι | Preorder.frestrictLe m ω ∈ S m ∧
          ω (m + 1) ∈ T m (Preorder.frestrictLe m ω)} :=
  traceDist_kernel_step_bound A μ₀ m (S m) (T m) p (h_step m)

/-! ### Refines_safe

If `Π` refines `Σ` (via `proj`) and `φ` holds always for `Σ`'s
trace (under projected predicates), then `φ` holds always for
`Π`'s trace.

Proof: extract the `Refines` witness `(μ₀', A')`, instantiate the
`AlmostBox`-on-Σ hypothesis there, then use `ae_map_iff` to push
the AE-event back through `Measure.map proj`. The state-component
identity `h_proj_state` lets us turn `φ ((proj ω) n).1` into
`(φ ∘ state_proj) ((ω n).1)`, which is exactly the Σ-side
hypothesis at index `n`.

The hypothesis is universally quantified over `(μ₀', A')` (with
`[IsProbabilityMeasure μ₀']` carried as an instance). This is
strictly stronger than the existential form but matches the
"safety holds for *every* abstract execution" reading and lets
us instantiate at the witness produced by `Refines`. -/

/-- Invariant `φ` on the abstract spec lifts (via projection) to
an invariant on the concrete spec. Requires measurability of
`proj` and of the predicate set; both are satisfied for our
discrete protocol settings. -/
theorem Refines_safe
    [Countable σ] [Countable σ']
    [Countable ι] [Countable ι']
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace σ'] [MeasurableSingletonClass σ']
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace ι'] [MeasurableSingletonClass ι']
    {spec₁ : ProbActionSpec σ ι} {spec₂ : ProbActionSpec σ' ι'}
    {proj : Trace σ' ι' → Trace σ ι}
    (h_ref : Refines spec₁ spec₂ proj)
    (h_proj_meas : Measurable proj)
    (state_proj : σ' → σ)
    (h_proj_state : ∀ (ω : Trace σ' ι') n, ((proj ω) n).1 = state_proj ((ω n).1))
    (φ : σ → Prop) (h_phi_meas : MeasurableSet {s : σ | φ s})
    (μ₀ : Measure σ) [hμ₀ : IsProbabilityMeasure μ₀]
    (A : Adversary σ ι)
    (h_box : ∀ (μ₀' : Measure σ') [IsProbabilityMeasure μ₀']
        (A' : Adversary σ' ι'),
        AlmostBox spec₂ A' μ₀' (φ ∘ state_proj)) :
    AlmostBox spec₁ A μ₀ φ := by
  obtain ⟨μ₀', hμ₀', A', h_eq⟩ := h_ref μ₀ hμ₀ A
  haveI : IsProbabilityMeasure μ₀' := hμ₀'
  have hbox' := h_box μ₀' A'
  -- Reduce to AE on the pushforward `Measure.map proj _`.
  unfold AlmostBox at hbox' ⊢
  rw [← h_eq]
  -- The predicate set `{ω | ∀ n, φ (ω n).1}` is measurable as a
  -- countable intersection of preimages of `{s | φ s}`.
  have h_pred : MeasurableSet {ω : Trace σ ι | ∀ n, φ (ω n).1} := by
    have heq : {ω : Trace σ ι | ∀ n, φ (ω n).1} = ⋂ n, {ω | φ (ω n).1} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iInter fun n =>
      (measurable_fst.comp (measurable_pi_apply n)) h_phi_meas
  rw [ae_map_iff h_proj_meas.aemeasurable h_pred]
  filter_upwards [hbox'] with ω' h_ae n
  rw [h_proj_state ω' n]
  exact h_ae n

/-! ## `AlmostDiamond_of_leads_to`

Liveness analogue of `Refines_safe`: an `AlmostDiamond` "leads-to"
bridge. If on AE traces, the eventual occurrence of `P` implies the
eventual occurrence of `Q`, then `AlmostDiamond P` implies
`AlmostDiamond Q`.

Used by protocol-specific liveness proofs (e.g.,
`BrachaRBC.brbProb_totality_AS_fair`) to lift deterministic leads-to
properties (`P ↝ Q` under fairness, in the upstream Leslie TLA
sense) to the probabilistic-trace setting. The deterministic
leads-to becomes the AE per-trace implication hypothesis. -/

/-- `AlmostDiamond` is preserved under AE-pointwise eventual
implication.

This is the trace-level liveness counterpart of `Refines_safe`'s
invariant lift. The hypothesis `h_lt` packages "deterministic
leads-to" at the per-trace level: AE on the trace measure, if
`P` ever holds on the trajectory, then `Q` eventually holds too.

Concrete protocols supply `h_lt` either by porting upstream
deterministic `pred_implies … ↝ …` lemmas to the trajectory side,
or by direct trace-level reasoning. -/
theorem AlmostDiamond_of_leads_to
    [Countable σ] [Countable ι]
    [MeasurableSpace σ] [MeasurableSingletonClass σ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {spec : ProbActionSpec σ ι}
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : Adversary σ ι)
    {P Q : σ → Prop}
    (h_lt : ∀ᵐ ω ∂(traceDist spec A μ₀),
      (∃ n, P ((ω n).1)) → ∃ m, Q ((ω m).1))
    (h_P : AlmostDiamond spec A μ₀ P) :
    AlmostDiamond spec A μ₀ Q := by
  unfold AlmostDiamond at h_P ⊢
  filter_upwards [h_lt, h_P] with ω h_lt_ω h_P_ω
  exact h_lt_ω h_P_ω

end Leslie.Prob
