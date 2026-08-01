/-
M3 Phase 10.1 — `DeterministicProbActionSpec` and the generic
`simulate*` machinery.

A *deterministic* probabilistic spec is one whose every per-step
effect is `PMF.pure (step a s)`: all randomness lives in `μ₀`
(the initial measure).  AVSS, BrachaRBC, SyncVSS, and AVSSAbstract
all fit this pattern.  Common-coin / random-oracle protocols do not.

Phase 10's plan (`AVSS-MODEL-NOTES.md` §14) promotes the inductive
AE-bridge from `AVSS.lean` §19.2 to a meta-theorem; this file is the
data foundation:

  * `DeterministicProbActionSpec` — the deterministic spec record.
  * `toProbActionSpec` — the adapter wrapping each step in `PMF.pure`.
  * `simulateNext` / `simulateRev` / `simulateTrace` — the generic
    deterministic simulation, taking a plain `Adversary σ ι` and
    reading only `D.gate`, `D.step`, and `A.schedule`.

Plus the structural simp lemmas (`_length`, `_ne_nil`, `_succ_eq`,
`_head_eq`, `_zero`) that PR 10.2 will use to prove the AE-bridge.

The shape mirrors the existing AVSS-specific definitions in
`AVSS.lean` §19.2 (`avssSimulateNext`, `avssSimulateRev`,
`avssSimulateTrace`); PR 10.3 will collapse those to one-line
instantiations of the generic versions.

No `traceDist` reasoning here — that's PR 10.2.  No measurability
typeclasses — they are imposed only at `Trace.traceDist` call sites
(matching `Action.lean` and `Adversary.lean`).
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Trace

namespace Leslie.Prob

/-! ## DeterministicProbActionSpec -/

/-- A deterministic state-machine spec: every action's effect is
`PMF.pure (step a s)`.  Strict subclass of `ProbActionSpec` covering
all protocols whose only randomness lives in `μ₀`.

Mirrors `ProbActionSpec` minus the per-action `PMF` — the generic
`toProbActionSpec` adapter wraps each `step a s` in `PMF.pure`. -/
structure DeterministicProbActionSpec (σ : Type*) (ι : Type*) where
  /-- Initial-state predicate (inherited verbatim by `toProbActionSpec`). -/
  init : σ → Prop
  /-- Per-action gate, mirroring `ProbGatedAction.gate`. -/
  gate : ι → σ → Prop
  /-- Per-action deterministic next-state.  `toProbActionSpec` lifts this
  to `PMF.pure (step a s)`. -/
  step : ι → σ → σ

namespace DeterministicProbActionSpec

variable {σ ι : Type*}

/-! ### Adapter to `ProbActionSpec`

Wrap each deterministic `step` in `PMF.pure` to obtain a
`ProbActionSpec`.  Three definitional simp lemmas expose the
projections so downstream proofs can rewrite freely. -/

/-- Lift a deterministic spec to a `ProbActionSpec` by wrapping each
step in `PMF.pure`. -/
noncomputable def toProbActionSpec (D : DeterministicProbActionSpec σ ι) :
    ProbActionSpec σ ι where
  init    := D.init
  actions := fun a =>
    { gate   := D.gate a
      effect := fun s _ => PMF.pure (D.step a s) }

@[simp] theorem toProbActionSpec_init (D : DeterministicProbActionSpec σ ι) :
    D.toProbActionSpec.init = D.init := rfl

@[simp] theorem toProbActionSpec_actions_gate
    (D : DeterministicProbActionSpec σ ι) (a : ι) (s : σ) :
    (D.toProbActionSpec.actions a).gate s = D.gate a s := rfl

@[simp] theorem toProbActionSpec_actions_effect
    (D : DeterministicProbActionSpec σ ι) (a : ι) (s : σ)
    (h : D.gate a s) :
    (D.toProbActionSpec.actions a).effect s h = PMF.pure (D.step a s) := rfl

end DeterministicProbActionSpec

/-! ## Generic deterministic simulation

Mirrors `AVSS.lean` §19.2's `avssSimulateNext` / `avssSimulateRev` /
`avssSimulateTrace` but reads only the deterministic spec's `gate`
and `step`, and the plain `Adversary.schedule`.  PR 10.3 will rewrite
the AVSS-specific versions as one-line wrappers of these. -/

section Simulate

open Classical

variable {σ ι : Type*}

/-- One step of the deterministic simulation, given the previous
reverse-order prefix.  If the prefix's head fires the schedule's
chosen action and that action's gate holds, apply `D.step`; otherwise
stutter at the current state.

The `fallback` argument plugs the unreachable `prev = []` case for
Lean totality; under the `simulateRev` recursion below the prefix is
always non-empty (`simulateRev_ne_nil`). -/
noncomputable def simulateNext
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (fallback : σ) (prev : List (σ × Option ι)) : σ × Option ι :=
  let s_k : σ := (prev.head?.map Prod.fst).getD fallback
  match A.schedule prev.reverse with
  | none   => (s_k, (none : Option ι))
  | some i =>
      if D.gate i s_k then (D.step i s_k, some i)
      else (s_k, (none : Option ι))

/-- Reverse-order simulated trace prefix at step `k`.  Returns a list
of length `k+1` ordered as `[step k, step k-1, …, step 0]`. -/
noncomputable def simulateRev
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) : ℕ → List (σ × Option ι)
  | 0     => [(s_0, (none : Option ι))]
  | (k+1) =>
    let prev := simulateRev D A s_0 k
    simulateNext D A s_0 prev :: prev

/-- The simulated trace at step `k`: extract the head of the
reverse-order prefix list. -/
noncomputable def simulateTrace
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) : σ × Option ι :=
  match simulateRev D A s_0 k with
  | []     => (s_0, (none : Option ι))  -- unreachable; see `simulateRev_ne_nil`
  | x :: _ => x

/-! ### Structural simp lemmas

These mirror the AVSS-specific lemmas (`avssSimulateRev_length`,
`avssSimulateRev_ne_nil`, `avssSimulateTrace_zero`,
`avssSimulateTrace_succ_eq`, `avssSimulateRev_head_eq`) in
`AVSS.lean` §19.2.  Proofs are by definitional reduction or short
induction on `k`. -/

theorem simulateRev_length
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    (simulateRev D A s_0 k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [simulateRev, ih]

theorem simulateRev_ne_nil
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    simulateRev D A s_0 k ≠ [] := by
  intro h
  have := simulateRev_length D A s_0 k
  rw [h] at this; simp at this

theorem simulateRev_succ
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    simulateRev D A s_0 (k+1) =
      simulateNext D A s_0 (simulateRev D A s_0 k) ::
        simulateRev D A s_0 k := rfl

@[simp] theorem simulateTrace_zero
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) :
    simulateTrace D A s_0 0 = (s_0, (none : Option ι)) := rfl

@[simp] theorem simulateTrace_zero_fst
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) :
    (simulateTrace D A s_0 0).1 = s_0 := rfl

@[simp] theorem simulateTrace_zero_snd
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) :
    (simulateTrace D A s_0 0).2 = (none : Option ι) := rfl

/-- Successor-step structural identity: the state-action pair at step
`k+1` equals `simulateNext` applied to the reverse-order prefix at
step `k`. -/
theorem simulateTrace_succ_eq
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    simulateTrace D A s_0 (k+1) =
      simulateNext D A s_0 (simulateRev D A s_0 k) := by
  simp [simulateTrace, simulateRev]

/-- The state at step `k` of the simulate equals the head of the
reverse-prefix list (when nonempty). -/
theorem simulateRev_head_eq
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    (simulateRev D A s_0 k).head?.map Prod.fst =
      some (simulateTrace D A s_0 k).1 := by
  unfold simulateTrace
  cases h : simulateRev D A s_0 k with
  | nil       => exact absurd h (simulateRev_ne_nil D A s_0 k)
  | cons x xs => simp

/-- Index-form characterisation of `simulateRev` reversed: the reverse
of the reverse-order prefix list at step `k` equals `List.ofFn (fun i :
Fin (k+1) => simulateTrace D A s_0 i.val)`.

This is the structural identity that lets us match `FinPrefix.toList`
(also a `List.ofFn` / `List.finRange.map`) with the simulate prefix
when proving the inductive step in `traceDist_AE_eq_simulateTrace_strong`
below.  Mirrors `avssSimulateRev_reverse_eq_ofFn` from `AVSS.lean §19.2`. -/
theorem simulateRev_reverse_eq_ofFn
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    (simulateRev D A s_0 k).reverse =
      List.ofFn (fun i : Fin (k+1) => simulateTrace D A s_0 i.val) := by
  induction k with
  | zero =>
    show ([(s_0, (none : Option ι))]).reverse =
        List.ofFn (fun i : Fin 1 => simulateTrace D A s_0 i.val)
    rw [List.reverse_singleton, List.ofFn_succ]
    simp [simulateTrace_zero]
  | succ k ih =>
    show (simulateNext D A s_0 (simulateRev D A s_0 k) ::
            simulateRev D A s_0 k).reverse =
        List.ofFn (fun i : Fin (k+2) => simulateTrace D A s_0 i.val)
    rw [List.reverse_cons, ih]
    -- Expand the RHS via `List.ofFn_succ'` (only).
    conv_rhs => rw [List.ofFn_succ', List.concat_eq_append]
    -- Both sides now have shape `List.ofFn (... Fin (k+1) ...) ++ [last]`.
    -- The two `List.ofFn` parts agree because `(Fin.castSucc i).val = i.val` is rfl.
    have hsim_last : simulateNext D A s_0 (simulateRev D A s_0 k) =
        simulateTrace D A s_0 (Fin.last (k+1)).val := by
      show simulateNext D A s_0 (simulateRev D A s_0 k) =
          simulateTrace D A s_0 (k+1)
      exact (simulateTrace_succ_eq D A s_0 k).symm
    rw [hsim_last]
    rfl

end Simulate

/-! ## AE-bridge meta-theorem (Phase 10.2)

Under any deterministic spec `D : DeterministicProbActionSpec σ ι` and
any adversary `A : Adversary σ ι`, the trace measure
`traceDist D.toProbActionSpec A μ₀` AE-equals the deterministic
`simulateTrace D A (ω 0).fst k` at every step `k`.

The proof is a verbatim transliteration of the AVSS-specific argument
in `AVSS.lean §19.2` (`avss_traceDist_AE_eq_avssSimulateTrace`), with
renames

  * `avssStep i s` → `D.step i s`
  * `avssSpec sec corr` → `D.toProbActionSpec`
  * `actionGate i s` → `D.gate i s`
  * `avssSimulate*` → `simulate*`

This makes inductive invariant arguments *purely combinatorial*: prove
the invariant on the deterministic `simulateTrace`, lift to the trace
distribution as an almost-sure statement, and conclude.

PR 10.3 will collapse `AVSS.lean §19.2`'s entire 200+ LOC proof chain
to one-line instantiations of these meta-theorems. -/

section AEBridge

open Classical
open MeasureTheory ProbabilityTheory

variable {σ ι : Type*}
  [Countable σ] [Countable ι]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Per-prefix kernel AE-bridge: under the deterministic spec `D` and
adversary `A`, the step kernel at index `k` over a prefix `h` puts
AE-mass on the simulate's next step at `(h ⟨0⟩).1` — provided the
prefix matches the simulate up to step `k`.

This is the per-history component of the inductive step in
`traceDist_AE_eq_simulateTrace_strong` below.  The proof branches on
the schedule and gate, identifying each Dirac point with
`simulateNext`.  Mirrors `avssSpec_R_stepKernel_AE_simulate` from
`AVSS.lean §19.2`. -/
private theorem stepKernel_AE_simulate
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι) (k : ℕ)
    (h : FinPrefix σ ι k) :
    ∀ᵐ y ∂(stepKernel D.toProbActionSpec A k h),
        (∀ i (hi : i ≤ k),
            h ⟨i, Finset.mem_Iic.mpr hi⟩ =
              simulateTrace D A
                (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 i) →
        y =
          simulateTrace D A
            (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 (k+1) := by
  classical
  set s_0 : σ :=
    (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 with hs0
  -- Under hQ (prefix matches simulate), h.toList = (simRev D A s_0 k).reverse
  -- and h.currentState = (simulateTrace D A s_0 k).1.  These two equalities
  -- reduce the kernel computation to `simulateNext`.
  have h_pred_consequences :
      (∀ i (hi : i ≤ k),
          h ⟨i, Finset.mem_Iic.mpr hi⟩ = simulateTrace D A s_0 i) →
      h.toList = (simulateRev D A s_0 k).reverse ∧
        h.currentState = (simulateTrace D A s_0 k).1 := by
    intro hQ
    refine ⟨?_, ?_⟩
    · -- `h.toList = (List.finRange (k+1)).map _`, and
      -- `(simRev D A s_0 k).reverse = List.ofFn _`.  Match per-index.
      unfold FinPrefix.toList
      rw [simulateRev_reverse_eq_ofFn, List.ofFn_eq_map]
      apply List.map_congr_left
      intro i _
      exact hQ i.val (by have := i.isLt; omega)
    · unfold FinPrefix.currentState
      exact congrArg Prod.fst (hQ k le_rfl)
  -- Branch on the kernel structure.  Both branches yield a Dirac measure.
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable,
    ProbabilityTheory.Kernel.coe_mk]
  have hPset : MeasurableSet
      {y : σ × Option ι |
        (∀ i (hi : i ≤ k),
            h ⟨i, Finset.mem_Iic.mpr hi⟩ = simulateTrace D A s_0 i) →
        y = simulateTrace D A s_0 (k+1)} :=
    MeasurableSet.of_discrete
  rcases hsched : A.schedule h.toList with _ | i
  · -- Schedule says `none`: kernel = `Dirac (h.currentState, none)`.
    rw [ae_dirac_iff hPset]
    intro hQ
    obtain ⟨h_toList, h_curr⟩ := h_pred_consequences hQ
    rw [simulateTrace_succ_eq]
    unfold simulateNext
    have h_sched_simRev : A.schedule
        (simulateRev D A s_0 k).reverse = none := by
      rw [← h_toList]; exact hsched
    rw [h_sched_simRev]
    have h_head := simulateRev_head_eq D A s_0 k
    show (h.currentState, _) =
        (((simulateRev D A s_0 k).head?.map Prod.fst).getD s_0, _)
    rw [h_head, Option.getD_some, h_curr]
  · -- Schedule says `some i`: branch on the gate at `h.currentState`.
    by_cases hgate : (D.toProbActionSpec.actions i).gate h.currentState
    · -- Gate-pass: pure-Dirac kernel applies `D.step i`.
      simp only [hgate, dite_true]
      rw [show (D.toProbActionSpec.actions i).effect h.currentState hgate
            = PMF.pure (D.step i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      intro hQ
      obtain ⟨h_toList, h_curr⟩ := h_pred_consequences hQ
      rw [simulateTrace_succ_eq]
      unfold simulateNext
      have h_sched_simRev : A.schedule
          (simulateRev D A s_0 k).reverse = some i := by
        rw [← h_toList]; exact hsched
      rw [h_sched_simRev]
      have h_head := simulateRev_head_eq D A s_0 k
      -- `(D.toProbActionSpec.actions i).gate = D.gate i` is definitional, so
      -- `hgate : D.gate i h.currentState`.
      have hgate_curr : D.gate i h.currentState := hgate
      have hgate_simRev : D.gate i
          (((simulateRev D A s_0 k).head?.map Prod.fst).getD s_0) := by
        rw [h_head, Option.getD_some, ← h_curr]; exact hgate_curr
      show (D.step i h.currentState, some i) =
          (let s_k := ((simulateRev D A s_0 k).head?.map Prod.fst).getD s_0
           if D.gate i s_k then (D.step i s_k, some i)
           else (s_k, (none : Option ι)))
      simp only [if_pos hgate_simRev]
      rw [h_head, Option.getD_some, ← h_curr]
    · -- Gate-fail stutter: kernel = `Dirac (h.currentState, none)`.
      simp only [hgate, dite_false, ae_dirac_iff hPset]
      intro hQ
      obtain ⟨h_toList, h_curr⟩ := h_pred_consequences hQ
      rw [simulateTrace_succ_eq]
      unfold simulateNext
      have h_sched_simRev : A.schedule
          (simulateRev D A s_0 k).reverse = some i := by
        rw [← h_toList]; exact hsched
      rw [h_sched_simRev]
      have h_head := simulateRev_head_eq D A s_0 k
      have hgate_curr : ¬ D.gate i h.currentState := hgate
      have hgate_simRev : ¬ D.gate i
          (((simulateRev D A s_0 k).head?.map Prod.fst).getD s_0) := by
        rw [h_head, Option.getD_some, ← h_curr]; exact hgate_curr
      show (h.currentState, _) =
          (let s_k := ((simulateRev D A s_0 k).head?.map Prod.fst).getD s_0
           if D.gate i s_k then (D.step i s_k, some i)
           else (s_k, (none : Option ι)))
      simp only [if_neg hgate_simRev]
      rw [h_head, Option.getD_some, h_curr]

/-- The pair-form step-0 marginal of `traceDist`: projecting the trace
at step `0` to the full `(state, action)` pair recovers the initial
measure paired with `none`.  Mirrors `traceDist_step_zero_pair_marginal`
from `AVSS.lean §19.2` but parameterised over the deterministic spec. -/
theorem traceDist_step_zero_pair_marginal
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    (traceDist D.toProbActionSpec A μ₀).map (fun ω => ω 0) =
      μ₀.map (fun s => (s, (none : Option ι))) := by
  classical
  unfold traceDist
  set μ₀_full : Measure (σ × Option ι) :=
    μ₀.map (fun s => (s, (none : Option ι)))
    with hμ₀_full_def
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- Step-0 marginal of `Kernel.trajMeasure`.
  unfold ProbabilityTheory.Kernel.trajMeasure
  have hmeas_eval0 : Measurable
      (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
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
      (Preorder.frestrictLe₂
        (π := fun _ : ℕ => σ × Option ι) (le_refl 0)) :=
    Preorder.measurable_frestrictLe₂ _
  have hcomp : Measurable
      ((fun y : Π _ : Finset.Iic 0, σ × Option ι => y ⟨0, by simp⟩) ∘
        Preorder.frestrictLe₂
          (π := fun _ : ℕ => σ × Option ι) (le_refl 0)) :=
    hmeas_pia.comp hmeas_fl2
  rw [hfact, ProbabilityTheory.Kernel.map_comp_right _ hmeas_fl0 hmeas_pia,
      ProbabilityTheory.Kernel.traj_map_frestrictLe_of_le (le_refl 0)]
  rw [ProbabilityTheory.Kernel.deterministic_map hmeas_fl2 hmeas_pia]
  rw [Measure.deterministic_comp_eq_map hcomp]
  rw [Measure.map_map hcomp (by fun_prop)]
  convert Measure.map_id (μ := μ₀_full)

/-- AE-base: the action component of step `0` of any `traceDist` is
`none`.  Pulls back `traceDist_step_zero_pair_marginal` through the
`Prod.snd` projection.  Mirrors `traceDist_step_zero_snd_AE` from
`AVSS.lean §19.2`. -/
theorem traceDist_step_zero_snd_AE
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] :
    ∀ᵐ ω ∂(traceDist D.toProbActionSpec A μ₀),
        (ω 0).2 = (none : Option ι) := by
  classical
  have hmarg := traceDist_step_zero_pair_marginal D A μ₀
  have hmeas_eval0 : Measurable
      (fun ω : Π _ : ℕ, σ × Option ι => ω 0) :=
    measurable_pi_apply 0
  -- AE on the pair-marginal: every `(s, none)` has snd = none.
  have hAE_full :
      ∀ᵐ x ∂(μ₀.map (fun s : σ => (s, (none : Option ι)))),
        x.2 = none := by
    rw [ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
    exact Filter.Eventually.of_forall fun _ => rfl
  -- Pull back through the trace-marginal identity.
  rw [← hmarg, ae_map_iff hmeas_eval0.aemeasurable
    MeasurableSet.of_discrete] at hAE_full
  exact hAE_full

/-- Strong-form inductive AE-bridge: under the deterministic spec `D`
and adversary `A`, the prefix `(ω 0..k)` of any `traceDist` trace
AE-matches the simulate's prefix `simulateTrace D A (ω 0).1 i` for
every `i ≤ k`.

Strong because `A.schedule` at every step depends on the *full*
prefix-history (via `A.schedule h.toList`), so a per-step inductive
step needs the matching to hold over the entire prefix.  Mirrors
`traceDist_AE_eq_avssSimulateTrace_strong` from `AVSS.lean §19.2`. -/
private theorem traceDist_AE_eq_simulateTrace_strong
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] (k : ℕ) :
    ∀ᵐ ω ∂(traceDist D.toProbActionSpec A μ₀),
        ∀ i, i ≤ k → ω i = simulateTrace D A (ω 0).1 i := by
  classical
  induction k with
  | zero =>
    have h0 := traceDist_step_zero_snd_AE D A μ₀
    filter_upwards [h0] with ω hω i hi
    interval_cases i
    rw [simulateTrace_zero]
    exact Prod.ext rfl hω
  | succ k ih =>
    -- Suffices: ∀ᵐ ω, ω (k+1) = sim (k+1)  AND  IH (∀ i ≤ k, ω i = sim i).
    -- Combine the IH AE with a single-step AE conditional on the IH.
    suffices hone_step :
        ∀ᵐ ω ∂(traceDist D.toProbActionSpec A μ₀),
          (∀ i, i ≤ k → ω i = simulateTrace D A (ω 0).1 i) →
            ω (k+1) = simulateTrace D A (ω 0).1 (k+1) by
      filter_upwards [ih, hone_step] with ω h_ih h_step i hi
      rcases Nat.lt_or_ge i (k+1) with h_lt | h_ge
      · exact h_ih i (by omega)
      · have hi_eq : i = k + 1 := by omega
        subst hi_eq
        exact h_step h_ih
    -- Marginal recurrence: pull (frestrictLe k ω, ω (k+1)) marginal.
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, σ × Option ι =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : σ => (s, (none : Option ι)))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((traceDist D.toProbActionSpec A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel D.toProbActionSpec A k) =
        (traceDist D.toProbActionSpec A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    -- Per-prefix AE: under hQ, the kernel's Dirac point matches simulate.
    have h_inner : ∀ᵐ h ∂((traceDist D.toProbActionSpec A μ₀).map
            (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel D.toProbActionSpec A k h),
          (∀ i (hi : i ≤ k),
              h ⟨i, Finset.mem_Iic.mpr hi⟩ =
                simulateTrace D A
                  (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 i) →
          y =
            simulateTrace D A
              (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 (k+1) :=
      Filter.Eventually.of_forall fun h =>
        stepKernel_AE_simulate D A k h
    -- Lift to AE on the joint measure.
    have hjoint :
        ∀ᵐ x ∂(((traceDist D.toProbActionSpec A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel D.toProbActionSpec A k)),
          (∀ i (hi : i ≤ k),
              x.1 ⟨i, Finset.mem_Iic.mpr hi⟩ =
                simulateTrace D A
                  (x.1 ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 i) →
          x.2 =
            simulateTrace D A
              (x.1 ⟨0, Finset.mem_Iic.mpr (Nat.zero_le k)⟩).1 (k+1) :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    -- Transfer along hk and translate.
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    -- `(Preorder.frestrictLe k ω) ⟨i, _⟩ = ω i` is definitional.
    filter_upwards [hjoint] with ω hω hpre
    apply hω
    intro i hi
    exact hpre i hi

/-- **Phase 10.2 AE-bridge meta-theorem.** Under any deterministic spec
`D : DeterministicProbActionSpec σ ι` and any adversary `A : Adversary
σ ι`, the trace at step `k` AE-equals `simulateTrace D A (ω 0).1 k` —
because every step's effect-PMF is a Dirac (`PMF.pure (D.step i s)`)
and the schedule is a deterministic function of the view-history.

Generalises `AVSS.lean §19.2`'s `traceDist_AE_eq_avssSimulateTrace`.
PR 10.3 will collapse that AVSS-specific theorem to a one-line
instantiation of this meta-theorem. -/
theorem traceDist_AE_eq_simulateTrace
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀] (k : ℕ) :
    ∀ᵐ ω ∂(traceDist D.toProbActionSpec A μ₀),
        ω k = simulateTrace D A (ω 0).1 k := by
  filter_upwards [traceDist_AE_eq_simulateTrace_strong D A μ₀ k]
    with ω hω
  exact hω k le_rfl

end AEBridge

end Leslie.Prob
