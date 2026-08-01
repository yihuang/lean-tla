/-
M3 W3 — BenOrAsync calibration test for `FairASTCertificate`.

This file is the calibration test for the **fair** AST certificate
defined in `Leslie.Prob.Liveness` (POPL 2026 fair extension). It
mirrors `Examples/Prob/RandomWalker1D.lean`'s role for the demonic
rule (`ASTCertificate`).

The point is to instantiate `FairASTCertificate` on a stripped-down,
async Ben-Or-style protocol so that **every fair-only field** of the
certificate is exercised non-vacuously. Specifically:

  * `V_super_fair` — strict supermartingale on fair actions only.
  * `U_dec_det` — deterministic-decrease pattern on fair actions only.

The demonic counterpart `RandomWalker1D` exercises only the
unconditional fields (`V_super`, `U_dec_prob`); the new fields above
require an example with a *non-trivial* fair / non-fair action split.

## Protocol

A simplified async Ben-Or fallback (per design plan v2.2 §"AST rule"):

  * **State**: `(round : ℕ, decided : Bool)`.
  * **Action `delay`**: `round ↦ round + 1`, no decision change.
    Enabled when `¬ decided`. **NOT a fair action** — adversary may
    fire `delay` arbitrarily often.
  * **Action `decide`**: `decided ↦ true`. Enabled when `¬ decided`.
    **IS a fair action** — the fairness assumption forces it to fire
    eventually.

The state `decided = true` is terminal. The fairness assumption is
the real ingredient: under any weakly-fair adversary, `decide` must
eventually fire because it's continuously enabled while `¬ decided`.

The init predicate `s.round = 0 ∧ ¬ s.decided` plus a static round
budget `N` give the bound `s.round ≤ N` along trajectories — but
because `delay` increases `round`, **`Inv` is just `True`** and the
`V_init_bdd` field uses the constant bound `K = 1` (since `V s = 1`
on undecided, `V s = 0` on decided).

This is enough to verify every certificate field elaborates
correctly and closes form. Real Ben-Or with multi-party agreement
plus probabilistic coin-tossing is a future M3+ deliverable; the
present file is **only** a calibration that the `FairASTCertificate`
shape matches what async randomized protocols need.

## What's calibrated

  * `Inv` — trivial (`True`).
  * `V s = if s.decided then 0 else 1` — the supermartingale.
  * `U s = if s.decided then 0 else 1` — the variant.
  * `V_super`: holds on both actions (V is non-increasing).
  * `V_super_fair`: holds **strictly** on the fair `decide` action.
  * `U_dec_det`: U decreases when `decide` fires.
  * `U_bdd_subl`: bounded by `1` for any sublevel set.
  * `U_dec_prob`: the deterministic decrease lifts to probability `1`.
  * `V_init_bdd`: uniform bound `K = 1`.

## What this does NOT calibrate

  * Multi-party agreement — out of scope for the rule's calibration.
    Probabilistic decision via coin toss with multi-party broadcast
    is a future deliverable.
  * Quantitative tail bounds — calibration only checks the
    certificate's *shape*, not concrete probability bounds.
-/

import Leslie.Prob.Liveness

namespace Leslie.Examples.Prob.BenOrAsync

open Leslie.Prob NNReal
open scoped ENNReal

/-! ## §1. State + action -/

/-- BenOrAsync state: round counter (used by the adversary's delay
budget; not load-bearing for the certificate's bound) plus a
decision bit. -/
structure BOState where
  round   : ℕ
  decided : Bool
  deriving DecidableEq, Repr

/-- BenOrAsync action labels. `delay` is non-fair; `decide` is
fair-required. -/
inductive BOAction
  | delay
  | decide
  deriving DecidableEq, Repr

/-! ## §2. Countable / measurable instances

`FairASTCertificate` requires `[Countable σ] [Countable ι]
[MeasurableSpace σ] [MeasurableSingletonClass σ]
[MeasurableSpace ι] [MeasurableSingletonClass ι]`. We supply the
discrete instances. -/

instance : Countable BOState := by
  classical
  let f : BOState → ℕ × Bool := fun s => (s.round, s.decided)
  let g : ℕ × Bool → BOState := fun ⟨n, b⟩ => ⟨n, b⟩
  have hl : Function.LeftInverse g f := fun _ => rfl
  exact Function.Injective.countable hl.injective

instance : Countable BOAction := by
  classical
  let f : BOAction → Fin 2 := fun
    | .delay  => 0
    | .decide => 1
  let g : Fin 2 → BOAction := fun n => if n = 0 then .delay else .decide
  have hl : Function.LeftInverse g f := fun a => by cases a <;> rfl
  exact Function.Injective.countable hl.injective

instance : MeasurableSpace BOState := ⊤
instance : MeasurableSingletonClass BOState := ⟨fun _ => trivial⟩
instance : MeasurableSpace BOAction := ⊤
instance : MeasurableSingletonClass BOAction := ⟨fun _ => trivial⟩

/-! ## §3. Spec

Both actions are gated on `¬ decided`. `delay` increments `round`;
`decide` flips `decided` to `true`. Effects are Dirac. -/

/-- BenOrAsync spec: init from `(0, false)`; both actions enabled
when undecided. -/
noncomputable def boSpec : ProbActionSpec BOState BOAction where
  init := fun s => s.round = 0 ∧ ¬ s.decided
  actions := fun
    | .delay =>
      { gate   := fun s => ¬ s.decided
        effect := fun s _ => PMF.pure ⟨s.round + 1, s.decided⟩ }
    | .decide =>
      { gate   := fun s => ¬ s.decided
        effect := fun s _ => PMF.pure ⟨s.round, true⟩ }

/-- A state is terminated iff `decided`. -/
def boTerminated (s : BOState) : Prop := s.decided = true

/-! ## §4. Fairness assumptions

Fair-required actions: `{decide}`. The `isWeaklyFair` predicate is
left as `True` — same convention as `AVSSStub.avssFair`. The real
temporal-side condition is consumed by `FairASTCertificate.sound`
internally; for calibration we only need the predicate to elaborate
and `decide ∈ fair_actions` to hold. -/

/-- The set of fair-required action labels. -/
def boFairActions : Set BOAction := { a | a = .decide }

/-- Fairness assumptions for BenOrAsync. -/
noncomputable def boFair : FairnessAssumptions BOState BOAction where
  fair_actions := boFairActions
  isWeaklyFair := fun _ => True

@[simp] theorem decide_mem_fair_actions :
    BOAction.decide ∈ boFair.fair_actions := by
  show (BOAction.decide : BOAction) ∈ boFairActions
  rfl

@[simp] theorem delay_not_mem_fair_actions :
    BOAction.delay ∉ boFair.fair_actions := by
  show (BOAction.delay : BOAction) ∉ boFairActions
  intro h
  cases h

/-! ## §5. The certificate

Every obligation closes by reducing the per-action `tsum` over the
Dirac PMF to a single term via `tsum_eq_single`, then a one-liner
boolean / numeric inequality. The non-trivial cases — `V_super_fair`
and `U_dec_det` — exercise the fair-only fields. -/

/-- The `FairASTCertificate` instance for `boSpec` against
`boTerminated`. -/
noncomputable def boCert :
    FairASTCertificate boSpec boFair boTerminated where
  Inv := fun _ => True
  V := fun s => if s.decided then 0 else 1
  U := fun s => if s.decided then 0 else 1
  inv_init := fun _ _ => trivial
  inv_step := fun _ _ _ _ _ _ => trivial
  V_term := fun s _ ht => by
    -- `s.decided = true` ⇒ V s = 0.
    have h : s.decided = true := ht
    simp [h]
  V_pos := fun s _ ht => by
    -- `¬ s.decided` ⇒ V s = 1 > 0.
    have hf : s.decided = false := by
      cases h : s.decided
      · rfl
      · exact absurd h ht
    simp [hf]
  V_super := fun i s _ _ hnt => Or.inl <| by
    -- `s.decided = false` (from `hnt : ¬ boTerminated s`).
    have hf : s.decided = false := by
      cases h : s.decided
      · rfl
      · exact absurd h hnt
    cases i
    · -- delay action: `s' = ⟨s.round + 1, s.decided⟩`. `V s' = V s = 1`.
      simp only [boSpec]
      rw [tsum_eq_single ⟨s.round + 1, s.decided⟩]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
    · -- decide action: `s' = ⟨s.round, true⟩`. `V s' = 0 < V s = 1`.
      simp only [boSpec]
      rw [tsum_eq_single ⟨s.round, true⟩]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        simp [hf]
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_super_fair := fun i s _ hfair _ hnt => Or.inl <| by
    -- The fair action is `decide`; on it, V strictly decreases from 1 to 0.
    have hf : s.decided = false := by
      cases h : s.decided
      · rfl
      · exact absurd h hnt
    cases i
    · -- delay: contradiction with `hfair`.
      exact absurd hfair (by simp)
    · -- decide: tsum collapses to `V ⟨s.round, true⟩ = 0 < 1 = V s`.
      simp only [boSpec]
      rw [tsum_eq_single ⟨s.round, true⟩]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        simp [hf]
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  U_term := fun s _ ht => by
    have h : s.decided = true := ht
    simp [h]
  U_dec_det := fun i s _ hfair _ hnt s' hs' => by
    have hf : s.decided = false := by
      cases h : s.decided
      · rfl
      · exact absurd h hnt
    cases i
    · -- delay: contradiction with `hfair`.
      exact absurd hfair (by simp)
    · -- decide: support is `{⟨s.round, true⟩}`, U decreases 1 → 0.
      simp only [boSpec, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      left
      simp [hf]
  U_bdd_subl := fun _ => by
    -- U is at most 1 unconditionally.
    refine ⟨1, fun s _ _ => ?_⟩
    by_cases h : s.decided
    · simp [h]
    · simp [h]
  V_init_bdd := ⟨1, fun s _ => by
    by_cases h : s.decided
    · simp [h]
    · simp [h]⟩

/-! ## §6. Sanity examples -/

/-- The certificate elaborates: every field types correctly. -/
noncomputable example :
    FairASTCertificate boSpec boFair boTerminated := boCert

/-- The variant value at an undecided state. -/
example : boCert.U ⟨5, false⟩ = 1 := rfl

/-- The variant value at a decided state. -/
example : boCert.U ⟨5, true⟩ = 0 := rfl

/-- The likelihood value at an undecided state. -/
example : boCert.V ⟨3, false⟩ = (1 : ℝ≥0) := rfl

/-- The likelihood value at a decided state. -/
example : boCert.V ⟨3, true⟩ = (0 : ℝ≥0) := rfl

/-- Termination predicate at a decided state. -/
example : boTerminated ⟨7, true⟩ := rfl

/-- Non-termination at an undecided state. -/
example : ¬ boTerminated ⟨7, false⟩ := by
  show ¬ ((false : Bool) = true)
  decide

/-- The fair action `decide` is in `fair_actions`. -/
example : BOAction.decide ∈ boFair.fair_actions := decide_mem_fair_actions

/-- The non-fair action `delay` is *not* in `fair_actions`. -/
example : BOAction.delay ∉ boFair.fair_actions := delay_not_mem_fair_actions

end Leslie.Examples.Prob.BenOrAsync
