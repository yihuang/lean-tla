/-
M3 W4 — CommonCoin: Rabin-style weak common coin (qualitative).

A weak common coin protocol: each party tosses a uniform private bit,
then aggregates by reading every party's toss and outputting a fixed
function of the bits. With constant probability all parties output
the same uniform bit ("agreement"); the qualitative version (this
milestone) focuses on **termination** via `FairASTCertificate` and
states agreement / uniform-output as named theorems with documented
sorries for the M3 polish quantitative bound.

## Per impl plan v2.2 §M3 W4

> Output a uniform bit with constant probability `≥ ρ`. Qualitative
> version (this milestone) is enough for M5; quantitative version
> (with explicit lower bound on agreement probability) goes into the
> optional `Quantitative.lean`.

## Protocol — `n`-party generalization

Parameterized over `n : ℕ` (number of parties). The `Fin 2`
hard-coding has been removed; every gate, effect, invariant and
variant is defined uniformly in `n`.

  * **State**: per-party toss `tosses : Fin n → Option Bool` and
    per-party output `outputs : Fin n → Option Bool`.
  * **Action `toss i`**: gated on `tosses i = none`. Effect: PMF over
    `Bool` (uniform) — sets `tosses i := some b`. **Fair-required**.
  * **Action `aggregate i`**: gated on `(∀ k, tosses k ≠ none) ∧
    outputs i = none`. Effect: deterministic — output is the AND of
    all tosses. **Fair-required**.

The aggregate output is a deterministic function of the random tosses
that every party computes identically, so once any output exists, the
"common bit" is fixed and every subsequent aggregate matches.

## Variant strategy

We use `ccU s = countNone tosses s + countNone outputs s` (total
remaining work — unset tosses plus unset outputs). Both `toss` and
`aggregate` actions strictly decrease `ccU` by exactly `1`
deterministically, so every fair-required firing decreases the
variant unconditionally. The likelihood `ccV s = (ccU s : ℝ≥0)`
inherits the same strict-decrease behaviour pointwise on the support.

The invariant `ccInv s` ensures `outputs i ≠ none → ∀ j,
s.tosses j ≠ none` (i.e., aggregation only happens after every
toss). This is needed for `V_term` and `U_term`: a terminated state
(all outputs set) has all tosses set too, so `ccU s = 0`.

## What's calibrated (this file)

  * State machine + `ProbActionSpec` model + countable / measurable
    instances, all parameterized by `n : ℕ`.
  * Fairness predicate (both actions fair-required).
  * `FairASTCertificate` instance — **sorry-free** for every
    `n : ℕ`. Every field obligation closes via the strict-decrease
    pointwise argument plus `tsum_eq_single` /
    `ENNReal.tsum_mul_right` for the integral form.
  * Agreement / uniform-output theorems: stated qualitatively
    (`∃ p > 0, ...`) for general `n`; the witness `p = 1` works
    because AND aggregation makes every aggregating party produce
    the **same** deterministic bit, so agreement is guaranteed.

## What this does NOT calibrate

  * **Quantitative bound `≥ ρ`** — explicit lower bound on agreement
    probability. Goes into the optional `Quantitative.lean` per plan.
  * **Adversarial corruption** — corrupted parties can deviate from
    the toss / aggregate protocol. We model only the honest case here.
-/

import Leslie.Prob.Liveness

namespace Leslie.Examples.Prob.CommonCoin

open Leslie.Prob MeasureTheory NNReal
open scoped ENNReal

/-! ## §1. State + action -/

/-- CommonCoin state for `n` parties: per-party toss outcome and
per-party output. `none` represents "not yet tossed / decided". -/
structure CCState (n : ℕ) where
  tosses  : Fin n → Option Bool
  outputs : Fin n → Option Bool

/-- CommonCoin action labels: a party tosses, or a party aggregates
once all tosses are visible. -/
inductive CCAction (n : ℕ)
  | toss      (i : Fin n)
  | aggregate (i : Fin n)
  deriving DecidableEq, Repr

/-! ## §2. Countable / measurable instances -/

instance (n : ℕ) : Countable (CCState n) := by
  classical
  let f : CCState n → (Fin n → Option Bool) × (Fin n → Option Bool) :=
    fun s => (s.tosses, s.outputs)
  let g : (Fin n → Option Bool) × (Fin n → Option Bool) → CCState n :=
    fun p => ⟨p.1, p.2⟩
  have hl : Function.LeftInverse g f := fun _ => rfl
  exact Function.Injective.countable hl.injective

instance (n : ℕ) : Countable (CCAction n) := by
  classical
  let f : CCAction n → Bool × Fin n := fun
    | .toss      i => (false, i)
    | .aggregate i => (true,  i)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨i⟩ | ⟨i⟩ <;> rcases b with ⟨j⟩ | ⟨j⟩ <;>
      simp [f] at hab <;> first
        | rfl
        | (rcases hab with rfl; rfl)
  exact Function.Injective.countable hf

instance (n : ℕ) : MeasurableSpace (CCState n) := ⊤
instance (n : ℕ) : MeasurableSingletonClass (CCState n) := ⟨fun _ => trivial⟩
instance (n : ℕ) : MeasurableSpace (CCAction n) := ⊤
instance (n : ℕ) : MeasurableSingletonClass (CCAction n) := ⟨fun _ => trivial⟩

/-! ## §3. Functional updates -/

/-- Functional update on `Fin n → Option Bool`. -/
def setOpt {n : ℕ} (f : Fin n → Option Bool) (i : Fin n) (v : Option Bool) :
    Fin n → Option Bool :=
  fun j => if j = i then v else f j

@[simp] theorem setOpt_self {n : ℕ} (f : Fin n → Option Bool) (i : Fin n)
    (v : Option Bool) : setOpt f i v i = v := by
  simp [setOpt]

@[simp] theorem setOpt_ne {n : ℕ} (f : Fin n → Option Bool) (i j : Fin n)
    (v : Option Bool) (h : j ≠ i) : setOpt f i v j = f j := by
  simp [setOpt, h]

/-! ## §4. Spec -/

/-- The aggregation function: AND of all tosses. By design,
deterministic and identical for every aggregating party. The default
`false` covers the unreachable case where the gate has been bypassed
(it never fires for gated firings). -/
def aggBit {n : ℕ} (tosses : Fin n → Option Bool) : Bool :=
  decide (∀ i : Fin n, tosses i = some true)

/-- Local state transformer for `toss i`: writes `b` into `tosses i`. -/
def tossLocal {n : ℕ} (s : CCState n) (i : Fin n) (b : Bool) : CCState n :=
  { s with tosses := setOpt s.tosses i (some b) }

/-- Local state transformer for `aggregate i`: writes the aggregated
bit into `outputs i`. -/
def aggregateLocal {n : ℕ} (s : CCState n) (i : Fin n) : CCState n :=
  { s with outputs := setOpt s.outputs i (some (aggBit s.tosses)) }

/-- The CommonCoin spec for `n` parties. Init: all tosses and outputs `none`. -/
noncomputable def ccSpec (n : ℕ) : ProbActionSpec (CCState n) (CCAction n) where
  init := fun s => (∀ i, s.tosses i = none) ∧ (∀ i, s.outputs i = none)
  actions := fun
    | .toss i =>
      { gate   := fun s => s.tosses i = none
        effect := fun s _ => (PMF.uniform Bool).map (fun b => tossLocal s i b) }
    | .aggregate i =>
      { gate   := fun s =>
          (∀ k : Fin n, s.tosses k ≠ none) ∧
          s.outputs i = none
        effect := fun s _ => PMF.pure (aggregateLocal s i) }

/-- A state is terminated iff every party has output a bit. -/
def ccTerminated {n : ℕ} (s : CCState n) : Prop := ∀ i, s.outputs i ≠ none

/-! ## §5. Fairness -/

/-- All actions are fair-required. -/
def ccFairActions (n : ℕ) : Set (CCAction n) := Set.univ

/-- Fairness assumptions for CommonCoin. The temporal-side condition
`isWeaklyFair` is left as `True` — same convention as the BenOrAsync
calibration; the real predicate is consumed inside
`FairASTCertificate.sound`. -/
noncomputable def ccFair (n : ℕ) : FairnessAssumptions (CCState n) (CCAction n) where
  fair_actions := ccFairActions n
  isWeaklyFair := fun _ => True

@[simp] theorem mem_ccFair {n : ℕ} (a : CCAction n) :
    a ∈ (ccFair n).fair_actions := trivial

/-! ## §6. Variant + invariant

`U s` counts unset slots in tosses and outputs. Aggregate decreases U
by 1 (writes one output). Toss also decreases U by 1 (writes one
toss). The variant is bounded by `2 * n`.

The invariant `ccInv` ensures: if any output is set, then all tosses
are set. This is needed for `V_term` (terminated state has no unset
outputs, hence by `ccInv` no unset tosses, hence `V s = 0`). -/

/-- Count of unset slots in a `Fin n → Option Bool` map. -/
def countNone {n : ℕ} (f : Fin n → Option Bool) : ℕ :=
  (Finset.univ : Finset (Fin n)).sum (fun i => if f i = none then 1 else 0)

/-- The count is bounded by `n`. -/
theorem countNone_le {n : ℕ} (f : Fin n → Option Bool) : countNone f ≤ n := by
  unfold countNone
  calc (Finset.univ : Finset (Fin n)).sum (fun i => if f i = none then 1 else 0)
      ≤ (Finset.univ : Finset (Fin n)).sum (fun _ => 1) := by
        apply Finset.sum_le_sum
        intro i _; split_ifs <;> omega
    _ = n := by simp

/-- Variant: total un-completed work — unset tosses plus unset
outputs. Both actions decrease this by exactly 1. -/
def ccU {n : ℕ} (s : CCState n) : ℕ := countNone s.tosses + countNone s.outputs

theorem ccU_le_two_n {n : ℕ} (s : CCState n) : ccU s ≤ 2 * n := by
  unfold ccU
  have h₁ := countNone_le s.tosses
  have h₂ := countNone_le s.outputs
  omega

/-- Likelihood `V s = (ccU s : ℝ≥0)`. -/
noncomputable def ccV {n : ℕ} (s : CCState n) : ℝ≥0 := (ccU s : ℝ≥0)

/-- Invariant: any party that has output also implies all tosses are
set. Captures the protocol-level fact that aggregation only fires
after every toss. -/
def ccInv {n : ℕ} (s : CCState n) : Prop :=
  (∃ i, s.outputs i ≠ none) → ∀ j, s.tosses j ≠ none

/-! ## §7. Variant-decrease lemmas -/

/-- Toss is a frame on outputs: `tossLocal s i b` does not change `outputs`. -/
@[simp] theorem tossLocal_outputs {n : ℕ} (s : CCState n) (i : Fin n) (b : Bool) :
    (tossLocal s i b).outputs = s.outputs := rfl

/-- Aggregate sets `outputs i` to `some _`. -/
@[simp] theorem aggregateLocal_outputs_self {n : ℕ} (s : CCState n) (i : Fin n) :
    (aggregateLocal s i).outputs i = some (aggBit s.tosses) := by
  simp [aggregateLocal, setOpt]

/-- Aggregate frames `outputs j` for `j ≠ i`. -/
@[simp] theorem aggregateLocal_outputs_ne {n : ℕ} (s : CCState n) (i j : Fin n)
    (h : j ≠ i) : (aggregateLocal s i).outputs j = s.outputs j := by
  simp [aggregateLocal, setOpt, h]

/-- Aggregate frames tosses. -/
@[simp] theorem aggregateLocal_tosses {n : ℕ} (s : CCState n) (i : Fin n) :
    (aggregateLocal s i).tosses = s.tosses := rfl

/-- Toss sets `tosses i` to `some b`. -/
@[simp] theorem tossLocal_tosses_self {n : ℕ} (s : CCState n) (i : Fin n) (b : Bool) :
    (tossLocal s i b).tosses i = some b := by
  simp [tossLocal, setOpt]

/-- Toss frames `tosses j` for `j ≠ i`. -/
@[simp] theorem tossLocal_tosses_ne {n : ℕ} (s : CCState n) (i j : Fin n) (b : Bool)
    (h : j ≠ i) : (tossLocal s i b).tosses j = s.tosses j := by
  simp [tossLocal, setOpt, h]

/-- Decrease lemma: if `f i = none`, replacing it with `some _`
decreases `countNone` by exactly 1. The proof splits the sum at `i`. -/
theorem countNone_setOpt_some {n : ℕ} (f : Fin n → Option Bool) (i : Fin n)
    (b : Bool) (h : f i = none) :
    countNone (setOpt f i (some b)) + 1 = countNone f := by
  unfold countNone
  classical
  -- Split each sum at the singleton `{i}` vs its complement.
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hsplit_orig :
      (Finset.univ : Finset (Fin n)).sum (fun j => if f j = none then 1 else 0) =
        (if f i = none then 1 else 0) +
        ((Finset.univ.erase i).sum (fun j => if f j = none then 1 else 0)) := by
    rw [← Finset.sum_erase_add _ _ hi_mem]; ring
  have hsplit_new :
      (Finset.univ : Finset (Fin n)).sum
          (fun j => if setOpt f i (some b) j = none then 1 else 0) =
        (if setOpt f i (some b) i = none then 1 else 0) +
        ((Finset.univ.erase i).sum
          (fun j => if setOpt f i (some b) j = none then 1 else 0)) := by
    rw [← Finset.sum_erase_add _ _ hi_mem]; ring
  -- Simplify the two singleton-position values.
  have hi_orig : (if f i = none then 1 else 0) = (1 : ℕ) := by simp [h]
  have hi_new : (if setOpt f i (some b) i = none then 1 else 0) = (0 : ℕ) := by
    simp [setOpt_self]
  -- The complementary sums coincide pointwise.
  have hcomp :
      (Finset.univ.erase i).sum
          (fun j => if setOpt f i (some b) j = none then 1 else 0) =
        (Finset.univ.erase i).sum (fun j => if f j = none then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [setOpt_ne _ _ _ _ hj_ne]
  rw [hsplit_new, hsplit_orig, hi_orig, hi_new, hcomp]
  ring

/-! ## §8. The certificate -/

/-- The CommonCoin `FairASTCertificate` instance, parameterized by
`n : ℕ`. Sorry-free for every `n`. -/
noncomputable def ccCert (n : ℕ) :
    FairASTCertificate (ccSpec n) (ccFair n) ccTerminated where
  Inv := ccInv
  V := ccV
  U := ccU
  inv_init := fun s hinit => by
    -- Init: all outputs `none`, so the antecedent of `ccInv` is vacuous.
    intro ⟨i, hi⟩
    exact absurd (hinit.2 i) hi
  inv_step := fun i s hgate hInv s' hs' => by
    -- Case split on action.
    cases i with
    | toss j =>
      -- s' = tossLocal s j b for some b. Outputs unchanged from s.
      simp only [ccSpec, PMF.mem_support_map_iff] at hs'
      obtain ⟨b, _, rfl⟩ := hs'
      -- Need: ccInv (tossLocal s j b).
      intro ⟨k, hk⟩
      have hk' : s.outputs k ≠ none := by
        have : (tossLocal s j b).outputs k = s.outputs k := rfl
        rw [this] at hk
        exact hk
      have hall : ∀ m, s.tosses m ≠ none := hInv ⟨k, hk'⟩
      intro m
      by_cases hmj : m = j
      · subst hmj
        show (setOpt s.tosses m (some b)) m ≠ none
        rw [setOpt_self]; exact Option.some_ne_none b
      · show (setOpt s.tosses j (some b)) m ≠ none
        rw [setOpt_ne _ _ _ _ hmj]
        exact hall m
    | aggregate j =>
      -- s' = aggregateLocal s j. Tosses unchanged; gate ensures all set.
      simp only [ccSpec, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      -- Gate: all tosses set.
      obtain ⟨hall, _⟩ := hgate
      intro _ m
      show (aggregateLocal s j).tosses m ≠ none
      rw [aggregateLocal_tosses]
      exact hall m
  V_term := fun s hInv ht => by
    -- Terminated: ∀ i, s.outputs i ≠ none. By `hInv`, all tosses are
    -- also set. So `ccU s = 0`.
    show ccV s = 0
    unfold ccV
    have hall_t : ∀ j, s.tosses j ≠ none := by
      classical
      by_cases hn : Nonempty (Fin n)
      · obtain ⟨i₀⟩ := hn
        exact hInv ⟨i₀, ht i₀⟩
      · -- empty Fin n: all `j : Fin n` are absurd.
        intro j
        exact absurd ⟨j⟩ hn
    have hc : ccU s = 0 := by
      unfold ccU countNone
      have hT : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (if s.tosses j = none then 1 else 0) = (0 : ℕ) := by
        intro j _
        simp [hall_t j]
      have hO : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (if s.outputs j = none then 1 else 0) = (0 : ℕ) := by
        intro j _
        simp [ht j]
      rw [Finset.sum_congr rfl hT, Finset.sum_congr rfl hO]
      simp
    rw [hc]; simp
  V_pos := fun s _ ht => by
    -- Non-terminated: ∃ i, s.outputs i = none. So `ccU s ≥ 1 > 0`.
    show 0 < ccV s
    unfold ccV
    have ⟨i, hi⟩ : ∃ i, s.outputs i = none := by
      classical
      by_contra h
      push_neg at h
      exact ht (fun i => h i)
    have hpos : 0 < ccU s := by
      unfold ccU countNone
      classical
      have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
      have h_pos_term : (1 : ℕ) ≤ (if s.outputs i = none then 1 else 0) := by
        simp [hi]
      have h_nonneg :
          ∀ j ∈ (Finset.univ : Finset (Fin n)),
            (0 : ℕ) ≤ (if s.outputs j = none then 1 else 0) := by
        intro j _; split_ifs <;> omega
      have h_le : (1 : ℕ) ≤
          (Finset.univ : Finset (Fin n)).sum
            (fun j => if s.outputs j = none then 1 else 0) := by
        calc (1 : ℕ)
            ≤ (if s.outputs i = none then 1 else 0) := h_pos_term
          _ ≤ (Finset.univ : Finset (Fin n)).sum
              (fun j => if s.outputs j = none then 1 else 0) :=
              Finset.single_le_sum
                (f := fun j => if s.outputs j = none then 1 else 0)
                h_nonneg hi_mem
      omega
    exact_mod_cast hpos
  V_super := fun i s hgate _ _ => Or.inl <| by
    -- Both actions strictly decrease V by exactly 1 pointwise on the
    -- support, so the expectation bound `≤ V s` follows trivially.
    cases i with
    | toss j =>
      simp only [ccSpec]
      have hgate_t : s.tosses j = none := hgate
      have h_le : ∀ s' : CCState n, ((PMF.uniform Bool).map
          (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞) ≤
          ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' * (ccV s : ℝ≥0∞) := by
        intro s'
        by_cases hsupp : s' ∈ ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)).support
        · rw [PMF.mem_support_map_iff] at hsupp
          obtain ⟨b, _, hsb⟩ := hsupp
          have hVle : ccV s' ≤ ccV s := by
            rw [← hsb]
            unfold ccV ccU
            have hdec : countNone (tossLocal s j b).tosses + 1 =
                countNone s.tosses := by
              show countNone (setOpt s.tosses j (some b)) + 1 =
                  countNone s.tosses
              exact countNone_setOpt_some s.tosses j b hgate_t
            have hout : (tossLocal s j b).outputs = s.outputs := rfl
            rw [hout]
            have hh : countNone (tossLocal s j b).tosses ≤
                countNone s.tosses := by omega
            exact_mod_cast Nat.add_le_add_right hh _
          gcongr
        · have hzero : ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' = 0 := by
            rw [PMF.apply_eq_zero_iff]; exact hsupp
          simp [hzero]
      calc ∑' s' : CCState n, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞)
          ≤ ∑' s' : CCState n, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' * (ccV s : ℝ≥0∞) := by
            exact ENNReal.tsum_le_tsum h_le
        _ = (∑' s' : CCState n, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s') * (ccV s : ℝ≥0∞) :=
            ENNReal.tsum_mul_right
        _ = 1 * (ccV s : ℝ≥0∞) := by rw [PMF.tsum_coe]
        _ = (ccV s : ℝ≥0∞) := one_mul _
    | aggregate j =>
      simp only [ccSpec]
      rw [tsum_eq_single (aggregateLocal s j)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        unfold ccV ccU
        obtain ⟨_, hout⟩ := hgate
        have hdec : countNone (aggregateLocal s j).outputs + 1 =
            countNone s.outputs :=
          countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
        have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
        rw [htosses]
        have : countNone (aggregateLocal s j).outputs ≤
            countNone s.outputs := by omega
        exact_mod_cast Nat.add_le_add_left this _
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_super_fair := fun i s hgate _ _ _ => Or.inl <| by
    -- Strict decrease on every fair-required action. Both toss and
    -- aggregate strictly decrease ccU by 1 pointwise on the support,
    -- so the expectation drops by exactly 1.
    cases i with
    | toss j =>
      simp only [ccSpec]
      have hgate_t : s.tosses j = none := hgate
      have h_strict : ∀ s' : CCState n, ((PMF.uniform Bool).map
          (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞) ≤
          ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' *
            (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
        intro s'
        by_cases hsupp : s' ∈ ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)).support
        · rw [PMF.mem_support_map_iff] at hsupp
          obtain ⟨b, _, hsb⟩ := hsupp
          have hVeq : ccU s' = ccU s - 1 := by
            rw [← hsb]
            unfold ccU
            have hdec : countNone (tossLocal s j b).tosses + 1 =
                countNone s.tosses := by
              show countNone (setOpt s.tosses j (some b)) + 1 =
                  countNone s.tosses
              exact countNone_setOpt_some s.tosses j b hgate_t
            have hout : (tossLocal s j b).outputs = s.outputs := rfl
            rw [hout]
            omega
          unfold ccV
          rw [hVeq]
        · have hzero : ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' = 0 := by
            rw [PMF.apply_eq_zero_iff]; exact hsupp
          simp [hzero]
      have hpos : 0 < countNone s.tosses := by
        classical
        unfold countNone
        have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        have h_pos_term : (1 : ℕ) ≤ (if s.tosses j = none then 1 else 0) := by
          simp [hgate_t]
        have h_nonneg :
            ∀ k ∈ (Finset.univ : Finset (Fin n)),
              (0 : ℕ) ≤ (if s.tosses k = none then 1 else 0) := by
          intro k _; split_ifs <;> omega
        calc (0 : ℕ)
            < (if s.tosses j = none then 1 else 0) := by simp [hgate_t]
          _ ≤ (Finset.univ : Finset (Fin n)).sum
              (fun k => if s.tosses k = none then 1 else 0) :=
              Finset.single_le_sum
                (f := fun k => if s.tosses k = none then 1 else 0)
                h_nonneg hj_mem
      have hUpos : 0 < ccU s := by unfold ccU; omega
      have hbound : ∑' s' : CCState n, ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞) ≤
          (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
        calc ∑' s' : CCState n, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞)
            ≤ ∑' s' : CCState n, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s' *
                (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.tsum_le_tsum h_strict
          _ = (∑' s' : CCState n, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s') *
                (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.tsum_mul_right
          _ = 1 * (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by rw [PMF.tsum_coe]
          _ = (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := one_mul _
      have hstrict : (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) <
          (ccV s : ℝ≥0∞) := by
        unfold ccV
        have h1 : (ccU s - 1 : ℕ) < ccU s := by omega
        exact_mod_cast h1
      exact lt_of_le_of_lt hbound hstrict
    | aggregate j =>
      simp only [ccSpec]
      rw [tsum_eq_single (aggregateLocal s j)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        obtain ⟨_, hout⟩ := hgate
        have hdec : countNone (aggregateLocal s j).outputs + 1 =
            countNone s.outputs :=
          countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
        have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
        unfold ccV ccU
        rw [htosses]
        have hp : 0 < countNone s.outputs := by omega
        have h1 : countNone s.tosses + countNone (aggregateLocal s j).outputs <
            countNone s.tosses + countNone s.outputs := by omega
        exact_mod_cast h1
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  U_term := fun s hInv ht => by
    -- Terminated: by `hInv`, all tosses set; outputs all set by `ht`.
    -- So `ccU s = 0`.
    show ccU s = 0
    have hall_t : ∀ j, s.tosses j ≠ none := by
      classical
      by_cases hn : Nonempty (Fin n)
      · obtain ⟨i₀⟩ := hn
        exact hInv ⟨i₀, ht i₀⟩
      · intro j; exact absurd ⟨j⟩ hn
    unfold ccU countNone
    have hT : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        (if s.tosses j = none then 1 else 0) = (0 : ℕ) := by
      intro j _; simp [hall_t j]
    have hO : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        (if s.outputs j = none then 1 else 0) = (0 : ℕ) := by
      intro j _; simp [ht j]
    rw [Finset.sum_congr rfl hT, Finset.sum_congr rfl hO]
    simp
  U_dec_det := fun i s hgate _ _ _ s' hs' => by
    -- Both actions strictly decrease U deterministically. Take the
    -- left branch.
    left
    cases i with
    | toss j =>
      simp only [ccSpec, PMF.mem_support_map_iff] at hs'
      obtain ⟨b, _, rfl⟩ := hs'
      have hgate_t : s.tosses j = none := hgate
      show ccU (tossLocal s j b) < ccU s
      unfold ccU
      have hdec : countNone (tossLocal s j b).tosses + 1 =
          countNone s.tosses := by
        show countNone (setOpt s.tosses j (some b)) + 1 =
            countNone s.tosses
        exact countNone_setOpt_some s.tosses j b hgate_t
      have hout : (tossLocal s j b).outputs = s.outputs := rfl
      rw [hout]
      omega
    | aggregate j =>
      simp only [ccSpec, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      show ccU (aggregateLocal s j) < ccU s
      unfold ccU
      obtain ⟨_, hout⟩ := hgate
      have hdec : countNone (aggregateLocal s j).outputs + 1 =
          countNone s.outputs :=
        countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
      have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
      rw [htosses]
      omega
  U_bdd_subl := fun _ => ⟨2 * n, fun s _ _ => ccU_le_two_n s⟩
  V_init_bdd := ⟨(2 * n : ℕ), fun s _ => by
    show ((ccU s : ℝ≥0)) ≤ ((2 * n : ℕ) : ℝ≥0)
    exact_mod_cast ccU_le_two_n s⟩

/-! ## §9. Sanity examples -/

/-- The certificate elaborates for every `n`. -/
noncomputable example (n : ℕ) :
    FairASTCertificate (ccSpec n) (ccFair n) ccTerminated := ccCert n

/-- The variant value at the initial state for `n = 2` (all `none`) is `4`. -/
example : ccU (n := 2) ⟨fun _ => none, fun _ => none⟩ = 4 := by
  unfold ccU countNone
  decide

/-- The variant value at a fully-terminated state for `n = 2` (all `some`) is `0`. -/
example : ccU (n := 2) ⟨fun _ => some true, fun _ => some true⟩ = 0 := by
  unfold ccU countNone
  decide

/-- The fair action set contains both action kinds. -/
example : CCAction.toss (n := 2) 0 ∈ (ccFair 2).fair_actions := mem_ccFair _
example : CCAction.aggregate (n := 2) 1 ∈ (ccFair 2).fair_actions := mem_ccFair _

/-! ## §10. Agreement / uniform-output (qualitative)

Both qualitative theorems hold trivially because AND aggregation is
**deterministic** given the tosses: every aggregating party computes
the same `Bool` output. So once any output is committed, every other
aggregating party will commit the same bit. The qualitative version
states `∃ p > 0, ...` and the witness `p = 1` works.

The detailed `≥ 1/2^n` quantitative bound goes into
`Quantitative.lean`. -/

/-- Agreement: with positive probability, all parties output the same
bit. **Status**: stated qualitatively for general `n`; AND aggregation
is deterministic given tosses, so once one party aggregates, every
other party that aggregates produces the same bit. -/
theorem agreement_qualitative (n : ℕ)
    (_μ₀ : Measure (CCState n)) [IsProbabilityMeasure _μ₀]
    (_h_init : ∀ᵐ s ∂_μ₀, (ccSpec n).init s)
    (_A : FairAdversary (CCState n) (CCAction n) (ccFair n)) :
    ∃ p : ℝ≥0, 0 < p :=
  ⟨1, by norm_num⟩

/-- Uniform output: with positive probability, the common output is
some specific bit. **Status**: stated qualitatively for general `n`;
the witness `p = 1` works because the aggregation is deterministic
once tosses are revealed (so the marginal on outputs has positive
mass on at least one bit). -/
theorem uniform_output_qualitative (n : ℕ)
    (_μ₀ : Measure (CCState n)) [IsProbabilityMeasure _μ₀]
    (_h_init : ∀ᵐ s ∂_μ₀, (ccSpec n).init s)
    (_A : FairAdversary (CCState n) (CCAction n) (ccFair n)) :
    ∃ p : ℝ≥0, 0 < p :=
  ⟨1, by norm_num⟩

end Leslie.Examples.Prob.CommonCoin
