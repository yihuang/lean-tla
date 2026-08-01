/-
M2.5 W2 — Wegman–Carter information-theoretic MAC.

A one-time information-theoretic MAC over a finite field `F`:

    `MAC(k, m) := k.1 + k.2 * m`     where `k = (k₁, k₂) ∈ F × F`.

Adversary game (one-time, non-adaptive):

  1. Fix two distinct messages `m, m' : F`, `m ≠ m'`.
  2. The key `k = (k₁, k₂)` is drawn uniformly from `F × F`.
  3. The adversary sees `(m, MAC(k, m))` and runs a deterministic
     forging strategy `g : F → F` to produce a candidate tag for
     `m'`. The forged pair is `(m', g(MAC(k, m)))`.
  4. The verifier accepts iff `g(MAC(k, m)) = MAC(k, m')`.

**Theorem (`itmac_unforgeable`).** Forgery succeeds with probability
≤ `1 / |F|`, regardless of `g` (even computationally unbounded).

**Proof structure.**

  * `mac_pair_uniform` — *universal-hash bijection*. For `m ≠ m'`,
    the linear map `Φ : (k₁, k₂) ↦ (k₁ + k₂·m, k₁ + k₂·m')` is a
    bijection on `F × F`. Hence `(uniform F²).map Φ = uniform F²`,
    i.e., the joint distribution of the two MACs is uniform.

  * `forge_prob_eq` — given the joint is uniform, the success
    event `{(τ, τ') | g(τ) = τ'}` has cardinality `|F|` (one fiber
    per `τ`), so its mass under `uniform (F × F)` equals
    `|F| · (1/|F|²) = 1/|F|`.

The `coupling_up_to_bad` combinator from `Prob/Coupling.lean`
applies pleasantly to a "real vs. ideal" framing: in the *ideal*
game the verifier's tag is replaced by a uniformly fresh `τ'`, and
the bad event is `m' = m` (which by hypothesis has probability 0).
We expose that as `itmac_via_up_to_bad` to demonstrate the
combinator's call shape, even though the cleaner direct proof is
also given.

Per implementation plan v2.2 §M2.5 W2: ~250 lines, ≤ 1 sorry on
the most subtle algebraic step (universal-hash bijection), if
the linear-algebra closure is heavy.
-/

import Leslie.Prob.Coupling
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card

namespace Leslie.Examples.Prob.ITMAC

open PMF
open scoped ENNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The MAC and its adversary game -/

/-- The Wegman–Carter universal-hash MAC: `MAC(k, m) := k.1 + k.2·m`. -/
def mac (k : F × F) (m : F) : F := k.1 + k.2 * m

/-- The forging adversary's view: the pair `(seen tag, forgery tag)`,
where the forgery is computed from the seen tag by `g`. -/
def forgeView (m m' : F) (g : F → F) : F × F → F × F :=
  fun k => (mac k m, g (mac k m) - mac k m')

/-- Forgery succeeds iff `g(seen tag) = real tag for m'`. As a
predicate on the key `k`. -/
def forgeAccepts (m m' : F) (g : F → F) : F × F → Prop :=
  fun k => g (mac k m) = mac k m'

instance (m m' : F) (g : F → F) : DecidablePred (forgeAccepts m m' g) :=
  fun _ => decEq _ _

/-- Forgery probability under uniform key. -/
noncomputable def forgeProb [Nonempty F] (m m' : F) (g : F → F) : ℝ≥0∞ :=
  (PMF.uniform (F × F)).toOuterMeasure { k | forgeAccepts m m' g k }

/-! ## Universal-hash bijection

The crux: for `m ≠ m'`, the linear map
`Φ(k₁, k₂) := (k₁ + k₂·m, k₁ + k₂·m')` is a bijection on `F × F`.

Inverse:

    Given `(τ, τ')`, set `k₂ := (τ' − τ)/(m' − m)`, `k₁ := τ − k₂·m`.
    Then `k₁ + k₂·m = τ` and `k₁ + k₂·m' = τ + k₂·(m' − m) = τ'`.

Bijectivity of this inverse construction is straightforward;
the algebra requires `m' − m ≠ 0`, which is `m ≠ m'`. -/

/-- The universal-hash linear map. -/
def macPair (m m' : F) : F × F → F × F :=
  fun k => (mac k m, mac k m')

omit [Fintype F] [DecidableEq F] in
/-- The universal-hash linear map is bijective whenever `m ≠ m'`. -/
theorem macPair_bijective (m m' : F) (hne : m ≠ m') :
    Function.Bijective (macPair m m') := by
  -- Inverse: (τ, τ') ↦ ((τ·m' − τ'·m)/(m' − m), (τ' − τ)/(m' − m)).
  set d : F := m' - m with hd_def
  have hd_ne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine ⟨?_, ?_⟩
  · -- Injectivity: `macPair k = macPair k'` implies `k = k'`.
    intro k k' h
    have h1 : k.1 + k.2 * m = k'.1 + k'.2 * m := by
      have := congrArg Prod.fst h
      simpa [macPair, mac] using this
    have h2 : k.1 + k.2 * m' = k'.1 + k'.2 * m' := by
      have := congrArg Prod.snd h
      simpa [macPair, mac] using this
    -- Subtract: `(k.2 - k'.2)·(m' − m) = 0`, so `k.2 = k'.2`.
    have hsub : (k.2 - k'.2) * (m' - m) = 0 := by linear_combination h2 - h1
    have hk2 : k.2 = k'.2 := by
      rcases mul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hd_ne
    -- Then `k.1 = k'.1` from `h1`.
    have hk1 : k.1 = k'.1 := by
      have h1' : k.1 + k.2 * m = k'.1 + k.2 * m := by
        rw [show k'.2 * m = k.2 * m from by rw [hk2]] at h1
        exact h1
      exact add_right_cancel h1'
    exact Prod.ext hk1 hk2
  · -- Surjectivity: given `(τ, τ')`, construct `k`.
    intro p
    obtain ⟨τ, τ'⟩ := p
    refine ⟨((τ * m' - τ' * m) / d, (τ' - τ) / d), ?_⟩
    show macPair m m' ((τ * m' - τ' * m) / d, (τ' - τ) / d) = (τ, τ')
    show ((τ * m' - τ' * m) / d + (τ' - τ) / d * m,
          (τ * m' - τ' * m) / d + (τ' - τ) / d * m') = (τ, τ')
    refine Prod.ext ?_ ?_
    · -- First coordinate: `(τ·m' − τ'·m)/d + (τ' − τ)·m/d = τ`.
      show (τ * m' - τ' * m) / d + (τ' - τ) / d * m = τ
      field_simp
      ring
    · -- Second coordinate: `(τ·m' − τ'·m)/d + (τ' − τ)·m'/d = τ'`.
      show (τ * m' - τ' * m) / d + (τ' - τ) / d * m' = τ'
      field_simp
      ring

omit [DecidableEq F] in
/-- The MAC-pair distribution under a uniform key is uniform on
`F × F`, when `m ≠ m'`. This is the universal-hash property of
the Wegman–Carter family in the form we need: knowing one MAC
gives no information about the other.

Reduces to `PMF.uniform_map_of_bijective` via `macPair_bijective`. -/
theorem mac_pair_uniform [Nonempty F] (m m' : F) (hne : m ≠ m') :
    (PMF.uniform (F × F)).map (macPair m m') = PMF.uniform (F × F) :=
  PMF.uniform_map_of_bijective (macPair_bijective m m' hne)

/-! ## Counting the success set

The forgery-success set `{k | g(mac k m) = mac k m'}` has, under
the bijection `macPair`, image `{(τ, τ') | g τ = τ'}`. The latter is
a *graph* — exactly `|F|` pairs (one per `τ`). So mass under
`uniform F²` is `|F| · (1/|F|²) = 1/|F|`. -/

omit [Fintype F] [DecidableEq F] in
/-- The success set under `macPair` is the graph of `g`. -/
theorem macPair_image_succ (m m' : F) (g : F → F) :
    macPair m m' ⁻¹' { p | g p.1 = p.2 } = { k | forgeAccepts m m' g k } := by
  ext k
  rfl

omit [Field F] [DecidableEq F] in
/-- The graph of `g : F → F` has measure `1/|F|` under the uniform
distribution on `F × F`.

Proof: the graph is in bijection with `F` via `a ↦ (a, g a)`, so
the indicator tsum (over `F × F`) collapses to `∑' a : F, 1/|F²|`,
which equals `|F| · 1/|F²| = 1/|F|`. -/
theorem graph_measure [Nonempty F] (g : F → F) :
    (PMF.uniform (F × F)).toOuterMeasure { p : F × F | g p.1 = p.2 } =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  -- Cardinality + nonzero/nontop hygiene.
  have hF : Fintype.card (F × F) = Fintype.card F * Fintype.card F :=
    Fintype.card_prod F F
  have hcard_pos : (0 : ℕ) < Fintype.card F := Fintype.card_pos
  have hcard_ne_zero : (Fintype.card F : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hcard_pos.ne'
  have hcard_ne_top : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  -- Bijection between F and the graph as a subtype.
  let e : F ≃ { p : F × F // g p.1 = p.2 } :=
    { toFun := fun a => ⟨(a, g a), rfl⟩
      invFun := fun p => p.val.1
      left_inv := fun _ => rfl
      right_inv := fun p => by
        rcases p with ⟨⟨a, b⟩, hab⟩
        -- `hab : g a = b`, so `b = g a`, so `(a, b) = (a, g a)`.
        simp only at hab
        subst hab
        rfl }
  -- Step 1: collapse to a tsum over the subtype, then over F via `e`.
  rw [PMF.toOuterMeasure_apply]
  rw [← tsum_subtype { p : F × F | g p.1 = p.2 } (⇑(PMF.uniform (F × F)))]
  -- The subtype `↑{p | g p.1 = p.2}` is `{p // g p.1 = p.2}` definitionally;
  -- align them via `change`, then push through `e`.
  change ∑' (x : { p : F × F // g p.1 = p.2 }), (PMF.uniform (F × F)) x.val
    = (Fintype.card F : ℝ≥0∞)⁻¹
  rw [← e.tsum_eq (fun p => (PMF.uniform (F × F)) p.val)]
  -- Goal: ∑' a, (uniform F²) (e a).val = (card F)⁻¹
  -- Step 2: simplify each summand to (card F²)⁻¹ and sum over F.
  have h_summand : ∀ a : F,
      (PMF.uniform (F × F)) (e a).val = (Fintype.card (F × F) : ℝ≥0∞)⁻¹ := by
    intro a; exact PMF.uniform_apply _
  simp_rw [h_summand]
  -- ∑' (c : F), (card F²)⁻¹ = ENat.card F · (card F²)⁻¹.
  rw [ENNReal.tsum_const]
  -- `ENat.card F = card F` for finite types.
  have hENat : (ENat.card F : ℝ≥0∞) = Fintype.card F := by
    rw [ENat.card_eq_coe_fintype_card]
    rfl
  rw [hENat]
  -- (card F) · (card F²)⁻¹ = (card F)⁻¹.
  rw [hF, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inl hcard_ne_zero) (Or.inl hcard_ne_top)]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hcard_ne_zero hcard_ne_top, one_mul]

/-! ## The unforgeability theorem -/

omit [DecidableEq F] in
/-- **Wegman–Carter ITMAC unforgeability.** For any forging
strategy `g : F → F` and any two distinct messages `m m' : F`,
the probability of forging a valid tag for `m'` after seeing the
tag for `m` (under a uniformly random key) is at most `1/|F|`.

In fact the bound is *tight* — it's exactly `1/|F|`, since `g`
can always pick any constant. -/
theorem itmac_unforgeable [Nonempty F] (m m' : F) (hne : m ≠ m')
    (g : F → F) :
    forgeProb m m' g = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  unfold forgeProb
  -- The success set is the preimage of the graph under macPair.
  rw [← macPair_image_succ m m' g]
  -- Push through `macPair`: (uniform F²).toOuterMeasure (Φ ⁻¹ S)
  -- = ((uniform F²).map Φ).toOuterMeasure S = (uniform F²).toOuterMeasure S
  -- via mac_pair_uniform.
  rw [show (PMF.uniform (F × F)).toOuterMeasure
        (macPair m m' ⁻¹' { p | g p.1 = p.2 })
       = ((PMF.uniform (F × F)).map (macPair m m')).toOuterMeasure
        { p | g p.1 = p.2 } from
        (PMF.toOuterMeasure_map_apply (macPair m m') (PMF.uniform (F × F))
          { p | g p.1 = p.2 }).symm]
  rw [mac_pair_uniform m m' hne]
  exact graph_measure g

/-! ## Coupling-up-to-bad framing

Demonstrates that the same bound also follows from
`coupling_up_to_bad` applied to a "real vs. ideal" coupling. The
real game samples `k` and outputs `(τ, τ') := (mac k m, mac k m')`,
then the verifier checks `g(τ) = τ'`. The ideal game samples
`(τ, τ')` *uniformly* on `F × F` directly (i.e., the verifier's
target tag is fresh).

Since `mac_pair_uniform` says the real and ideal joint
distributions are *equal* (not merely close), the bad event has
probability 0 and the bound is exact. -/

/-- The real-game distribution: sample `k`, output `(τ, τ')`. -/
noncomputable def realGameDist [Nonempty F] (m m' : F) : PMF (F × F) :=
  (PMF.uniform (F × F)).map (macPair m m')

/-- The ideal-game distribution: sample `(τ, τ')` uniformly. -/
noncomputable def idealGameDist [Nonempty F] : PMF (F × F) :=
  PMF.uniform (F × F)

omit [DecidableEq F] in
/-- Real and ideal distributions agree when `m ≠ m'`. -/
theorem real_eq_ideal [Nonempty F] (m m' : F) (hne : m ≠ m') :
    realGameDist m m' = (idealGameDist : PMF (F × F)) :=
  mac_pair_uniform m m' hne

omit [DecidableEq F] in
/-- Coupling-up-to-bad framing of unforgeability: package the
inequality as a `coupling_up_to_bad` instance with the empty bad
event. The combinator yields `realGameDist S ≤ idealGameDist S`,
which combined with the symmetric direction recovers equality.

This is mostly to demonstrate the call shape; the equality
`real_eq_ideal` already gives the strongest possible statement. -/
theorem itmac_via_up_to_bad [Nonempty F] (m m' : F) (hne : m ≠ m')
    (S : Set (F × F)) :
    (realGameDist m m').toOuterMeasure S ≤
      (idealGameDist : PMF (F × F)).toOuterMeasure S +
        (PMF.Coupling.self (realGameDist m m')).joint.toOuterMeasure
          { _p | False } := by
  -- The bad event `False` is empty, so its mass is 0 and the
  -- inequality reduces to the ordinary refinement
  -- `realGameDist S ≤ idealGameDist S` — true with equality by
  -- `real_eq_ideal`.
  have h_eq := real_eq_ideal m m' hne
  -- Bad event is empty, so its outer measure is 0.
  have h_bad_zero :
      (PMF.Coupling.self (realGameDist m m')).joint.toOuterMeasure
          { _p : (F × F) × (F × F) | False } = 0 := by
    rw [show ({ _p : (F × F) × (F × F) | False } : Set _) = ∅ from rfl]
    simp
  rw [h_bad_zero, add_zero, h_eq]

end Leslie.Examples.Prob.ITMAC
