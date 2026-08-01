/-
M1 W3 — Polynomial uniformity library (foundations).

`uniformWithFixedZero d s` is the uniform distribution over polynomials
of degree ≤ d with constant term `s`. The headline theorem
`evals_uniform` says: for `pts ⊂ F` with `|pts| ≤ d`, `0 ∉ pts`, and
`d + 1 ≤ Fintype.card F`, the joint distribution of evaluations
`(f(p))_{p∈pts}` is uniform on `pts → F`. This is the algebraic core
of Shamir secrecy (M1 W4).

The proof of `evals_uniform` reduces to a direct injectivity argument:
for `pts.card = d`, the eval map `(Fin d → F) → (pts → F)` is
injective (any two coefficient vectors agreeing on `pts ∪ {0}` —
which has size `d + 1` — produce a polynomial of degree ≤ d with
`d + 1` zeros, hence is zero), and bijectivity follows from card
equality. For `pts.card < d`, extend `pts` to `pts'` of size `d` in
`F \ ({0} ∪ pts)` (requiring `d + 1 ≤ Fintype.card F`), apply the
equal-card case to `pts'`, then project — using a constant-fiber
surjection helper.

Status (M1 W3, sorry-free):
  * Helper `PMF.uniform_map_of_bijective` proved.
  * Helper `PMF.uniform_map_of_surjective_constFiber` proved
    (pushforward under constant-fiber surjection is uniform).
  * `uniformWithFixedZero`, `uniformBivariateWithFixedZero` defined.
  * `evals_uniform` proved (with extra hypothesis `d + 1 ≤ Fintype.card F`).
  * `bivariate_evals_uniform` proved (row-then-column reduction to
    univariate `evals_uniform`; same field-size hypothesis applied
    to each axis).

Per implementation plan v2.2 §M1 W3.
-/

import Leslie.Prob.PMF
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Fintype.EquivFin

namespace Leslie.Prob.Polynomial

open scoped ENNReal

/-! ## Pushforward of uniform under a bijection

Mathlib doesn't expose this directly; it is the workhorse for every
"uniform-stays-uniform-under-bijection" lemma below. Proof: the
forward marginal at each codomain point is exactly the source's
mass at the unique preimage, which is `1/|α| = 1/|β|`. -/

theorem _root_.PMF.uniform_map_of_bijective
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {f : α → β} (hf : Function.Bijective f) :
    (PMF.uniform α).map f = PMF.uniform β := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.uniform_apply]
  obtain ⟨a, ha⟩ := hf.surjective b
  have hcard : (Fintype.card α : ℝ≥0∞) = Fintype.card β :=
    congrArg Nat.cast (Fintype.card_of_bijective hf)
  rw [tsum_eq_single a]
  · simp [ha, hcard]
  · intro a' ha'
    have : f a' ≠ b := fun h_eq =>
      ha' (hf.injective (h_eq.trans ha.symm))
    simp [Ne.symm this]

/-! ## Pushforward of uniform under a constant-fiber surjection

If every fiber of `g : α → β` has the same size `k > 0`, then the
pushforward of `uniform α` under `g` is `uniform β`. Generalizes
`uniform_map_of_bijective` (where `k = 1`). -/

theorem _root_.PMF.uniform_map_of_surjective_constFiber
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β]
    (g : α → β) (k : ℕ) (hk : 0 < k)
    (h_fib : ∀ b : β, (Finset.univ.filter (fun a => g a = b)).card = k) :
    (PMF.uniform α).map g = PMF.uniform β := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  simp only [PMF.uniform_apply]
  have h_α_eq : Fintype.card α = Fintype.card β * k := by
    have hsumeq : (Finset.univ : Finset α).card =
        ∑ b : β, (Finset.univ.filter (fun a => g a = b)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext a
        simp
      · intro x _ y _ hxy
        simp only [Function.onFun]
        rw [Finset.disjoint_filter]
        intro a _ ha
        exact fun ha' => hxy (ha.symm.trans ha')
    have h2 : (Finset.univ : Finset α).card = Fintype.card α := rfl
    rw [h2] at hsumeq
    rw [hsumeq, Finset.sum_congr rfl (fun b _ => h_fib b), Finset.sum_const,
        Finset.card_univ, smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.univ.filter (fun a => g a = b))
      (fun a ha => by simp at ha; simp [Ne.symm ha])]
  have hsum : ∀ a ∈ (Finset.univ.filter (fun a => g a = b)),
      (if b = g a then ((Fintype.card α : ℝ≥0∞)⁻¹) else 0) =
        ((Fintype.card α : ℝ≥0∞)⁻¹) := by
    intro a ha
    simp at ha
    simp [ha]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, h_fib b, h_α_eq]
  rw [nsmul_eq_mul]
  push_cast
  rw [ENNReal.mul_inv]
  · rw [← mul_assoc, mul_comm (k : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · exact_mod_cast hk.ne'
    · simp
  · left; exact_mod_cast (Fintype.card_pos).ne'
  · left; simp

/-! ## Pi-lift of a uniform pushforward

If `h : α → β` pushes forward `uniform α` to `uniform β`, then for any
finite nonempty index `ι`, the per-coordinate map `f ↦ (i ↦ h (f i))`
pushes forward `uniform (ι → α)` to `uniform (ι → β)`.

Proof sketch: from `(uniform α).map h = uniform β`, every fiber of `h`
has the same size `k = |α|/|β|`. For the per-coordinate map
`Φ : (ι → α) → (ι → β)`, the fiber over `g` is the product over `i` of
the per-coordinate fibers `{a | h a = g i}`, hence has size `k^|ι|`,
constant in `g`. Conclude via `uniform_map_of_surjective_constFiber`. -/

theorem _root_.PMF.uniform_pi_map_of_uniform_map
    {ι α β : Type*}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β]
    {h : α → β} (h_uniform : (PMF.uniform α).map h = PMF.uniform β) :
    (PMF.uniform (ι → α)).map (fun f i => h (f i)) = PMF.uniform (ι → β) := by
  -- Extract the constant fiber size of `h` from the PMF equation.
  -- For any b : β, the fiber {a | h a = b} has size |α|/|β|.
  have h_card_β_pos : 0 < Fintype.card β := Fintype.card_pos
  have h_card_α_pos : 0 < Fintype.card α := Fintype.card_pos
  -- The fiber size for h.
  have h_fib_h : ∀ b : β,
      (Finset.univ.filter (fun a : α => h a = b)).card * Fintype.card β
        = Fintype.card α := by
    intro b
    have h_pmf : ((PMF.uniform α).map h) b = (PMF.uniform β) b := by rw [h_uniform]
    simp only [PMF.map_apply, PMF.uniform_apply] at h_pmf
    -- Reduce the tsum to a sum over the fiber.
    have h_sum : (∑' (a : α), if b = h a then ((Fintype.card α : ℝ≥0∞))⁻¹ else 0)
        = (Finset.univ.filter (fun a : α => h a = b)).card *
            ((Fintype.card α : ℝ≥0∞))⁻¹ := by
      rw [tsum_eq_sum (s := Finset.univ.filter (fun a => h a = b))
          (fun a ha => by simp at ha; simp [Ne.symm ha])]
      have hsum_eq : ∀ a ∈ (Finset.univ.filter (fun a : α => h a = b)),
          (if b = h a then ((Fintype.card α : ℝ≥0∞))⁻¹ else 0)
            = ((Fintype.card α : ℝ≥0∞))⁻¹ := by
        intro a ha; simp at ha; simp [ha]
      rw [Finset.sum_congr rfl hsum_eq, Finset.sum_const, nsmul_eq_mul]
    rw [h_sum] at h_pmf
    -- h_pmf : (filter.card : ℝ≥0∞) * |α|⁻¹ = |β|⁻¹.
    have hα_ne : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast h_card_α_pos.ne'
    have hα_ne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hβ_ne : (Fintype.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast h_card_β_pos.ne'
    have hβ_ne_top : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- Multiply both sides by |α| to get filter.card = |α|/|β|, then by |β| to clear.
    have h_pmf2 :
        ((Finset.univ.filter (fun a : α => h a = b)).card : ℝ≥0∞) * Fintype.card β
          = Fintype.card α := by
      -- From h_pmf : k * |α|⁻¹ = |β|⁻¹.
      -- Multiply both sides by |α|: k = |α| * |β|⁻¹.
      have h_pmf' : ((Finset.univ.filter (fun a : α => h a = b)).card : ℝ≥0∞)
          = (Fintype.card β : ℝ≥0∞)⁻¹ * Fintype.card α := by
        have := congrArg (· * (Fintype.card α : ℝ≥0∞)) h_pmf
        simp only at this
        rw [mul_assoc, ENNReal.inv_mul_cancel hα_ne hα_ne_top, mul_one] at this
        exact this
      -- Multiply by |β|.
      rw [h_pmf']
      rw [mul_comm ((Fintype.card β : ℝ≥0∞)⁻¹), mul_assoc,
          ENNReal.inv_mul_cancel hβ_ne hβ_ne_top, mul_one]
    -- Cast back to ℕ.
    have h_pmf3 :
        (((Finset.univ.filter (fun a : α => h a = b)).card * Fintype.card β : ℕ) : ℝ≥0∞)
          = ((Fintype.card α : ℕ) : ℝ≥0∞) := by
      push_cast; exact h_pmf2
    exact_mod_cast h_pmf3
  -- Conclude |β| ∣ |α| and the per-fiber size k.
  have h_β_dvd_α : Fintype.card β ∣ Fintype.card α := by
    obtain ⟨b⟩ := (inferInstance : Nonempty β)
    exact ⟨_, (h_fib_h b).symm.trans (by ring)⟩
  set k : ℕ := Fintype.card α / Fintype.card β with hk_def
  have hk_card : Fintype.card α = Fintype.card β * k := by
    rw [hk_def, Nat.mul_div_cancel' h_β_dvd_α]
  have hk_fib : ∀ b : β,
      (Finset.univ.filter (fun a : α => h a = b)).card = k := by
    intro b
    have := h_fib_h b
    rw [hk_card] at this
    have h_eq : (Finset.univ.filter (fun a : α => h a = b)).card * Fintype.card β
        = k * Fintype.card β := by rw [this]; ring
    exact Nat.eq_of_mul_eq_mul_right h_card_β_pos h_eq
  have hk_pos : 0 < k := by
    by_contra hk0
    push_neg at hk0
    interval_cases k
    rw [Nat.mul_zero] at hk_card
    exact absurd hk_card h_card_α_pos.ne'
  -- Now the Pi map: each fiber over g : ι → β has size k^|ι|.
  have h_pow_pos : 0 < k ^ Fintype.card ι := pow_pos hk_pos _
  apply PMF.uniform_map_of_surjective_constFiber (fun (f : ι → α) i => h (f i))
      (k ^ Fintype.card ι) h_pow_pos
  intro g
  -- Fiber: {f : ι → α | (fun i => h (f i)) = g} = {f | ∀ i, h (f i) = g i}.
  -- This corresponds to Fintype.piFinset (fun i => univ.filter (h · = g i)).
  have h_fib_eq :
      Finset.univ.filter (fun f : ι → α => (fun i => h (f i)) = g)
        = Fintype.piFinset (fun i => Finset.univ.filter (fun a : α => h a = g i)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Fintype.mem_piFinset]
    constructor
    · intro hf i
      have := congrFun hf i
      simp [this]
    · intro hf
      funext i
      exact (hf i)
  rw [h_fib_eq, Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun i _ => hk_fib (g i))]
  rw [Finset.prod_const, Finset.card_univ]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Uniform polynomial with fixed constant term -/

/-- A uniform random polynomial of degree ≤ d with constant term `s`,
realized by sampling the coefficients of `X, X², …, X^d` uniformly
from `F`. -/
noncomputable def uniformWithFixedZero (d : ℕ) (s : F) :
    PMF (_root_.Polynomial F) :=
  (PMF.uniform (Fin d → F)).map fun coefs =>
    Polynomial.C s + ∑ i : Fin d,
      Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)

/-- A uniform random bivariate polynomial of bidegree ≤ (dx, dy)
with constant term `s`. Built as `Polynomial (Polynomial F)` —
the inner ring is `Polynomial F` and its constants are coefficients
in the outer `X` variable.

⚠ **Degenerate for VSS.** This distribution forces *every* axis
coefficient (both `(i, 0)` for `i ≥ 1` and `(0, j)` for `j ≥ 1`)
to zero, so `f(x, 0) = s` for **all** `x` and `f(0, y) = s` for
all `y`. See `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` §9–§10.
For the literature-standard distribution, use
`uniformBivariateFullWithFixedZero` below. -/
noncomputable def uniformBivariateWithFixedZero (dx dy : ℕ) (s : F) :
    PMF (_root_.Polynomial (_root_.Polynomial F)) :=
  (PMF.uniform (Fin dx → Fin dy → F)).map fun coefs =>
    Polynomial.C (Polynomial.C s) + ∑ i : Fin dx, ∑ j : Fin dy,
      Polynomial.C (Polynomial.C (coefs i j)) *
        Polynomial.X ^ (i.val + 1) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1)

/-- A uniform random bivariate polynomial of bidegree ≤ `(dx, dy)`
with **only** the constant `(0, 0)` coefficient pinned to `s`. All
other `(dx + 1) * (dy + 1) - 1` coefficients are independently and
uniformly distributed in `F`.

Sampled in three independent pieces:
* an *interior* matrix `coefs : Fin dx → Fin dy → F` —
  the coefficients at `(i.val + 1, j.val + 1)` (i.e. both axes ≥ 1);
* an *axis-X* vector `axisX : Fin dx → F` —
  the coefficients at `(i.val + 1, 0)`;
* an *axis-Y* vector `axisY : Fin dy → F` —
  the coefficients at `(0, j.val + 1)`.

This is the literature-standard distribution for bivariate Shamir
secret-sharing: under it, `f(α, 0) = s + ∑_{i} axisX_i α^{i+1}` is
a genuine degree-`dx` Shamir polynomial in `α` with constant
term `s`.  Compare with `uniformBivariateWithFixedZero` (axis-zero
variant) which forces every axis coefficient to zero — degenerate
for VSS purposes; see `AVSS-MODEL-NOTES.md` §9–§10. -/
noncomputable def uniformBivariateFullWithFixedZero (dx dy : ℕ) (s : F) :
    PMF (_root_.Polynomial (_root_.Polynomial F)) :=
  (PMF.uniform ((Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F))).map
    fun ⟨coefs, axisX, axisY⟩ =>
      Polynomial.C (Polynomial.C s) +
      (∑ i : Fin dx, Polynomial.C (Polynomial.C (axisX i)) *
        Polynomial.X ^ (i.val + 1)) +
      (∑ j : Fin dy, Polynomial.C (Polynomial.C (axisY j)) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
      ∑ i : Fin dx, ∑ j : Fin dy,
        Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X ^ (i.val + 1) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)

/-! ## Headline theorems

Both `evals_uniform` and `bivariate_evals_uniform` are proved
sorry-free below.

The univariate `evals_uniform` argument: the eval map
`(Fin d → F) → (pts → F)` is injective in the equal-cardinality
case (any two coefficient vectors agreeing on `pts ∪ {0}`, of size
`d + 1`, produce a polynomial of degree ≤ d with `d + 1` zeros,
which is zero), and bijectivity follows from card equality.
The strict-subcardinality case extends `pts` to a set of size `d`
inside `F \ ({0} ∪ pts)` (using `d + 1 ≤ Fintype.card F`) and
projects via a constant-fiber surjection.

`bivariate_evals_uniform` reduces to univariate `evals_uniform`
applied row-then-column, using the factoring
`f(p,q) = s + ∑_i (∑_j coefs(i,j) * q^(j+1)) * p^(i+1)`. -/

/-! ## Injectivity of the evaluation map (equal-cardinality case)

For `pts.card = d` with `0 ∉ pts`, the map sending coefficients
`(c_0, …, c_{d-1})` to the evaluation tuple
`p ↦ s + ∑ i, c_i * p^(i+1)` is injective. Proof: if two coefficient
vectors agree on `pts`, then `Δ(X) := ∑ (c1 i - c2 i) * X^(i+1)` has
degree ≤ d and vanishes on `pts ∪ {0}` (size `d + 1`), hence is zero,
hence all its coefficients agree. -/

omit [Fintype F] in
theorem eval_map_injective (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card = d) (h_nz : (0 : F) ∉ pts) :
    Function.Injective fun (coefs : Fin d → F) =>
        fun (p : pts) =>
          (Polynomial.C s + ∑ i : Fin d,
            Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)).eval p.val := by
  intro c1 c2 h_eq
  set Δ : Polynomial F :=
      ∑ i : Fin d, Polynomial.C (c1 i - c2 i) * Polynomial.X ^ (i.val + 1) with hΔ
  -- Δ vanishes at every p ∈ pts (subtract the eval-equality at p).
  have h_eval_pts : ∀ p ∈ pts, Δ.eval p = 0 := by
    intro p hp
    have hh := congrFun h_eq ⟨p, hp⟩
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finset_sum,
               Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hh
    have hh' : ∑ x, c1 x * p ^ (x.val + 1) = ∑ x, c2 x * p ^ (x.val + 1) :=
      add_left_cancel hh
    rw [hΔ, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
               Polynomial.eval_X, sub_mul]
    rw [Finset.sum_sub_distrib, hh']
    ring
  -- Δ has zero constant term, so it vanishes at 0.
  have h_eval_0 : Δ.eval 0 = 0 := by
    rw [hΔ, Polynomial.eval_finset_sum]
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  -- Δ has degree ≤ d.
  have h_deg : Δ.degree ≤ (d : WithBot ℕ) := by
    rw [hΔ]
    apply le_trans (Polynomial.degree_sum_le _ _)
    rw [Finset.sup_le_iff]
    intro i _
    apply le_trans (Polynomial.degree_C_mul_X_pow_le _ _)
    exact_mod_cast Nat.succ_le_iff.mpr i.is_lt
  -- pts ∪ {0} has size d + 1, so Δ.degree < (d+1) = card (pts ∪ {0}).
  set pts0 : Finset F := insert (0 : F) pts with hpts0
  have h_pts0_card : pts0.card = d + 1 := by
    rw [hpts0, Finset.card_insert_of_notMem h_nz, h_card]
  have h_eval_pts0 : ∀ x ∈ pts0, Δ.eval x = 0 := by
    intro x hx
    rw [hpts0, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact h_eval_0
    · exact h_eval_pts x hx
  have h_deg_lt : Δ.degree < (pts0.card : WithBot ℕ) := by
    rw [h_pts0_card]
    calc Δ.degree ≤ (d : WithBot ℕ) := h_deg
      _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self d
  have hΔ_zero : Δ = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero pts0 h_deg_lt h_eval_pts0
  -- Read off coefficients: each coefficient of Δ at degree (i+1) equals c1 i - c2 i.
  funext i
  have h_coef : Δ.coeff (i.val + 1) = 0 := by rw [hΔ_zero]; simp
  rw [hΔ, Polynomial.finset_sum_coeff] at h_coef
  have h_unique : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      (Polynomial.C (c1 j - c2 j) * Polynomial.X ^ (j.val + 1)).coeff (i.val + 1)
        = if j = i then c1 i - c2 i else 0 := by
    intro j _
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases h : j = i
    · subst h; simp
    · simp only [if_neg h]
      have hne : i.val + 1 ≠ j.val + 1 := by
        intro heq; apply h; apply Fin.ext; omega
      rw [if_neg hne]
  rw [Finset.sum_congr rfl h_unique, Finset.sum_ite_eq' Finset.univ i] at h_coef
  simp at h_coef
  exact sub_eq_zero.mp h_coef

/-! ## Equal-cardinality case of `evals_uniform`

When `pts.card = d`, the eval map is a bijection between
`Fin d → F` and `pts → F` (both of size `(card F)^d`). Apply
`PMF.uniform_map_of_bijective`. -/

theorem evals_uniform_eq_card (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card = d) (h_nz : (0 : F) ∉ pts) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F) := by
  unfold uniformWithFixedZero
  rw [PMF.map_comp]
  -- Card equality: (card F)^d = (card F)^pts.card.
  have h_card_eq : Fintype.card (Fin d → F) = Fintype.card (pts → F) := by
    rw [Fintype.card_fun, Fintype.card_fun]
    simp [Fintype.card_coe, h_card]
  -- Injectivity from eval_map_injective.
  have h_inj : Function.Injective fun (coefs : Fin d → F) =>
      fun (p : pts) =>
        Polynomial.eval p.val (Polynomial.C s + ∑ i : Fin d,
          Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) :=
    eval_map_injective d s pts h_card h_nz
  -- Bijectivity from inj + card equality.
  have h_bij : Function.Bijective fun (coefs : Fin d → F) =>
      fun (p : pts) =>
        Polynomial.eval p.val (Polynomial.C s + ∑ i : Fin d,
          Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨h_inj, h_card_eq⟩
  exact PMF.uniform_map_of_bijective h_bij

/-- Joint of evaluations at `pts` is uniform on `pts → F` whenever
`|pts| ≤ d`, `0 ∉ pts`, and the field is large enough
(`d + 1 ≤ Fintype.card F`). The latter is needed so that we can
extend `pts` to size `d` within `F \ {0}` for the marginalization
argument when `pts.card < d`.

For `pts.card = d`, the eval map is a bijection (via injectivity
+ cardinality, see `evals_uniform_eq_card`).

For `pts.card < d`, extend `pts` to a `pts'` of size `d` in
`F \ ({0} ∪ pts)`, apply the equal-card case to `pts'`, then project
the uniform on `pts' → F` down to `pts → F` via restriction (which
is a constant-fiber surjection of fiber size
`(Fintype.card F) ^ (d - pts.card)`).

For `d = 0` (so also `pts.card = 0`): both sides are `pure (·)` on
the empty function — handled directly. -/
theorem evals_uniform (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card ≤ d) (h_nz : (0 : F) ∉ pts)
    (h_F : d + 1 ≤ Fintype.card F) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F) := by
  -- Extend pts to pts' of size d within F \ ({0} ∪ pts).
  -- The set F \ ({0} ∪ pts) has at least `d - pts.card` elements
  -- (using `d + 1 ≤ Fintype.card F`).
  have h_avail : d - pts.card ≤ (Finset.univ \ (insert (0 : F) pts)).card := by
    have h_eq : (Finset.univ \ (insert (0 : F) pts)).card =
        Fintype.card F - (pts.card + 1) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Finset.card_insert_of_notMem h_nz]
    rw [h_eq]; omega
  obtain ⟨extras, h_extras_sub, h_extras_card⟩ :=
    Finset.exists_subset_card_eq h_avail
  -- extras is disjoint from {0} ∪ pts.
  have h_extras_disj_excluded : Disjoint extras (insert (0 : F) pts) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    have ha' : a ∈ Finset.univ \ (insert (0 : F) pts) := h_extras_sub ha
    rw [Finset.mem_sdiff] at ha'
    apply ha'.2
    rw [heq]; exact hb
  have h_extras_disj_pts : Disjoint extras pts :=
    Disjoint.mono_right (Finset.subset_insert _ _) h_extras_disj_excluded
  have h_extras_no_zero : (0 : F) ∉ extras := by
    intro h0
    have : (0 : F) ∈ Finset.univ \ (insert (0 : F) pts) := h_extras_sub h0
    rw [Finset.mem_sdiff, Finset.mem_insert] at this
    exact this.2 (Or.inl rfl)
  set pts' : Finset F := pts ∪ extras with hpts'_def
  -- Properties of pts'.
  have hpts'_card : pts'.card = d := by
    rw [hpts'_def, Finset.card_union_of_disjoint h_extras_disj_pts.symm,
        h_extras_card]
    omega
  have hpts'_nz : (0 : F) ∉ pts' := by
    rw [hpts'_def, Finset.mem_union]
    rintro (h | h)
    · exact h_nz h
    · exact h_extras_no_zero h
  have h_pts_sub_pts' : pts ⊆ pts' := by
    rw [hpts'_def]; exact Finset.subset_union_left
  -- Restriction map (pts' → F) → (pts → F) given by composition with inclusion.
  let restr : (pts' → F) → (pts → F) := fun g p => g ⟨p.val, h_pts_sub_pts' p.property⟩
  -- Factor: eval at pts = restr ∘ (eval at pts').
  have h_factor :
      (fun (f : Polynomial F) (p : pts) => f.eval p.val) =
        restr ∘ (fun (f : Polynomial F) (p' : pts') => f.eval p'.val) := by
    funext f p
    rfl
  rw [h_factor, ← PMF.map_comp]
  -- Apply equal-card case to pts'.
  rw [evals_uniform_eq_card d s pts' hpts'_card hpts'_nz]
  -- Now need: (PMF.uniform (pts' → F)).map restr = PMF.uniform (pts → F).
  -- Apply uniform_map_of_surjective_constFiber.
  -- Fiber of restr at any r : pts → F has size (Fintype.card F)^(extras.card)
  -- (extensions of r to extras).
  have h_card_F_pos : 0 < Fintype.card F := by linarith
  have h_extras_pow_pos : 0 < (Fintype.card F) ^ extras.card := pow_pos h_card_F_pos _
  haveI : Nonempty (pts' → F) := by
    have hF : Nonempty F := ⟨0⟩
    exact ⟨fun _ => 0⟩
  haveI : Nonempty (pts → F) := ⟨fun _ => 0⟩
  -- The fiber computation: fix r : pts → F, count g : pts' → F with restr g = r.
  -- Such g is determined by r and (g restricted to extras), giving (card F)^extras.card.
  apply PMF.uniform_map_of_surjective_constFiber restr
      ((Fintype.card F) ^ extras.card) h_extras_pow_pos
  intro r
  -- We need: |{g : pts' → F | restr g = r}| = (card F)^extras.card.
  -- Build a bijection between this fiber and (extras → F).
  -- Define the equivalence: g ↦ (extras ↦ g (i with hi : i ∈ pts')).
  -- For p ∈ pts', either p ∈ pts (and g p = r ⟨p, _⟩) or p ∈ extras.
  -- The free degrees of freedom are exactly g restricted to extras.
  classical
  -- Counting: cardinality of fiber = (Fintype.card F)^extras.card.
  -- Use Finset.card_eq via an explicit bijection with extras → F.
  have h_fib_card :
      (Finset.univ.filter (fun (g : pts' → F) => restr g = r)).card =
        (Fintype.card F) ^ extras.card := by
    -- Use an explicit equivalence between fiber and (extras → F).
    have h_pow : (Fintype.card F) ^ extras.card = Fintype.card (extras → F) := by
      rw [Fintype.card_fun, Fintype.card_coe]
    -- Reduce the goal to Fintype.card on the subtype.
    have h_filter_card_eq :
        (Finset.univ.filter (fun (g : pts' → F) => restr g = r)).card =
        Fintype.card { g : pts' → F // restr g = r } := by
      rw [Fintype.card_subtype]
    rw [h_filter_card_eq, h_pow]
    -- Now: card { g // restr g = r } = card (extras → F).
    -- Build a bijection φ.
    let φ : { g : pts' → F // restr g = r } → (extras → F) :=
      fun ⟨g, _⟩ e =>
        g ⟨e.val, by rw [hpts'_def]; exact Finset.mem_union_right _ e.property⟩
    have hφ_bij : Function.Bijective φ := by
      refine ⟨?_, ?_⟩
      · intro ⟨g1, hg1⟩ ⟨g2, hg2⟩ h_eq_φ
        simp only [Subtype.mk_eq_mk]
        funext ⟨p, hp⟩
        rw [hpts'_def, Finset.mem_union] at hp
        rcases hp with hp | hp
        · -- p ∈ pts.
          have hg1_at :
              g1 ⟨p, by rw [hpts'_def]; exact Finset.mem_union_left _ hp⟩ =
              r ⟨p, hp⟩ := by
            have := congrFun hg1 ⟨p, hp⟩
            simpa [restr] using this
          have hg2_at :
              g2 ⟨p, by rw [hpts'_def]; exact Finset.mem_union_left _ hp⟩ =
              r ⟨p, hp⟩ := by
            have := congrFun hg2 ⟨p, hp⟩
            simpa [restr] using this
          rw [hg1_at, hg2_at]
        · -- p ∈ extras.
          exact congrFun h_eq_φ ⟨p, hp⟩
      · intro t
        let g : pts' → F := fun ⟨p, hp⟩ =>
          if h : p ∈ pts then r ⟨p, h⟩
            else t ⟨p, by
              have : p ∈ pts ∪ extras := by rw [← hpts'_def]; exact hp
              rw [Finset.mem_union] at this
              exact this.resolve_left h⟩
        refine ⟨⟨g, ?_⟩, ?_⟩
        · funext ⟨p, hp⟩
          show g ⟨p, h_pts_sub_pts' hp⟩ = r ⟨p, hp⟩
          simp only [g, hp, dif_pos]
        · funext ⟨e, he⟩
          have h_e_not_pts : e ∉ pts := fun h_e_pts =>
            (Finset.disjoint_iff_ne.mp h_extras_disj_pts) e he e h_e_pts rfl
          show g ⟨e, by rw [hpts'_def]; exact Finset.mem_union_right _ he⟩ = t ⟨e, he⟩
          simp only [g, h_e_not_pts, dif_neg, not_false_eq_true]
    exact Fintype.card_of_bijective hφ_bij
  exact h_fib_card

/-- Bivariate evaluation uniformity. Proof reduces to univariate
`evals_uniform` applied in each direction via the row-then-column
factoring `f(p,q) = s + ∑_i (∑_j coefs(i,j) * q^(j+1)) * p^(i+1)`. -/
theorem bivariate_evals_uniform (dx dy : ℕ) (s : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y)
    (h_Fx : dx + 1 ≤ Fintype.card F) (h_Fy : dy + 1 ≤ Fintype.card F) :
    (uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      = PMF.uniform (pts_x → pts_y → F) := by
  -- Edge cases first: if either pts_x or pts_y is empty, the codomain
  -- `pts_x → pts_y → F` is a subsingleton, and any two PMFs on a
  -- subsingleton type are equal.
  by_cases h_xy_subsing : pts_x.card = 0 ∨ pts_y.card = 0
  · -- Subsingleton case.
    have h_subsing : Subsingleton (pts_x → pts_y → F) := by
      rcases h_xy_subsing with hx | hy
      · haveI : IsEmpty pts_x := by
          rw [Finset.card_eq_zero] at hx
          subst hx
          exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
        infer_instance
      · haveI : IsEmpty pts_y := by
          rw [Finset.card_eq_zero] at hy
          subst hy
          exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
        haveI : Subsingleton (pts_y → F) := inferInstance
        infer_instance
    apply PMF.ext
    intro g
    have h_default : ∀ a, a = g := fun a => Subsingleton.elim a g
    have hμ := PMF.tsum_coe ((uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val))
    have hν := PMF.tsum_coe (PMF.uniform (pts_x → pts_y → F))
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hμ
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hν
    rw [hμ, hν]
  -- Non-degenerate case: both pts are nonempty.
  push_neg at h_xy_subsing
  obtain ⟨h_px_pos, h_py_pos⟩ := h_xy_subsing
  have h_dx_pos : 0 < dx := lt_of_lt_of_le (Nat.pos_of_ne_zero h_px_pos) h_cx
  have h_dy_pos : 0 < dy := lt_of_lt_of_le (Nat.pos_of_ne_zero h_py_pos) h_cy
  haveI : Nonempty (Fin dx) := ⟨⟨0, h_dx_pos⟩⟩
  haveI : Nonempty (Fin dy) := ⟨⟨0, h_dy_pos⟩⟩
  haveI h_pts_x_ne : Nonempty pts_x := by
    have h := Finset.card_pos.mp (Nat.pos_of_ne_zero h_px_pos)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  haveI h_pts_y_ne : Nonempty pts_y := by
    have h := Finset.card_pos.mp (Nat.pos_of_ne_zero h_py_pos)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  -- Define per-row Y-eval and per-q X-eval.
  set step1 : (Fin dx → Fin dy → F) → (Fin dx → pts_y → F) :=
    fun coefs i q => ∑ j : Fin dy, coefs i j * (q.val : F) ^ (j.val + 1) with hstep1
  set step2 : (Fin dx → pts_y → F) → (pts_x → pts_y → F) :=
    fun b p q => s + ∑ i : Fin dx, b i q * (p.val : F) ^ (i.val + 1) with hstep2
  -- Algebraic identity: bivariate eval = step2 ∘ step1.
  have h_factor : ∀ (coefs : Fin dx → Fin dy → F) (p : pts_x) (q : pts_y),
        Polynomial.eval (q.val : F)
          (Polynomial.eval (Polynomial.C (p.val : F))
            (Polynomial.C (Polynomial.C s) +
              ∑ i : Fin dx, ∑ j : Fin dy,
                Polynomial.C (Polynomial.C (coefs i j)) *
                  Polynomial.X ^ (i.val + 1) *
                  (Polynomial.C Polynomial.X) ^ (j.val + 1)))
      = step2 (step1 coefs) p q := by
    intro coefs p q
    simp only [hstep1, hstep2]
    -- Both inner and outer eval simplifications (one simp call handles both).
    simp only [Polynomial.eval_add, Polynomial.eval_C,
               Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_X]
    -- Algebraic massaging: ∑ i ∑ j, coefs i j * p^(i+1) * q^(j+1) = ∑ i, (∑ j, coefs i j * q^(j+1)) * p^(i+1).
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Push h_factor as a function-equality.
  have h_factor_fun :
      (fun (coefs : Fin dx → Fin dy → F) (p : pts_x) (q : pts_y) =>
        Polynomial.eval (q.val : F)
          (Polynomial.eval (Polynomial.C (p.val : F))
            (Polynomial.C (Polynomial.C s) +
              ∑ i : Fin dx, ∑ j : Fin dy,
                Polynomial.C (Polynomial.C (coefs i j)) *
                  Polynomial.X ^ (i.val + 1) *
                  (Polynomial.C Polynomial.X) ^ (j.val + 1))))
        = step2 ∘ step1 := by
    funext coefs p q; exact h_factor coefs p q
  -- Step 1: per-row Y-eval pushes uniform to uniform.
  have h_step1 :
      (PMF.uniform (Fin dx → Fin dy → F)).map step1
        = PMF.uniform (Fin dx → pts_y → F) := by
    -- The per-row map: row ↦ (q ↦ ∑ j, row j * q.val^(j+1)).
    -- This equals evals_uniform dy 0 pts_y h_cy h_ny h_Fy after simplification.
    have h_y_uni : (PMF.uniform (Fin dy → F)).map
        (fun (row : Fin dy → F) (q : pts_y) =>
          ∑ j : Fin dy, row j * (q.val : F) ^ (j.val + 1))
        = PMF.uniform (pts_y → F) := by
      have h_evals := evals_uniform dy (0 : F) pts_y h_cy h_ny h_Fy
      unfold uniformWithFixedZero at h_evals
      rw [PMF.map_comp] at h_evals
      have h_eq : (fun (row : Fin dy → F) (q : pts_y) =>
            ∑ j : Fin dy, row j * (q.val : F) ^ (j.val + 1))
          = (fun f (p : pts_y) => Polynomial.eval p.val f) ∘
              (fun coefs : Fin dy → F =>
                Polynomial.C (0 : F) + ∑ i : Fin dy,
                  Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) := by
        funext row q
        simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_C,
                   Polynomial.eval_finset_sum, Polynomial.eval_mul,
                   Polynomial.eval_pow, Polynomial.eval_X, zero_add]
      rw [h_eq]; exact h_evals
    -- Now lift via Pi-uniform helper.
    have h_pi := PMF.uniform_pi_map_of_uniform_map (ι := Fin dx) h_y_uni
    -- Rewrite step1 = fun coefs i => h (coefs i) where h is the per-row map.
    have h_step1_eq : step1 = fun (coefs : Fin dx → Fin dy → F) (i : Fin dx) =>
        (fun (row : Fin dy → F) (q : pts_y) =>
          ∑ j : Fin dy, row j * (q.val : F) ^ (j.val + 1)) (coefs i) := by
      funext coefs i q; rfl
    rw [h_step1_eq]; exact h_pi
  -- Step 2: pushforward via per-q X-eval. Decompose step2 via swaps.
  have h_step2 :
      (PMF.uniform (Fin dx → pts_y → F)).map step2
        = PMF.uniform (pts_x → pts_y → F) := by
    -- Decompose step2 = swap2 ∘ pi_x ∘ swap1.
    set swap1 : (Fin dx → pts_y → F) → (pts_y → Fin dx → F) :=
      fun b q i => b i q with hswap1
    set pi_x : (pts_y → Fin dx → F) → (pts_y → pts_x → F) :=
      fun M q p => s + ∑ i : Fin dx, M q i * (p.val : F) ^ (i.val + 1) with hpi_x
    set swap2 : (pts_y → pts_x → F) → (pts_x → pts_y → F) :=
      fun M p q => M q p with hswap2
    have h_decomp : step2 = swap2 ∘ pi_x ∘ swap1 := by
      funext b p q
      simp only [hstep2, Function.comp, hswap1, hpi_x, hswap2]
    rw [h_decomp]
    -- swap1 is bijective.
    have h_swap1_bij : Function.Bijective swap1 := by
      refine ⟨?_, ?_⟩
      · intro b1 b2 h_eq
        funext i q
        exact congrFun (congrFun h_eq q) i
      · intro M
        exact ⟨fun i q => M q i, rfl⟩
    have h_swap1 : (PMF.uniform (Fin dx → pts_y → F)).map swap1
        = PMF.uniform (pts_y → Fin dx → F) :=
      PMF.uniform_map_of_bijective h_swap1_bij
    -- swap2 is bijective.
    have h_swap2_bij : Function.Bijective swap2 := by
      refine ⟨?_, ?_⟩
      · intro M1 M2 h_eq
        funext q p
        exact congrFun (congrFun h_eq p) q
      · intro N
        exact ⟨fun q p => N p q, rfl⟩
    have h_swap2 : (PMF.uniform (pts_y → pts_x → F)).map swap2
        = PMF.uniform (pts_x → pts_y → F) :=
      PMF.uniform_map_of_bijective h_swap2_bij
    -- Per-q X-eval via Pi-uniform helper.
    have h_x_uni : (PMF.uniform (Fin dx → F)).map
        (fun (col : Fin dx → F) (p : pts_x) =>
          s + ∑ i : Fin dx, col i * (p.val : F) ^ (i.val + 1))
        = PMF.uniform (pts_x → F) := by
      have h_evals := evals_uniform dx s pts_x h_cx h_nx h_Fx
      unfold uniformWithFixedZero at h_evals
      rw [PMF.map_comp] at h_evals
      have h_eq : (fun (col : Fin dx → F) (p : pts_x) =>
            s + ∑ i : Fin dx, col i * (p.val : F) ^ (i.val + 1))
          = (fun f (p : pts_x) => Polynomial.eval p.val f) ∘
              (fun coefs : Fin dx → F =>
                Polynomial.C s + ∑ i : Fin dx,
                  Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) := by
        funext col p
        simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_C,
                   Polynomial.eval_finset_sum, Polynomial.eval_mul,
                   Polynomial.eval_pow, Polynomial.eval_X]
      rw [h_eq]; exact h_evals
    have h_pi_x : (PMF.uniform (pts_y → Fin dx → F)).map pi_x
        = PMF.uniform (pts_y → pts_x → F) := by
      have h_pi := PMF.uniform_pi_map_of_uniform_map (ι := pts_y) h_x_uni
      have h_pi_x_eq : pi_x = fun (M : pts_y → Fin dx → F) (q : pts_y) =>
          (fun (col : Fin dx → F) (p : pts_x) =>
            s + ∑ i : Fin dx, col i * (p.val : F) ^ (i.val + 1)) (M q) := by
        funext M q p; rfl
      rw [h_pi_x_eq]; exact h_pi
    -- Compose: ((uniform).map swap1).map pi_x.map swap2.
    rw [show (swap2 ∘ pi_x ∘ swap1) = swap2 ∘ (pi_x ∘ swap1) from rfl]
    rw [← PMF.map_comp]
    rw [← PMF.map_comp]
    rw [h_swap1, h_pi_x, h_swap2]
  -- Compose step1 and step2.
  unfold uniformBivariateWithFixedZero
  rw [PMF.map_comp]
  -- The composed map equals step2 ∘ step1.
  rw [show ((fun f (p : pts_x) (q : pts_y) =>
              Polynomial.eval (q.val : F) (Polynomial.eval (Polynomial.C (p.val : F)) f))
            ∘ (fun coefs : Fin dx → Fin dy → F =>
                Polynomial.C (Polynomial.C s) + ∑ i : Fin dx, ∑ j : Fin dy,
                  Polynomial.C (Polynomial.C (coefs i j)) *
                    Polynomial.X ^ (i.val + 1) *
                    (Polynomial.C Polynomial.X) ^ (j.val + 1)))
          = step2 ∘ step1 from h_factor_fun]
  rw [← PMF.map_comp, h_step1, h_step2]

/-! ## Translation invariance of uniform

For any uniform distribution on a finite group, addition by a constant
is a bijection and hence preserves uniform.  Used by
`bivariate_evals_uniform_full` to absorb the additive shift coming
from the random axis-X / axis-Y coefficients of
`uniformBivariateFullWithFixedZero`. -/

omit [Fintype F] [DecidableEq F] in
private theorem uniform_map_add_const (β : Type*) [Fintype β]
    [Nonempty β] [DecidableEq β] [AddGroup β] (δ : β) :
    (PMF.uniform β).map (fun b => b + δ) = PMF.uniform β :=
  PMF.uniform_map_of_bijective (Function.bijective_iff_has_inverse.mpr
    ⟨fun b => b - δ, fun _ => by simp, fun _ => by simp⟩)

/-! ## Constant-fiber size from a uniform-pushforward equation

Extracts the "every fiber has the same size" information from
`(PMF.uniform α).map f = PMF.uniform β`. -/

private theorem fiber_card_const_of_uniform_map_eq
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β]
    {f : α → β} (h_uniform : (PMF.uniform α).map f = PMF.uniform β) :
    ∃ k : ℕ, 0 < k ∧ ∀ b : β,
      (Finset.univ.filter (fun a : α => f a = b)).card = k := by
  -- Pattern from `uniform_pi_map_of_uniform_map`.
  have h_card_β_pos : 0 < Fintype.card β := Fintype.card_pos
  have h_card_α_pos : 0 < Fintype.card α := Fintype.card_pos
  have h_fib : ∀ b : β,
      (Finset.univ.filter (fun a : α => f a = b)).card * Fintype.card β
        = Fintype.card α := by
    intro b
    have h_pmf : ((PMF.uniform α).map f) b = (PMF.uniform β) b := by rw [h_uniform]
    simp only [PMF.map_apply, PMF.uniform_apply] at h_pmf
    have h_sum : (∑' (a : α), if b = f a then ((Fintype.card α : ℝ≥0∞))⁻¹ else 0)
        = (Finset.univ.filter (fun a : α => f a = b)).card *
            ((Fintype.card α : ℝ≥0∞))⁻¹ := by
      rw [tsum_eq_sum (s := Finset.univ.filter (fun a => f a = b))
          (fun a ha => by simp at ha; simp [Ne.symm ha])]
      have hsum_eq : ∀ a ∈ (Finset.univ.filter (fun a : α => f a = b)),
          (if b = f a then ((Fintype.card α : ℝ≥0∞))⁻¹ else 0)
            = ((Fintype.card α : ℝ≥0∞))⁻¹ := by
        intro a ha; simp at ha; simp [ha]
      rw [Finset.sum_congr rfl hsum_eq, Finset.sum_const, nsmul_eq_mul]
    rw [h_sum] at h_pmf
    have hα_ne : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast h_card_α_pos.ne'
    have hα_ne_top : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hβ_ne : (Fintype.card β : ℝ≥0∞) ≠ 0 := by exact_mod_cast h_card_β_pos.ne'
    have hβ_ne_top : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have h_pmf2 :
        ((Finset.univ.filter (fun a : α => f a = b)).card : ℝ≥0∞) * Fintype.card β
          = Fintype.card α := by
      have h_pmf' : ((Finset.univ.filter (fun a : α => f a = b)).card : ℝ≥0∞)
          = (Fintype.card β : ℝ≥0∞)⁻¹ * Fintype.card α := by
        have := congrArg (· * (Fintype.card α : ℝ≥0∞)) h_pmf
        simp only at this
        rw [mul_assoc, ENNReal.inv_mul_cancel hα_ne hα_ne_top, mul_one] at this
        exact this
      rw [h_pmf']
      rw [mul_comm ((Fintype.card β : ℝ≥0∞)⁻¹), mul_assoc,
          ENNReal.inv_mul_cancel hβ_ne hβ_ne_top, mul_one]
    have h_pmf3 :
        (((Finset.univ.filter (fun a : α => f a = b)).card * Fintype.card β : ℕ) : ℝ≥0∞)
          = ((Fintype.card α : ℕ) : ℝ≥0∞) := by
      push_cast; exact h_pmf2
    exact_mod_cast h_pmf3
  have h_β_dvd_α : Fintype.card β ∣ Fintype.card α := by
    obtain ⟨b⟩ := (inferInstance : Nonempty β)
    exact ⟨_, (h_fib b).symm.trans (by ring)⟩
  refine ⟨Fintype.card α / Fintype.card β, ?_, ?_⟩
  · -- 0 < |α| / |β| from divisibility + positivity.
    exact Nat.div_pos (Nat.le_of_dvd h_card_α_pos h_β_dvd_α) h_card_β_pos
  · intro b
    have hfib_b := h_fib b
    have hα_eq : Fintype.card α = Fintype.card β * (Fintype.card α / Fintype.card β) := by
      rw [Nat.mul_div_cancel' h_β_dvd_α]
    rw [hα_eq] at hfib_b
    have h_eq : (Finset.univ.filter (fun a : α => f a = b)).card * Fintype.card β
        = (Fintype.card α / Fintype.card β) * Fintype.card β := by
      rw [hfib_b]; ring
    exact Nat.eq_of_mul_eq_mul_right h_card_β_pos h_eq

/-! ## Headline: `bivariate_evals_uniform` for the **full** distribution

For `uniformBivariateFullWithFixedZero` (only constant fixed at `s`),
the joint distribution of bivariate evaluations at the off-axis grid
`pts_x × pts_y` is uniform on `pts_x → pts_y → F`.

The proof reduces to the existing axis-zero `bivariate_evals_uniform`
plus translation invariance: writing `f.eval (C p)).eval q` as
`s + α(axisX)(p) + β(axisY)(q) + γ(coefs)(p, q)`, the γ-term's
distribution is uniform by `bivariate_evals_uniform dx dy 0`, and
`s + α(axisX)(p) + β(axisY)(q)` is a shift that depends only on
`(axisX, axisY, p, q)` — adding a (possibly random) shift to a
uniform distribution leaves it uniform. -/
theorem bivariate_evals_uniform_full (dx dy : ℕ) (s : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y)
    (h_Fx : dx + 1 ≤ Fintype.card F) (h_Fy : dy + 1 ≤ Fintype.card F) :
    (uniformBivariateFullWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      = PMF.uniform (pts_x → pts_y → F) := by
  classical
  -- Subsingleton edge cases (one or both pts empty).
  by_cases h_xy_subsing : pts_x.card = 0 ∨ pts_y.card = 0
  · have h_subsing : Subsingleton (pts_x → pts_y → F) := by
      rcases h_xy_subsing with hx | hy
      · haveI : IsEmpty pts_x := by
          rw [Finset.card_eq_zero] at hx
          subst hx
          exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
        infer_instance
      · haveI : IsEmpty pts_y := by
          rw [Finset.card_eq_zero] at hy
          subst hy
          exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
        haveI : Subsingleton (pts_y → F) := inferInstance
        infer_instance
    apply PMF.ext
    intro g
    have h_default : ∀ a, a = g := fun a => Subsingleton.elim a g
    have hμ := PMF.tsum_coe ((uniformBivariateFullWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val))
    have hν := PMF.tsum_coe (PMF.uniform (pts_x → pts_y → F))
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hμ
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hν
    rw [hμ, hν]
  push_neg at h_xy_subsing
  obtain ⟨h_px_pos, h_py_pos⟩ := h_xy_subsing
  have h_dx_pos : 0 < dx := lt_of_lt_of_le (Nat.pos_of_ne_zero h_px_pos) h_cx
  have h_dy_pos : 0 < dy := lt_of_lt_of_le (Nat.pos_of_ne_zero h_py_pos) h_cy
  haveI : Nonempty (Fin dx) := ⟨⟨0, h_dx_pos⟩⟩
  haveI : Nonempty (Fin dy) := ⟨⟨0, h_dy_pos⟩⟩
  haveI h_pts_x_ne : Nonempty pts_x := by
    have h := Finset.card_pos.mp (Nat.pos_of_ne_zero h_px_pos)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  haveI h_pts_y_ne : Nonempty pts_y := by
    have h := Finset.card_pos.mp (Nat.pos_of_ne_zero h_py_pos)
    exact ⟨⟨h.choose, h.choose_spec⟩⟩
  -- Step 1: Algebraic eval factoring.  After unfolding the polynomial-
  -- construction step, the eval-at-grid map equals the additive form M.
  let M : ((Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F)) →
      (pts_x → pts_y → F) :=
    fun cax => fun (p : pts_x) (q : pts_y) =>
      s + (∑ i : Fin dx, cax.2.1 i * p.val ^ (i.val + 1)) +
          (∑ j : Fin dy, cax.2.2 j * q.val ^ (j.val + 1)) +
          (∑ i : Fin dx, ∑ j : Fin dy,
            cax.1 i j * p.val ^ (i.val + 1) * q.val ^ (j.val + 1))
  have hM_def : ∀ (cax : (Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F))
      (p : pts_x) (q : pts_y),
      M cax p q = s + (∑ i : Fin dx, cax.2.1 i * p.val ^ (i.val + 1)) +
          (∑ j : Fin dy, cax.2.2 j * q.val ^ (j.val + 1)) +
          (∑ i : Fin dx, ∑ j : Fin dy,
            cax.1 i j * p.val ^ (i.val + 1) * q.val ^ (j.val + 1)) :=
    fun _ _ _ => rfl
  have h_factor :
      (uniformBivariateFullWithFixedZero dx dy s).map
        (fun f (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val) =
        (PMF.uniform ((Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F))).map M := by
    unfold uniformBivariateFullWithFixedZero
    rw [PMF.map_comp]
    congr 1
    funext cax
    obtain ⟨c, ax, ay⟩ := cax
    funext p q
    show ((Polynomial.C (Polynomial.C s) +
        (∑ i : Fin dx, Polynomial.C (Polynomial.C (ax i)) * Polynomial.X ^ (i.val + 1)) +
        (∑ j : Fin dy, Polynomial.C (Polynomial.C (ay j)) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
        ∑ i : Fin dx, ∑ j : Fin dy,
          Polynomial.C (Polynomial.C (c i j)) *
            Polynomial.X ^ (i.val + 1) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)).eval (Polynomial.C p.val)).eval q.val
      = M (c, ax, ay) p q
    rw [hM_def]
    simp only [Polynomial.eval_add, Polynomial.eval_C,
               Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_X]
  rw [h_factor]
  -- Step 2: γ-pushforward via existing `bivariate_evals_uniform dx dy 0`.
  -- Re-cast the body of the `bivariate_evals_uniform` call into the
  -- "γ" function we want.
  have h_γ : (PMF.uniform (Fin dx → Fin dy → F)).map
        (fun (c : Fin dx → Fin dy → F) (p : pts_x) (q : pts_y) =>
          ∑ i : Fin dx, ∑ j : Fin dy,
            c i j * p.val ^ (i.val + 1) * q.val ^ (j.val + 1))
        = PMF.uniform (pts_x → pts_y → F) := by
    have h_old := bivariate_evals_uniform dx dy (0 : F)
        pts_x pts_y h_cx h_cy h_nx h_ny h_Fx h_Fy
    unfold uniformBivariateWithFixedZero at h_old
    rw [PMF.map_comp] at h_old
    have h_eq : (fun (c : Fin dx → Fin dy → F) (p : pts_x) (q : pts_y) =>
          ∑ i : Fin dx, ∑ j : Fin dy,
            c i j * p.val ^ (i.val + 1) * q.val ^ (j.val + 1))
        = (fun f (p : pts_x) (q : pts_y) =>
            (f.eval (Polynomial.C p.val)).eval q.val) ∘
          (fun (coefs : Fin dx → Fin dy → F) =>
            Polynomial.C (Polynomial.C (0 : F)) +
              ∑ i : Fin dx, ∑ j : Fin dy,
                Polynomial.C (Polynomial.C (coefs i j)) *
                  Polynomial.X ^ (i.val + 1) *
                  (Polynomial.C Polynomial.X) ^ (j.val + 1)) := by
      funext c p q
      simp only [Function.comp_apply, Polynomial.eval_add, Polynomial.eval_C,
                 Polynomial.eval_finset_sum, Polynomial.eval_mul,
                 Polynomial.eval_pow, Polynomial.eval_X, ← Polynomial.C_pow,
                 zero_add]
    rw [h_eq]; exact h_old
  -- Step 3: Show `(uniform on source).map M` = `uniform on target`
  -- via constant-fiber surjection.  Fiber over v has size
  -- `|F|^|pts_x| × |F|^|pts_y| × γ-fiber-size`, where γ-fiber-size is
  -- extracted from `h_γ`.
  obtain ⟨k_γ, hk_γ_pos, hk_γ_fib⟩ := fiber_card_const_of_uniform_map_eq h_γ
  -- Source nonemptiness is automatic from existing instances.
  haveI : Nonempty (Fin dx → Fin dy → F) := ⟨fun _ _ => 0⟩
  haveI : Nonempty (Fin dx → F) := ⟨fun _ => 0⟩
  haveI : Nonempty (Fin dy → F) := ⟨fun _ => 0⟩
  haveI : Nonempty (pts_x → pts_y → F) := ⟨fun _ _ => 0⟩
  haveI : Nonempty ((Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F)) :=
    inferInstance
  -- The fiber size we want.
  set k_total : ℕ := (Fintype.card F) ^ (Fintype.card (Fin dx)) *
                     (Fintype.card F) ^ (Fintype.card (Fin dy)) * k_γ with hk_total_def
  have h_card_F_pos : 0 < Fintype.card F := by linarith
  have hk_total_pos : 0 < k_total := by
    rw [hk_total_def]
    refine Nat.mul_pos (Nat.mul_pos ?_ ?_) hk_γ_pos
    · exact pow_pos h_card_F_pos _
    · exact pow_pos h_card_F_pos _
  apply PMF.uniform_map_of_surjective_constFiber M k_total hk_total_pos
  intro v
  -- Define γEval and the (ax, ay)-shifted γ-target.
  set γEval : (Fin dx → Fin dy → F) → (pts_x → pts_y → F) :=
    fun c (p : pts_x) (q : pts_y) =>
      ∑ i : Fin dx, ∑ j : Fin dy,
        c i j * p.val ^ (i.val + 1) * q.val ^ (j.val + 1) with hγEval_def
  set shifted : (Fin dx → F) → (Fin dy → F) → (pts_x → pts_y → F) :=
    fun ax ay (p : pts_x) (q : pts_y) =>
      v p q - s - (∑ i : Fin dx, ax i * p.val ^ (i.val + 1))
              - (∑ j : Fin dy, ay j * q.val ^ (j.val + 1)) with hshifted_def
  -- Algebraic identity: M(c, ax, ay) = v ↔ γEval c = shifted ax ay.
  have h_eqv : ∀ (c : Fin dx → Fin dy → F) (ax : Fin dx → F) (ay : Fin dy → F),
      M (c, ax, ay) = v ↔ γEval c = shifted ax ay := by
    intro c ax ay
    refine ⟨fun hM => ?_, fun hγ => ?_⟩
    · funext p q
      have hpq := congrFun (congrFun hM p) q
      have hM_pq := hM_def (c, ax, ay) p q
      simp only [hγEval_def, hshifted_def]
      linear_combination hpq - hM_pq
    · funext p q
      have hpq := congrFun (congrFun hγ p) q
      have hM_pq := hM_def (c, ax, ay) p q
      simp only [hγEval_def, hshifted_def] at hpq
      linear_combination hM_pq + hpq
  -- Bijection between M-fiber over v and Σ (ax, ay), γ-fiber over (shifted ax ay).
  let φ : {cax : (Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F) // M cax = v} →
      Σ axay : (Fin dx → F) × (Fin dy → F),
        {c : Fin dx → Fin dy → F // γEval c = shifted axay.1 axay.2} :=
    fun ⟨⟨c, ax, ay⟩, hM⟩ => ⟨(ax, ay), ⟨c, (h_eqv c ax ay).mp hM⟩⟩
  let ψ :
      (Σ axay : (Fin dx → F) × (Fin dy → F),
        {c : Fin dx → Fin dy → F // γEval c = shifted axay.1 axay.2}) →
      {cax : (Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F) // M cax = v} :=
    fun ⟨⟨ax, ay⟩, ⟨c, hc⟩⟩ => ⟨(c, ax, ay), (h_eqv c ax ay).mpr hc⟩
  have h_card_eq :
      (Finset.univ.filter (fun cax : (Fin dx → Fin dy → F) × (Fin dx → F) × (Fin dy → F) =>
        M cax = v)).card =
      Fintype.card (Σ axay : (Fin dx → F) × (Fin dy → F),
        {c : Fin dx → Fin dy → F // γEval c = shifted axay.1 axay.2}) := by
    rw [← Fintype.card_subtype]
    apply Fintype.card_congr
    refine ⟨φ, ψ, ?_, ?_⟩
    · rintro ⟨⟨c, ax, ay⟩, _⟩; rfl
    · rintro ⟨⟨ax, ay⟩, c, _⟩; rfl
  rw [h_card_eq]
  rw [Fintype.card_sigma]
  -- Each summand has card = k_γ via hk_γ_fib.
  have h_summand_card : ∀ axay : (Fin dx → F) × (Fin dy → F),
      Fintype.card {c : Fin dx → Fin dy → F // γEval c = shifted axay.1 axay.2} = k_γ := by
    intro axay
    rw [Fintype.card_subtype]
    exact hk_γ_fib (shifted axay.1 axay.2)
  rw [Finset.sum_congr rfl (fun axay _ => h_summand_card axay)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fun]

/-! ## Helper: uniform of a product factors as a bind

For finite nonempty `α, β`, the uniform PMF on `α × β` equals
sampling `a ~ uniform α` then `b ~ uniform β` and pairing — i.e.,
the standard "uniform of product = product of uniforms" identity,
expressed as a `bind`/`map` chain. Used by `evals_uniform_full_no_fixed`
below to peel off the random Shamir-constant. -/

omit [Field F] [Fintype F] [DecidableEq F] in
theorem _root_.PMF.uniform_prod_eq_bind {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    [DecidableEq α] [DecidableEq β] :
    PMF.uniform (α × β) =
      (PMF.uniform α).bind (fun a => (PMF.uniform β).map (a, ·)) := by
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [PMF.bind_apply]
  -- Compute the inner term `((uniform β).map (a', ·)) (a, b)` per a'.
  have h_inner : ∀ a' : α,
      ((PMF.uniform β).map (a', ·)) (a, b) =
        if a = a' then ((Fintype.card β : ℝ≥0∞))⁻¹ else 0 := by
    intro a'
    rw [PMF.map_apply]
    by_cases h : a = a'
    · subst h
      rw [tsum_eq_single b]
      · simp [PMF.uniform_apply]
      · intro b' hb'
        simp; intro h'; exact hb' h'.symm
    · rw [if_neg h]
      refine (tsum_congr (fun b' => ?_)).trans tsum_zero
      rw [if_neg]
      intro h_eq
      exact h (congrArg Prod.fst h_eq)
  -- Use `tsum_congr` to substitute h_inner inside the tsum.
  rw [show (∑' a' : α, PMF.uniform α a' * ((PMF.uniform β).map (a', ·)) (a, b))
        = ∑' a' : α, PMF.uniform α a' *
              (if a = a' then ((Fintype.card β : ℝ≥0∞))⁻¹ else 0) by
      apply tsum_congr; intro a'; rw [h_inner]]
  -- Sum over a' of (uniform α a' · (if a = a' then |β|⁻¹ else 0)) = |α|⁻¹ · |β|⁻¹.
  rw [tsum_eq_single a]
  · simp [PMF.uniform_apply, Fintype.card_prod]
    rw [ENNReal.mul_inv]
    · exact Or.inl (by exact_mod_cast (Fintype.card_pos).ne')
    · exact Or.inl (by simp)
  · intro a' ha'
    simp [PMF.uniform_apply]
    intro hcontra
    exact ha' hcontra.symm

/-! ## Random-constant Shamir secrecy

For `b ~ uniform (Fin t → F)` and `c ~ uniform F` independently,
the polynomial `c + ∑_i b_i · X^{i+1}` evaluated at `pts` (with
`pts.card ≤ t`, `0 ∉ pts`, `t + 1 ≤ |F|`) has joint distribution
uniform on `pts → F`. This is the no-fixed-zero variant of
`evals_uniform`: the constant `c` is also random rather than pinned.

Used by `rowPoly_eval_uniform_full` to handle rows `l ≥ 1` of the
bivariate polynomial's row-poly form. -/
theorem evals_uniform_full_no_fixed (t : ℕ) (pts : Finset F)
    (h_card : pts.card ≤ t) (h_nz : (0 : F) ∉ pts)
    (h_F : t + 1 ≤ Fintype.card F) :
    (PMF.uniform (F × (Fin t → F))).map
        (fun (cb : F × (Fin t → F)) (p : pts) =>
          cb.1 + ∑ i : Fin t, cb.2 i * (p.val : F) ^ (i.val + 1))
      = PMF.uniform (pts → F) := by
  classical
  rw [PMF.uniform_prod_eq_bind]
  rw [PMF.map_bind]
  -- After bind decomposition: (uniform F).bind (fun c => (uniform (Fin t → F)).map (...))
  have h_inner : ∀ c : F,
      ((PMF.uniform (Fin t → F)).map (Prod.mk c)).map
          (fun (cb : F × (Fin t → F)) (p : pts) =>
            cb.1 + ∑ i : Fin t, cb.2 i * (p.val : F) ^ (i.val + 1))
        = PMF.uniform (pts → F) := by
    intro c
    rw [PMF.map_comp]
    -- The composition (Prod.mk c) ≫ ... equals the per-c eval map.
    have h_comp : ((fun (cb : F × (Fin t → F)) (p : pts) =>
            cb.1 + ∑ i : Fin t, cb.2 i * (p.val : F) ^ (i.val + 1))
          ∘ (Prod.mk c))
        = (fun (b : Fin t → F) (p : pts) =>
            c + ∑ i : Fin t, b i * (p.val : F) ^ (i.val + 1)) := by
      funext b p; rfl
    rw [h_comp]
    -- This is the eval-pts pushforward of `uniformWithFixedZero t c`.
    have h_evals := evals_uniform t c pts h_card h_nz h_F
    unfold uniformWithFixedZero at h_evals
    rw [PMF.map_comp] at h_evals
    have h_eq : (fun (b : Fin t → F) (p : pts) =>
          c + ∑ i : Fin t, b i * (p.val : F) ^ (i.val + 1))
        = (fun f (p : pts) => Polynomial.eval p.val f) ∘
            (fun coefs : Fin t → F =>
              Polynomial.C c + ∑ i : Fin t,
                Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) := by
      funext b p
      simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_C,
                 Polynomial.eval_finset_sum, Polynomial.eval_mul,
                 Polynomial.eval_pow, Polynomial.eval_X]
    rw [h_eq]; exact h_evals
  conv_lhs => arg 2; ext c; rw [h_inner]
  exact PMF.bind_const _ _

/-! ## Row-poly form: per-row independent uniformity

Helper bijection: `(Fin t → F) × (Fin t → F × (Fin t → F)) ≃
((Fin t → Fin t → F) × (Fin t → F) × (Fin t → F))` via re-arrangement.

* axisX (`Fin t → F`) ↔ first factor.
* For each `k : Fin t`: `(axisY k, fun i => coefs i k)` ↔ k-th
  component of the second factor.

This re-grouping aligns the source distribution
`uniformBivariateFullWithFixedZero t t s` with the per-row
factoring used by `rowPoly_eval_uniform_full`. -/

omit [Fintype F] [DecidableEq F] in
/-- The l-th coefficient of `f.eval (C p)` where `f` is built
explicitly from `(coefs, axisX, axisY)`.

Strategy: simplify polynomial-of-polynomial eval at `C p` term by
term, then read off the `coeff l.val` of the resulting `Polynomial F`
using `coeff_C_mul_X_pow`. -/
private theorem rowPolyCoeff_explicit (t : ℕ) (s : F)
    (coefs : Fin t → Fin t → F) (axisX axisY : Fin t → F)
    (p : F) (l : Fin (t+1)) :
    ((Polynomial.C (Polynomial.C s) +
        (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
          Polynomial.X ^ (i.val + 1)) +
        (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
        ∑ i : Fin t, ∑ j : Fin t,
          Polynomial.C (Polynomial.C (coefs i j)) *
            Polynomial.X ^ (i.val + 1) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)).eval
        (Polynomial.C p)).coeff l.val =
      if h0 : l.val = 0 then s + ∑ i : Fin t, axisX i * p ^ (i.val + 1)
      else (have h_lt : l.val - 1 < t := by
              have h_l_lt := l.isLt
              omega
            axisY ⟨l.val - 1, h_lt⟩ +
              ∑ i : Fin t, coefs i ⟨l.val - 1, h_lt⟩ * p ^ (i.val + 1)) := by
  classical
  -- Step A: simplify `f.eval (C p)` into a polynomial in the inner Y.
  -- After simp, each term collapses to a constant (in Polynomial F)
  -- multiplied by a power of X (the inner Y).
  have h_step_A :
      ((Polynomial.C (Polynomial.C s) +
          (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
            Polynomial.X ^ (i.val + 1)) +
          (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
          ∑ i : Fin t, ∑ j : Fin t,
            Polynomial.C (Polynomial.C (coefs i j)) *
              Polynomial.X ^ (i.val + 1) *
              (Polynomial.C Polynomial.X) ^ (j.val + 1)).eval
          (Polynomial.C p) :
            _root_.Polynomial F) =
        Polynomial.C s +
        (∑ i : Fin t, Polynomial.C (axisX i * p ^ (i.val + 1))) +
        (∑ j : Fin t, Polynomial.C (axisY j) * Polynomial.X ^ (j.val + 1)) +
        ∑ i : Fin t, ∑ j : Fin t,
          Polynomial.C (coefs i j * p ^ (i.val + 1)) *
            Polynomial.X ^ (j.val + 1) := by
    simp only [Polynomial.eval_add, Polynomial.eval_C,
               Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_X,
               ← Polynomial.C_pow, ← Polynomial.C_mul]
  rw [h_step_A]
  -- Step B: extract coefficient at l.val.
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C]
  -- The four summands of `f.eval (C p)` are:
  -- (1) C s : coeff at 0 is s, else 0.
  -- (2) ∑_i C(axisX_i p^{i+1}) : coeff at 0 is ∑_i (axisX_i p^{i+1}), else 0.
  -- (3) ∑_j C(axisY_j) X^{j+1} : coeff at j+1 is axisY_j, else 0.
  -- (4) ∑_{i,j} C(c_{ij} p^{i+1}) X^{j+1} : coeff at j+1 is ∑_i c_{ij} p^{i+1}, else 0.
  rw [show (∑ i : Fin t, Polynomial.C (axisX i * p ^ (i.val + 1)) :
            _root_.Polynomial F).coeff l.val =
        if l.val = 0 then ∑ i : Fin t, axisX i * p ^ (i.val + 1) else 0 from by
      rw [Polynomial.finset_sum_coeff]
      by_cases hl : l.val = 0
      · rw [if_pos hl]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.coeff_C, if_pos hl]
      · rw [if_neg hl]
        apply Finset.sum_eq_zero; intro i _
        rw [Polynomial.coeff_C, if_neg hl]]
  rw [show (∑ j : Fin t, Polynomial.C (axisY j) * Polynomial.X ^ (j.val + 1) :
            _root_.Polynomial F).coeff l.val =
        if h0 : l.val = 0 then 0
        else axisY ⟨l.val - 1, by have := l.isLt; omega⟩ from by
      rw [Polynomial.finset_sum_coeff]
      by_cases hl : l.val = 0
      · rw [dif_pos hl]
        apply Finset.sum_eq_zero; intro j _
        rw [Polynomial.coeff_C_mul_X_pow]
        have h_ne : ¬ l.val = j.val + 1 := by omega
        rw [if_neg h_ne]
      · rw [dif_neg hl]
        have h_l_lt : l.val - 1 < t := by have := l.isLt; omega
        rw [Finset.sum_eq_single ⟨l.val - 1, h_l_lt⟩]
        · rw [Polynomial.coeff_C_mul_X_pow]
          have h_eq : l.val = (⟨l.val - 1, h_l_lt⟩ : Fin t).val + 1 := by
            show l.val = l.val - 1 + 1
            have := l.isLt; omega
          rw [if_pos h_eq]
        · intro j _ hj
          rw [Polynomial.coeff_C_mul_X_pow]
          have h_ne : ¬ l.val = j.val + 1 := by
            intro hcontra
            apply hj
            apply Fin.ext
            show j.val = l.val - 1
            have := l.isLt; omega
          rw [if_neg h_ne]
        · intro h_contra
          exact (h_contra (Finset.mem_univ _)).elim]
  rw [show (∑ i : Fin t, ∑ j : Fin t,
              Polynomial.C (coefs i j * p ^ (i.val + 1)) *
                Polynomial.X ^ (j.val + 1) :
            _root_.Polynomial F).coeff l.val =
        if h0 : l.val = 0 then 0
        else ∑ i : Fin t,
              coefs i ⟨l.val - 1, by have := l.isLt; omega⟩ * p ^ (i.val + 1) from by
      rw [Polynomial.finset_sum_coeff]
      by_cases hl : l.val = 0
      · rw [dif_pos hl]
        apply Finset.sum_eq_zero; intro i _
        rw [Polynomial.finset_sum_coeff]
        apply Finset.sum_eq_zero; intro j _
        rw [Polynomial.coeff_C_mul_X_pow]
        have h_ne : ¬ l.val = j.val + 1 := by omega
        rw [if_neg h_ne]
      · rw [dif_neg hl]
        have h_l_lt : l.val - 1 < t := by have := l.isLt; omega
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.finset_sum_coeff]
        rw [Finset.sum_eq_single ⟨l.val - 1, h_l_lt⟩]
        · rw [Polynomial.coeff_C_mul_X_pow]
          have h_eq : l.val = (⟨l.val - 1, h_l_lt⟩ : Fin t).val + 1 := by
            show l.val = l.val - 1 + 1
            have := l.isLt; omega
          rw [if_pos h_eq]
        · intro j _ hj
          rw [Polynomial.coeff_C_mul_X_pow]
          have h_ne : ¬ l.val = j.val + 1 := by
            intro hcontra
            apply hj
            apply Fin.ext
            show j.val = l.val - 1
            have := l.isLt; omega
          rw [if_neg h_ne]
        · intro h_contra
          exact (h_contra (Finset.mem_univ _)).elim]
  -- Combine the four parts.
  by_cases hl : l.val = 0
  · rw [if_pos hl, dif_pos hl, if_pos hl, dif_pos hl, dif_pos hl]
    ring
  · rw [if_neg hl, dif_neg hl, if_neg hl, dif_neg hl, dif_neg hl]
    ring

/-! ## Headline: row-poly secrecy for the full distribution

The joint distribution of "row coefficients" `(f.eval (C p)).coeff l`
over `(p, l) ∈ pts × Fin (t+1)` is uniform on `pts → Fin (t+1) → F`,
hence sec-invariant.  This is the AVSS Phase 7.4 algebraic core.

**Proof sketch** (per-row independence):

1. The bivariate polynomial sample `f ~ uniformBivariateFullWithFixedZero t t s`
   factorizes via `(coefs, axisX, axisY)`, giving the explicit form
   `(f.eval (C p)).coeff l =
      if l = 0 then s + ∑_i axisX_i p^{i+1}
      else axisY_{l-1} + ∑_i coefs_{i, l-1} p^{i+1}`.

2. Re-group: the data for row `l = 0` is `(s, axisX)` (with `s` fixed);
   for row `l = j+1`, it is `(axisY_j, coefs_{·, j}) ∈ F × (Fin t → F)`.

3. Per-row pushforward at `pts`:
   * Row 0: `axisX → (p ↦ s + ∑_i axisX_i p^{i+1})` is uniform on
     `pts → F` by `evals_uniform t s pts ...`.
   * Row j+1: `(axisY_j, coefs_{·, j}) → (p ↦ ...)` is uniform on
     `pts → F` by `evals_uniform_full_no_fixed t pts ...`.

4. Joint over l: rows are independent (different randomness slices),
   so joint is uniform on `pts → Fin (t+1) → F` (after `Fin.cases`
   and curry/swap rearrangements). -/
theorem rowPoly_eval_uniform_full (t : ℕ) (s : F) (pts : Finset F)
    (h_card : pts.card ≤ t) (h_nz : (0 : F) ∉ pts)
    (h_F : t + 1 ≤ Fintype.card F) :
    (uniformBivariateFullWithFixedZero t t s).map
        (fun f => fun (p : pts) (l : Fin (t+1)) =>
          (f.eval (Polynomial.C p.val)).coeff l.val)
      = PMF.uniform (pts → Fin (t+1) → F) := by
  classical
  -- Edge case: pts empty.
  by_cases h_pts_empty : pts.card = 0
  · -- Subsingleton case.
    haveI : IsEmpty pts := by
      rw [Finset.card_eq_zero] at h_pts_empty
      subst h_pts_empty
      exact ⟨fun ⟨_, h⟩ => Finset.notMem_empty _ h⟩
    haveI : Subsingleton (pts → Fin (t+1) → F) := inferInstance
    apply PMF.ext
    intro g
    have h_default : ∀ a, a = g := fun a => Subsingleton.elim a g
    have hμ := PMF.tsum_coe ((uniformBivariateFullWithFixedZero t t s).map
        (fun f => fun (p : pts) (l : Fin (t+1)) =>
          (f.eval (Polynomial.C p.val)).coeff l.val))
    have hν := PMF.tsum_coe (PMF.uniform (pts → Fin (t+1) → F))
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hμ
    rw [tsum_eq_single g (fun b hb => absurd (h_default b) hb)] at hν
    rw [hμ, hν]
  -- Non-degenerate case.
  push_neg at h_pts_empty
  have h_pts_nonempty : pts.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h_pts_empty)
  have h_t_pos : 0 < t := lt_of_lt_of_le (Nat.pos_of_ne_zero h_pts_empty) h_card
  haveI : Nonempty pts := ⟨⟨h_pts_nonempty.choose, h_pts_nonempty.choose_spec⟩⟩
  haveI : Nonempty (Fin t) := ⟨⟨0, h_t_pos⟩⟩
  haveI : Nonempty F := ⟨0⟩
  -- Step 1: rewrite the row-poly map via `rowPolyCoeff_explicit`.
  unfold uniformBivariateFullWithFixedZero
  rw [PMF.map_comp]
  have h_factor :
      ((fun f => fun (p : pts) (l : Fin (t+1)) =>
          (f.eval (Polynomial.C p.val)).coeff l.val)
        ∘ (fun (cax : (Fin t → Fin t → F) × (Fin t → F) × (Fin t → F)) =>
            Polynomial.C (Polynomial.C s) +
            (∑ i : Fin t, Polynomial.C (Polynomial.C (cax.2.1 i)) *
              Polynomial.X ^ (i.val + 1)) +
            (∑ j : Fin t, Polynomial.C (Polynomial.C (cax.2.2 j)) *
              (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
            ∑ i : Fin t, ∑ j : Fin t,
              Polynomial.C (Polynomial.C (cax.1 i j)) *
                Polynomial.X ^ (i.val + 1) *
                (Polynomial.C Polynomial.X) ^ (j.val + 1)))
        = (fun (cax : (Fin t → Fin t → F) × (Fin t → F) × (Fin t → F)) =>
            fun (p : pts) (l : Fin (t+1)) =>
              if h : l.val = 0 then
                s + ∑ i : Fin t, cax.2.1 i * (p.val : F) ^ (i.val + 1)
              else cax.2.2 ⟨l.val - 1, by omega⟩ +
                ∑ i : Fin t,
                  cax.1 i ⟨l.val - 1, by omega⟩ * (p.val : F) ^ (i.val + 1)) := by
    funext ⟨c, ax, ay⟩ p l
    simp only [Function.comp]
    exact rowPolyCoeff_explicit t s c ax ay p.val l
  rw [h_factor]
  -- Step 2: reshape source to `(Fin t → F) × (Fin t → F × (Fin t → F))`.
  -- Bijection: (c, ax, ay) ↔ (ax, fun k => (ay k, fun i => c i k)).
  let reshape :
      (Fin t → Fin t → F) × (Fin t → F) × (Fin t → F) →
        (Fin t → F) × (Fin t → F × (Fin t → F)) :=
    fun cax => (cax.2.1, fun k => (cax.2.2 k, fun i => cax.1 i k))
  let reshape_inv :
      (Fin t → F) × (Fin t → F × (Fin t → F)) →
        (Fin t → Fin t → F) × (Fin t → F) × (Fin t → F) :=
    fun ax_β => ((fun i k => (ax_β.2 k).2 i),
                 ax_β.1,
                 (fun k => (ax_β.2 k).1))
  have h_reshape_bij : Function.Bijective reshape := by
    refine ⟨?_, ?_⟩
    · rintro ⟨c1, ax1, ay1⟩ ⟨c2, ax2, ay2⟩ h_eq
      simp only [reshape, Prod.mk.injEq] at h_eq
      obtain ⟨h_ax, h_β⟩ := h_eq
      -- h_β : (fun k => (ay1 k, fun i => c1 i k)) = (fun k => (ay2 k, fun i => c2 i k))
      have h_ay : ay1 = ay2 := by
        funext k
        have := congrFun h_β k
        exact (Prod.mk.injEq _ _ _ _).mp this |>.1
      have h_c : c1 = c2 := by
        funext i k
        have := congrFun h_β k
        have h2 := (Prod.mk.injEq _ _ _ _).mp this |>.2
        exact congrFun h2 i
      rw [h_ax, h_ay, h_c]
    · intro ax_β
      exact ⟨reshape_inv ax_β, by simp [reshape, reshape_inv]⟩
  -- Pre-compose with reshape (bijection ⇒ uniform pushforward = uniform).
  have h_uniform_reshape :
      (PMF.uniform ((Fin t → Fin t → F) × (Fin t → F) × (Fin t → F))).map reshape
        = PMF.uniform ((Fin t → F) × (Fin t → F × (Fin t → F))) :=
    PMF.uniform_map_of_bijective h_reshape_bij
  -- The map (cax) → row-poly equals the map (ax_β = reshape cax) → row-poly via reshape.
  have h_map_eq :
      (fun cax : (Fin t → Fin t → F) × (Fin t → F) × (Fin t → F) =>
          fun (p : pts) (l : Fin (t+1)) =>
            if h : l.val = 0 then
              s + ∑ i : Fin t, cax.2.1 i * (p.val : F) ^ (i.val + 1)
            else cax.2.2 ⟨l.val - 1, by omega⟩ +
              ∑ i : Fin t,
                cax.1 i ⟨l.val - 1, by omega⟩ * (p.val : F) ^ (i.val + 1))
        = (fun ax_β : (Fin t → F) × (Fin t → F × (Fin t → F)) =>
            fun (p : pts) (l : Fin (t+1)) =>
              if h : l.val = 0 then
                s + ∑ i : Fin t, ax_β.1 i * (p.val : F) ^ (i.val + 1)
              else (ax_β.2 ⟨l.val - 1, by omega⟩).1 +
                ∑ i : Fin t,
                  (ax_β.2 ⟨l.val - 1, by omega⟩).2 i *
                    (p.val : F) ^ (i.val + 1))
          ∘ reshape := by
    funext cax p l
    simp only [Function.comp, reshape]
  rw [h_map_eq, ← PMF.map_comp, h_uniform_reshape]
  -- Step 3: use Fin.cases to split l = 0 vs l = succ.
  -- The map factors as:
  --   (ax, β) ↦ (p ↦ Fin.cases (eval0 ax p) (fun k => eval_α (β k) p))
  -- = (ax, β) ↦ (p ↦ l ↦ result)
  -- We want to express this through:
  --   - `eval0 : (Fin t → F) → (pts → F)`, `eval0 ax p = s + ∑_i ax_i p^{i+1}`.
  --   - `eval_α : (F × (Fin t → F)) → (pts → F)`, `eval_α (cb) p = cb.1 + ∑_i cb.2 i p^{i+1}`.
  let eval0 : (Fin t → F) → (pts → F) :=
    fun ax (p : pts) => s + ∑ i : Fin t, ax i * (p.val : F) ^ (i.val + 1)
  let eval_α : (F × (Fin t → F)) → (pts → F) :=
    fun cb (p : pts) => cb.1 + ∑ i : Fin t, cb.2 i * (p.val : F) ^ (i.val + 1)
  have h_eval0_uniform :
      (PMF.uniform (Fin t → F)).map eval0 = PMF.uniform (pts → F) := by
    have h_evals := evals_uniform t s pts h_card h_nz h_F
    unfold uniformWithFixedZero at h_evals
    rw [PMF.map_comp] at h_evals
    have h_eq : eval0 = (fun f (p : pts) => Polynomial.eval p.val f) ∘
        (fun coefs : Fin t → F =>
          Polynomial.C s + ∑ i : Fin t,
            Polynomial.C (coefs i) * Polynomial.X ^ (i.val + 1)) := by
      funext b p
      simp only [Function.comp, Polynomial.eval_add, Polynomial.eval_C,
                 Polynomial.eval_finset_sum, Polynomial.eval_mul,
                 Polynomial.eval_pow, Polynomial.eval_X, eval0]
    rw [h_eq]; exact h_evals
  have h_eval_α_uniform :
      (PMF.uniform (F × (Fin t → F))).map eval_α = PMF.uniform (pts → F) :=
    evals_uniform_full_no_fixed t pts h_card h_nz h_F
  -- The current map: (ax, β) ↦ (p ↦ l ↦ result(ax, β, p, l)).
  -- Rewrite via Fin.cases:
  --   result(ax, β, p, l) = Fin.cases (eval0 ax p) (fun k => eval_α (β k) p) l
  -- Then curry/swap p ↔ l.
  have h_via_fincases :
      (fun ax_β : (Fin t → F) × (Fin t → F × (Fin t → F)) =>
          fun (p : pts) (l : Fin (t+1)) =>
            if h : l.val = 0 then
              s + ∑ i : Fin t, ax_β.1 i * (p.val : F) ^ (i.val + 1)
            else (ax_β.2 ⟨l.val - 1, by omega⟩).1 +
              ∑ i : Fin t,
                (ax_β.2 ⟨l.val - 1, by omega⟩).2 i *
                  (p.val : F) ^ (i.val + 1))
        = (fun ax_β : (Fin t → F) × (Fin t → F × (Fin t → F)) =>
            fun (p : pts) (l : Fin (t+1)) =>
              Fin.cases (eval0 ax_β.1 p) (fun k => eval_α (ax_β.2 k) p) l) := by
    funext ax_β p l
    -- Case-split on l using Fin.cases / Fin.induction.
    refine l.cases ?_ ?_
    · -- l = 0
      simp [eval0, Fin.cases_zero]
    · -- l = k.succ
      intro k
      simp only [Fin.cases_succ]
      have h_l_ne_zero : k.succ.val ≠ 0 := by simp [Fin.succ]
      rw [dif_neg h_l_ne_zero]
      have h_l_pred : k.succ.val - 1 = k.val := by simp [Fin.succ]
      have h_idx_eq : (⟨k.succ.val - 1, by omega⟩ : Fin t) = k := by
        ext; exact h_l_pred
      rw [h_idx_eq]
  rw [h_via_fincases]
  -- Step 4: factor the map as `(ax_β) ↦ (ax_β.1 → eval0, ax_β.2 → β.k ↦ eval_α (β k))`,
  -- composed with Fin.cases swap and curry/swap.
  set step1 : (Fin t → F) × (Fin t → F × (Fin t → F)) →
              (pts → F) × (Fin t → pts → F) :=
    fun ax_β => (eval0 ax_β.1, fun k => eval_α (ax_β.2 k)) with hstep1
  set step2 : (pts → F) × (Fin t → pts → F) →
              pts → Fin (t+1) → F :=
    fun gf p l => Fin.cases (gf.1 p) (fun k => gf.2 k p) l with hstep2
  have h_decomp :
      (fun ax_β : (Fin t → F) × (Fin t → F × (Fin t → F)) =>
          fun (p : pts) (l : Fin (t+1)) =>
            Fin.cases (eval0 ax_β.1 p) (fun k => eval_α (ax_β.2 k) p) l)
        = step2 ∘ step1 := by
    funext ax_β p l
    simp only [Function.comp, step1, step2]
  rw [h_decomp, ← PMF.map_comp]
  -- Step 5: prove (uniform Source).map step1 = uniform target1.
  -- Use the "uniform of product map" lemma:
  --   if (uniform A).map f = uniform A' and (uniform B).map g = uniform B',
  --   then (uniform (A × B)).map (Prod.map f g) = uniform (A' × B').
  have h_step1 :
      (PMF.uniform ((Fin t → F) × (Fin t → F × (Fin t → F)))).map step1
        = PMF.uniform ((pts → F) × (Fin t → pts → F)) := by
    -- Decompose step1 as Prod.map eval0 (Pi-lift of eval_α).
    set pi_eval : (Fin t → F × (Fin t → F)) → (Fin t → pts → F) :=
      fun β k => eval_α (β k) with hpi_eval
    have h_pi :
        (PMF.uniform (Fin t → F × (Fin t → F))).map pi_eval
          = PMF.uniform (Fin t → pts → F) :=
      PMF.uniform_pi_map_of_uniform_map (ι := Fin t) h_eval_α_uniform
    have h_step1_eq : step1 = Prod.map eval0 pi_eval := by
      funext ax_β; rfl
    rw [h_step1_eq]
    -- Now apply Prod.map uniformity lemma.
    -- (uniform (A × B)).map (Prod.map f g) = uniform (A' × B').
    -- Proof: chain through `uniform_prod_eq_bind` and `bind_map`/`map_bind`.
    rw [PMF.uniform_prod_eq_bind]
    rw [PMF.map_bind]
    -- Inner: ((uniform B).map (a, ·)).map (Prod.map eval0 pi_eval)
    --      = (uniform B).map ((Prod.map eval0 pi_eval) ∘ (a, ·))
    --      = (uniform B).map (fun b => (eval0 a, pi_eval b))
    --      = ((uniform B).map pi_eval).map (Prod.mk (eval0 a))
    --      = (uniform (Fin t → pts → F)).map (Prod.mk (eval0 a))
    have h_inner : ∀ a : Fin t → F,
        ((PMF.uniform (Fin t → F × (Fin t → F))).map (Prod.mk a)).map
            (Prod.map eval0 pi_eval)
          = (PMF.uniform (Fin t → pts → F)).map (Prod.mk (eval0 a)) := by
      intro a
      rw [PMF.map_comp]
      have h_comp : (Prod.map eval0 pi_eval) ∘ (Prod.mk a)
          = Prod.mk (eval0 a) ∘ pi_eval := by
        funext b; rfl
      rw [h_comp, ← PMF.map_comp, h_pi]
    conv_lhs => arg 2; ext a; rw [h_inner]
    -- Now we have:
    --   (uniform A).bind (fun a => (uniform (Fin t → pts → F)).map (Prod.mk (eval0 a)))
    -- Substitute u = eval0 a via bind_map:
    --   ((uniform A).map eval0).bind (fun u => (uniform (Fin t → pts → F)).map (Prod.mk u))
    --   = (uniform (pts → F)).bind (fun u => ...) (by h_eval0_uniform)
    --   = uniform ((pts → F) × (Fin t → pts → F)) (by uniform_prod_eq_bind reversed).
    rw [show (fun a : Fin t → F =>
              (PMF.uniform (Fin t → pts → F)).map (Prod.mk (eval0 a)))
            = (fun u : pts → F => (PMF.uniform (Fin t → pts → F)).map (Prod.mk u))
              ∘ eval0 from rfl]
    rw [← PMF.bind_map _ eval0 _, h_eval0_uniform]
    rw [← PMF.uniform_prod_eq_bind]
  rw [h_step1]
  -- Step 6: step2 is bijective.
  have h_step2_bij : Function.Bijective step2 := by
    refine ⟨?_, ?_⟩
    · intro gf gf' h_eq
      refine Prod.ext ?_ ?_
      · -- gf.1 = gf'.1 via evaluation at l = 0.
        funext p
        have := congrFun (congrFun h_eq p) (0 : Fin (t+1))
        simpa [step2, Fin.cases_zero] using this
      · -- gf.2 = gf'.2 via evaluation at l = k.succ.
        funext k p
        have := congrFun (congrFun h_eq p) k.succ
        simpa [step2, Fin.cases_succ] using this
    · intro h
      refine ⟨((fun p => h p 0), (fun k p => h p k.succ)), ?_⟩
      funext p l
      refine Fin.cases ?_ ?_ l
      · simp [step2]
      · intro k; simp [step2]
  exact PMF.uniform_map_of_bijective h_step2_bij

/-! ## Sec-invariance corollary -/
theorem bivariate_shamir_secrecy_rowPoly_full (t : ℕ) (s s' : F)
    (pts : Finset F) (h_card : pts.card ≤ t) (h_nz : (0 : F) ∉ pts)
    (h_F : t + 1 ≤ Fintype.card F) :
    (uniformBivariateFullWithFixedZero t t s).map
        (fun f => fun (p : pts) (l : Fin (t+1)) =>
          (f.eval (Polynomial.C p.val)).coeff l.val)
      =
    (uniformBivariateFullWithFixedZero t t s').map
        (fun f => fun (p : pts) (l : Fin (t+1)) =>
          (f.eval (Polynomial.C p.val)).coeff l.val) := by
  rw [rowPoly_eval_uniform_full t s pts h_card h_nz h_F,
      rowPoly_eval_uniform_full t s' pts h_card h_nz h_F]

/-! ## Phase 8.6 / 11-δ: Bivariate row+column uniformity

The +200 LOC row+column secrecy upgrade deferred since `SyncVSS.lean §10`.
Generalises `bivariate_evals_uniform_full` (which gives uniformity on a
*rectangular* grid `pts_x × pts_y`) to **arbitrary subsets** `S ⊆ R × R`
of a single point set `R` (with `|R| ≤ t`, `0 ∉ R`).

This is the literature-standard form of bivariate Shamir secrecy: the
joint evaluation of `f` at any `≤ t × t` subset of "row × column" points
in `R × R` (avoiding both secret axes) is uniform on `F^|S|`.

**Proof strategy.** Corollary of `bivariate_evals_uniform_full t t sec R R …`
followed by a constant-fiber projection along the inclusion
`↑S ↪ ↑R × ↑R`.  Each fiber over `h : ↑S → F` has size
`|F|^(|R|² − |S|)` — independent of `h`. -/

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Auxiliary: pushforward of `PMF.uniform (κ → α)` along precomposition
with an injection `proj : ι → κ` is `PMF.uniform (ι → α)`.

Used by `bivariate_evals_uniform_row_col` to project the rectangular
joint distribution down to an arbitrary subset of evaluation points.

**Proof.**  Constant-fiber surjection: for each `h : ι → α`, the fiber
`{g : κ → α | g ∘ proj = h}` is in bijection with `(κ \ image proj) → α`
via "drop the proj-image-bound part" (forward) and "extend back via
proj⁻¹ on image proj using h" (backward).  Hence each fiber has size
`|α|^(|κ| − |ι|)`, constant in `h`.  Apply
`PMF.uniform_map_of_surjective_constFiber`. -/
theorem _root_.PMF.uniform_pi_restrict
    {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Fintype α] [DecidableEq α] [Nonempty α] [Nonempty ι] [Nonempty κ]
    (proj : ι → κ) (h_inj : Function.Injective proj) :
    (PMF.uniform (κ → α)).map (fun g => g ∘ proj) = PMF.uniform (ι → α) := by
  classical
  -- The set of "constrained" coordinates: image of proj.
  set imageSet : Finset κ := Finset.univ.image proj with himageSet_def
  have h_image_card : imageSet.card = Fintype.card ι := by
    rw [himageSet_def, Finset.card_image_of_injective _ h_inj, Finset.card_univ]
  have h_image_le : Fintype.card ι ≤ Fintype.card κ := by
    rw [← h_image_card, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  -- Choose a left-inverse of proj on its image, using injectivity.
  let invFun : κ → ι := fun k =>
    if h : k ∈ imageSet then
      Classical.choose (Finset.mem_image.mp h)
    else
      Classical.arbitrary ι
  have h_inv_proj : ∀ i : ι, invFun (proj i) = i := by
    intro i
    have h_mem : proj i ∈ imageSet :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have h_choose := Classical.choose_spec (Finset.mem_image.mp h_mem)
    show (if h : proj i ∈ imageSet then
      Classical.choose (Finset.mem_image.mp h) else Classical.arbitrary ι) = i
    rw [dif_pos h_mem]
    exact h_inj h_choose.2
  have h_proj_inv : ∀ k ∈ imageSet, proj (invFun k) = k := by
    intro k hk
    have h_choose := Classical.choose_spec (Finset.mem_image.mp hk)
    show proj (if h : k ∈ imageSet then
      Classical.choose (Finset.mem_image.mp h) else Classical.arbitrary ι) = k
    rw [dif_pos hk]
    exact h_choose.2
  -- Fiber size: |α|^(|κ| - |ι|).
  set k_size : ℕ := (Fintype.card α) ^ (Fintype.card κ - Fintype.card ι) with hk_size_def
  have h_card_α_pos : 0 < Fintype.card α := Fintype.card_pos
  have hk_pos : 0 < k_size := pow_pos h_card_α_pos _
  apply PMF.uniform_map_of_surjective_constFiber (fun g : κ → α => g ∘ proj) k_size hk_pos
  intro h
  -- Construct a bijection between the fiber and `(univ \ imageSet) → α`.
  -- Forward: drop the image-bound part (g ↦ g restricted to univ \ imageSet).
  -- Backward: f ↦ extend f to all of κ using h ∘ invFun on imageSet.
  let toFree : {g : κ → α // g ∘ proj = h} →
      ((Finset.univ \ imageSet : Finset κ) → α) :=
    fun ⟨g, _⟩ j => g j.val
  let fromFree : ((Finset.univ \ imageSet : Finset κ) → α) →
      {g : κ → α // g ∘ proj = h} :=
    fun f => ⟨fun k =>
      if hk : k ∈ imageSet then h (invFun k) else f ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩⟩,
      by
        funext i
        show (if hk : proj i ∈ imageSet then h (invFun (proj i))
              else f ⟨proj i, by simp [hk]⟩) = h i
        have hmem : proj i ∈ imageSet :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        rw [dif_pos hmem, h_inv_proj]⟩
  have h_bij : Function.Bijective toFree := by
    refine ⟨?_, ?_⟩
    · -- Injective.
      rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ heq
      apply Subtype.ext
      show g₁ = g₂
      funext k
      by_cases hk : k ∈ imageSet
      · -- On imageSet: g₁ k = g₂ k via h_inv_proj and the constraint hg₁ / hg₂.
        have h₁ : g₁ (proj (invFun k)) = h (invFun k) := congrFun hg₁ (invFun k)
        have h₂ : g₂ (proj (invFun k)) = h (invFun k) := congrFun hg₂ (invFun k)
        have hpik : proj (invFun k) = k := h_proj_inv k hk
        rw [hpik] at h₁ h₂
        rw [h₁, h₂]
      · -- On complement: g₁ k = g₂ k via the heq on free coords.
        have h_kmem : k ∈ (Finset.univ \ imageSet : Finset κ) := by simp [hk]
        exact congrFun heq ⟨k, h_kmem⟩
    · -- Surjective.
      intro f
      refine ⟨fromFree f, ?_⟩
      funext j
      show (fromFree f).val j.val = f j
      have hk_notin : j.val ∉ imageSet := by
        have hjm := j.property
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hjm
        exact hjm
      show (if hk : j.val ∈ imageSet then h (invFun j.val)
            else f ⟨j.val, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩⟩) = f j
      rw [dif_neg hk_notin]
  -- Compute the cardinality.
  rw [show (Finset.univ.filter (fun (g : κ → α) => g ∘ proj = h)).card =
        Fintype.card {g : κ → α // g ∘ proj = h} from
      (Fintype.card_subtype _).symm]
  rw [Fintype.card_of_bijective h_bij]
  rw [Fintype.card_fun, Fintype.card_coe, Finset.card_univ_diff, h_image_card]

/-- **Bivariate row+column uniformity (Phase 8.6 / 11-δ).**

Strengthens `bivariate_evals_uniform_full` from rectangular grids
`pts_x × pts_y` to arbitrary subsets `S ⊆ R × R` of a single point set
`R` (with `|R| ≤ t`, `0 ∉ R`).

Concretely: for `R ⊆ F` with `R.card ≤ t` and `0 ∉ R`, and any
`S ⊆ R ×ˢ R`, the joint evaluation distribution at `S` of a uniformly
sampled bivariate polynomial of bidegree `(t, t)` with `f(0, 0) = sec`
is uniform on `↑S → F`.

This is the literature-standard form of bivariate Shamir secrecy: the
corrupt coalition's view of `f` at *any* subset of (row, col) points
avoiding both secret axes is uniform — independently of the secret.
The conclusion does *not* require `S` to be a rectangular product;
it covers e.g. `S = {(p, q) | p ∈ corr_row} ∪ {(p, q) | q ∈ corr_col}`,
the row+column union form arising in AVSS's coalition view.

**Proof.** Corollary of `bivariate_evals_uniform_full t t sec R R …`,
followed by a constant-fiber projection along the canonical inclusion
`↑S ↪ ↑R × ↑R` (cf. `PMF.uniform_pi_restrict`). -/
theorem bivariate_evals_uniform_row_col
    (t : ℕ) (sec : F) (R : Finset F)
    (h_card : R.card ≤ t) (h_nz : (0 : F) ∉ R)
    (h_F : t + 1 ≤ Fintype.card F)
    (S : Finset (F × F)) (hS : S ⊆ R ×ˢ R)
    [Nonempty S] [Nonempty (↥R × ↥R)] :
    (uniformBivariateFullWithFixedZero t t sec).map
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2) =
      PMF.uniform (S → F) := by
  classical
  -- For `pq : ↑S`, both components live in `R` (since S ⊆ R ×ˢ R).
  have hR_S : ∀ (pq : S), pq.val.1 ∈ R ∧ pq.val.2 ∈ R := fun pq => by
    have h_in : pq.val ∈ R ×ˢ R := hS pq.property
    rwa [Finset.mem_product] at h_in
  -- Step 1: factor the eval map through the rectangular bivariate eval map.
  -- The eval map at `S` factors as `proj ∘ rect_eval`, where:
  --   * `rect_eval f : ↑R → ↑R → F = (p, q) ↦ (f.eval (C p)).eval q`,
  --   * `proj g : ↑S → F = pq ↦ g ⟨pq.val.1, _⟩ ⟨pq.val.2, _⟩`.
  have h_factor :
      (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2) =
        (fun (g : ↥R → ↥R → F) (pq : S) =>
          g ⟨pq.val.1, (hR_S pq).1⟩ ⟨pq.val.2, (hR_S pq).2⟩) ∘
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (p : ↥R) (q : ↥R) =>
          (f.eval (Polynomial.C p.val)).eval q.val) := by
    funext f pq; rfl
  rw [h_factor, ← PMF.map_comp]
  -- Step 2: apply the rectangular bivariate uniformity at pts_x = pts_y = R.
  rw [bivariate_evals_uniform_full t t sec R R h_card h_card h_nz h_nz h_F h_F]
  -- Step 3: factor `proj : (↥R → ↥R → F) → (↑S → F)` through uncurry plus
  -- precomposition with the canonical inclusion `iota : ↑S → ↥R × ↥R`.
  let iota : ↥S → ↥R × ↥R :=
    fun pq => (⟨pq.val.1, (hR_S pq).1⟩, ⟨pq.val.2, (hR_S pq).2⟩)
  have h_iota_inj : Function.Injective iota := by
    intro pq₁ pq₂ heq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst heq)
    · exact congrArg Subtype.val (congrArg Prod.snd heq)
  have h_curry_eq : (fun (g : ↥R → ↥R → F) (pq : S) =>
        g ⟨pq.val.1, (hR_S pq).1⟩ ⟨pq.val.2, (hR_S pq).2⟩) =
      (fun (g : ↥R × ↥R → F) => g ∘ iota) ∘ Function.uncurry := by
    funext g pq; rfl
  rw [h_curry_eq, ← PMF.map_comp]
  -- Step 4: uniform on `↥R → ↥R → F` maps to uniform on `↥R × ↥R → F` via uncurry.
  have h_uncurry_bij : Function.Bijective
      (Function.uncurry : (↥R → ↥R → F) → (↥R × ↥R → F)) :=
    ⟨fun _ _ h => funext fun a => funext fun b => congrFun h (a, b),
     fun g => ⟨Function.curry g, by funext ⟨a, b⟩; rfl⟩⟩
  rw [PMF.uniform_map_of_bijective h_uncurry_bij]
  -- Step 5: project to `↑S → F` via the constant-fiber projection.
  exact PMF.uniform_pi_restrict iota h_iota_inj

end Leslie.Prob.Polynomial
