/-
Copyright (c) 2026 Rupak Majumdar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rupak Majumdar
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Finite-coordinate Fubini lemmas for `Measure.infinitePi`

This file collects small product-measure facts used by the randomised
adversary tape construction.  The main lemma says that an `ENNReal` function
depending on a finite set of coordinates is independent of a fresh coordinate
under `Measure.infinitePi`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {ι : Type*} [DecidableEq ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

open Filtration

theorem lintegral_infinitePi_mul_eval_of_piFinset
    {s : Finset ι} {q : ι} (hq : q ∉ s)
    {A : (Π i, X i) → ℝ≥0∞} {B : X q → ℝ≥0∞}
    (hA : Measurable[piFinset s] A) (hB : Measurable B)
    (x : Π i, X i) :
    (∫⁻ y, A y * B (y q) ∂infinitePi μ) =
      (∫⁻ y, A y ∂infinitePi μ) * (∫⁻ z, B z ∂μ q) := by
  classical
  let F : (Π i, X i) → ℝ≥0∞ := fun y => A y * B (y q)
  have hF_meas : Measurable F := by
    exact (hA.mono (piFinset.le s) le_rfl).mul (hB.comp (measurable_pi_apply q))
  have hF_pi : Measurable[piFinset (insert q s)] F := by
    refine (hA.mono ?_ le_rfl).mul ?_
    · exact piFinset.mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
    · have hEval : Measurable[piFinset (insert q s)] (fun y : Π i, X i => y q) := by
        rw [piFinset_eq_comap_restrict (X := X) (insert q s)]
        simpa [Set.restrict_apply] using
          (measurable_pi_apply ⟨q, by simp⟩).comp
            (comap_measurable (((insert q s : Finset ι) : Set ι).restrict))
      exact hB.comp hEval
  rw [lintegral_infinitePi_of_piFinset μ hF_pi x]
  rw [lmarginal_insert (μ := μ) F hF_meas hq x]
  have h_inner (z : X q) :
      (∫⋯∫⁻_s, F ∂μ) (Function.update x q z) =
        (∫⋯∫⁻_s, A ∂μ) x * B z := by
    have hA_update (w : Π i : s, X i) :
        A (Function.updateFinset (Function.update x q z) s w) =
          A (Function.updateFinset x s w) := by
      apply hA.dependsOn_of_piFinset
      intro i hi
      have hif : i ∈ s := hi
      simp [Function.updateFinset, hif]
    simp only [lmarginal]
    calc
      (∫⁻ y : (i : s) → X i,
          F (Function.updateFinset (Function.update x q z) s y)
          ∂Measure.pi fun i : s => μ i)
          = ∫⁻ y : (i : s) → X i,
              A (Function.updateFinset x s y) * B z
              ∂Measure.pi fun i : s => μ i := by
            refine lintegral_congr fun y => ?_
            simp [F, hq, hA_update y, Function.updateFinset]
      _ = (∫⁻ y : (i : s) → X i, A (Function.updateFinset x s y)
              ∂Measure.pi fun i : s => μ i) * B z := by
            rw [lintegral_mul_const]
            exact (hA.mono (piFinset.le s) le_rfl).comp measurable_updateFinset
  simp_rw [h_inner]
  rw [lintegral_const_mul]
  · rw [lintegral_infinitePi_of_piFinset μ hA x]
  · exact hB

end MeasureTheory.Measure

namespace ProbabilityTheory

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory
  Preorder

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

theorem IicProdIoc_preimage_singleton
    (n : ℕ) (y : Π i : Iic (n + 1), X i.1) :
    (IicProdIoc (X := X) n (n + 1)) ⁻¹' {y} =
      {(frestrictLe₂ n.le_succ y, restrict₂ Ioc_subset_Iic_self y)} := by
  ext p
  constructor
  · intro hp
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
    subst hp
    exact Prod.ext
      (congrFun (frestrictLe₂_comp_IicProdIoc (X := X) n.le_succ) p).symm
      (congrFun (restrict₂_comp_IicProdIoc (X := X) n (n + 1)) p).symm
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact (MeasurableEquiv.IicProdIoc (X := X) n.le_succ).right_inv y

end ProbabilityTheory

namespace ProbabilityTheory.Kernel

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory
  Preorder

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

theorem partialTraj_succ_apply_singleton
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i.1) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    [∀ n, Countable (Π i : Iic n, X i.1)]
    [∀ n, MeasurableSingletonClass (Π i : Iic n, X i.1)]
    [∀ n, MeasurableSingletonClass (X n)]
    (n : ℕ) (x₀ : Π i : Iic 0, X i.1)
    (y : Π i : Iic (n + 1), X i.1) :
    partialTraj κ 0 (n + 1) x₀ {y} =
      partialTraj κ 0 n x₀ {frestrictLe₂ n.le_succ y} *
        (κ n (frestrictLe₂ n.le_succ y)) {y ⟨n + 1, mem_Iic.2 le_rfl⟩} := by
  rw [partialTraj_succ_of_le (zero_le n)]
  rw [Kernel.map_apply' _ measurable_IicProdIoc _ (MeasurableSet.singleton y)]
  rw [comp_apply' _ _ _ (measurable_IicProdIoc (MeasurableSet.singleton y))]
  simp_rw [IicProdIoc_preimage_singleton (X := X) n y]
  rw [lintegral_countable']
  rw [tsum_eq_single (frestrictLe₂ n.le_succ y)]
  · rw [Kernel.prod_apply, Kernel.id_apply]
    rw [show ({(frestrictLe₂ n.le_succ y, restrict₂ Ioc_subset_Iic_self y)} : Set _) =
        {frestrictLe₂ n.le_succ y} ×ˢ {restrict₂ Ioc_subset_Iic_self y} by
          rw [Set.singleton_prod_singleton]]
    rw [Measure.prod_prod]
    rw [Measure.dirac_apply_of_mem (by simp)]
    simp only [one_mul]
    rw [Kernel.map_apply' _ (MeasurableEquiv.piSingleton n).measurable _
      (MeasurableSet.singleton _)]
    have htail : restrict₂ Ioc_subset_Iic_self y =
        (MeasurableEquiv.piSingleton (X := X) n) (y ⟨n + 1, mem_Iic.2 le_rfl⟩) := by
      ext i
      cases Nat.mem_Ioc_succ' i
      rfl
    rw [htail]
    rw [show ⇑(MeasurableEquiv.piSingleton (X := X) n) ⁻¹'
          {(MeasurableEquiv.piSingleton (X := X) n) (y ⟨n + 1, mem_Iic.2 le_rfl⟩)} =
        {y ⟨n + 1, mem_Iic.2 le_rfl⟩} by
          ext z
          simp [(MeasurableEquiv.piSingleton (X := X) n).injective.eq_iff]]
    rw [mul_comm]
  · intro z hz
    rw [Kernel.prod_apply, Kernel.id_apply]
    rw [show ({(frestrictLe₂ n.le_succ y, restrict₂ Ioc_subset_Iic_self y)} : Set _) =
        {frestrictLe₂ n.le_succ y} ×ˢ {restrict₂ Ioc_subset_Iic_self y} by
          rw [Set.singleton_prod_singleton]]
    rw [Measure.prod_prod]
    rw [Measure.dirac_apply z]
    simp [hz]

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.Kernel

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory
  Preorder

variable {C : Type*} [MeasurableSpace C]

theorem partialTraj_succ_apply_singleton_const
    (κ : (n : ℕ) → Kernel (Π _i : Finset.Iic (α := ℕ) n, C) C)
    [∀ n, IsMarkovKernel (κ n)]
    [∀ n, Countable (Π _i : Finset.Iic (α := ℕ) n, C)]
    [∀ n, MeasurableSingletonClass (Π _i : Finset.Iic (α := ℕ) n, C)]
    [MeasurableSingletonClass C]
    (n : ℕ) (x₀ : Π _i : Finset.Iic (α := ℕ) 0, C)
    (y : Π _i : Finset.Iic (α := ℕ) (n + 1), C) :
    partialTraj (X := fun _ => C) κ 0 (n + 1) x₀ {y} =
      partialTraj (X := fun _ => C) κ 0 n x₀
          {fun i : Finset.Iic (α := ℕ) n => y ⟨i.1, Finset.mem_Iic.2
            ((Finset.mem_Iic.1 i.2).trans n.le_succ)⟩} *
        (κ n (fun i : Finset.Iic (α := ℕ) n => y ⟨i.1, Finset.mem_Iic.2
          ((Finset.mem_Iic.1 i.2).trans n.le_succ)⟩))
          {y ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩} := by
  simpa only using
    (partialTraj_succ_apply_singleton (X := fun _ : ℕ => C) κ n x₀ y)

end ProbabilityTheory.Kernel
