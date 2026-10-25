import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Bounded differences of squared linear forms

A coordinate replacement in the ellipticity cube has an explicit influence bound.
The estimate depends only on the absolute row sums and the replaced column.
-/

namespace LongRange

open scoped BigOperators

/-- Two points in the ellipticity interval differ by at most the inverse lower bound. -/
theorem abs_sub_le_of_mem_Icc {lam s t : ℝ} (hlam : 0 < lam)
    (hs : s ∈ Set.Icc lam lam⁻¹) (ht : t ∈ Set.Icc lam lam⁻¹) :
    |s - t| ≤ lam⁻¹ := by
  apply abs_sub_le_iff.mpr
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

variable {K J : Type*} [Fintype K] [Fintype J] [DecidableEq J]
    {lam : ℝ} (hlam : 0 < lam) (B : K → J → ℝ)
    {m : ℝ} (hm : m ∈ Set.Icc lam lam⁻¹)

include hlam hm

omit [Fintype K] [DecidableEq J] in
/-- A centered linear form on the cube is bounded by its absolute row sum. -/
theorem abs_linearForm_le (y : J → ℝ) (hy : ∀ j, y j ∈ Set.Icc lam lam⁻¹) (k : K) :
    |∑ j, B k j * (y j - m)| ≤ lam⁻¹ * ∑ j, |B k j| := by
  calc
    _ ≤ ∑ j, |B k j * (y j - m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, lam⁻¹ * |B k j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, mul_comm lam⁻¹]
      exact mul_le_mul_of_nonneg_left
        (abs_sub_le_of_mem_Icc hlam (hy j) hm) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Replacing one coordinate in the cube bounds the change of the sum of squared forms. -/
theorem sum_sq_linearForm_update_le (y : J → ℝ)
    (hy : ∀ j, y j ∈ Set.Icc lam lam⁻¹) (j : J)
    {t : ℝ} (ht : t ∈ Set.Icc lam lam⁻¹) :
    |∑ k, (∑ i, B k i * (y i - m)) ^ 2 -
        ∑ k, (∑ i, B k i * (Function.update y j t i - m)) ^ 2| ≤
      2 * lam⁻¹ ^ 2 * ∑ k, |B k j| * ∑ i, |B k i| := by
  have hy' : ∀ i, Function.update y j t i ∈ Set.Icc lam lam⁻¹ := by
    intro i
    by_cases h : i = j
    · subst i
      simpa only [Function.update_self] using ht
    · simpa only [Function.update_of_ne h] using hy i
  have hrow (k : K) :
      |(∑ i, B k i * (y i - m)) ^ 2 -
          (∑ i, B k i * (Function.update y j t i - m)) ^ 2| ≤
        2 * lam⁻¹ ^ 2 * (|B k j| * ∑ i, |B k i|) := by
    let D := ∑ i, B k i * (y i - m)
    let D' := ∑ i, B k i * (Function.update y j t i - m)
    have hdiff : D - D' = B k j * (y j - t) := by
      dsimp [D, D']
      rw [← Finset.sum_sub_distrib]
      calc
        _ = B k j * (y j - m) - B k j * (t - m) := by
          rw [Finset.sum_eq_single j]
          · rw [Function.update_self]
          · intro i _ hij
            rw [Function.update_of_ne hij, sub_self]
          · simp
        _ = _ := by ring
    have hd : |D - D'| ≤ lam⁻¹ * |B k j| := by
      rw [hdiff, abs_mul, mul_comm lam⁻¹]
      exact mul_le_mul_of_nonneg_left
        (abs_sub_le_of_mem_Icc hlam (hy j) ht) (abs_nonneg _)
    have hs : |D + D'| ≤ 2 * lam⁻¹ * ∑ i, |B k i| := by
      have hD := abs_linearForm_le hlam B hm y hy k
      have hD' := abs_linearForm_le hlam B hm _ hy' k
      calc
        _ ≤ |D| + |D'| := abs_add_le _ _
        _ ≤ lam⁻¹ * (∑ i, |B k i|) + lam⁻¹ * (∑ i, |B k i|) :=
          add_le_add hD hD'
        _ = _ := by ring
    change |D ^ 2 - D' ^ 2| ≤ _
    calc
      _ = |D - D'| * |D + D'| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (lam⁻¹ * |B k j|) * (2 * lam⁻¹ * ∑ i, |B k i|) :=
        mul_le_mul hd hs (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ = |∑ k, ((∑ i, B k i * (y i - m)) ^ 2 -
        (∑ i, B k i * (Function.update y j t i - m)) ^ 2)| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k, |(∑ i, B k i * (y i - m)) ^ 2 -
        (∑ i, B k i * (Function.update y j t i - m)) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, 2 * lam⁻¹ ^ 2 * (|B k j| * ∑ i, |B k i|) :=
      Finset.sum_le_sum fun k _ => hrow k
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A nonnegative scalar weight scales the coordinate influence bound. -/
theorem weighted_sum_sq_linearForm_update_le (y : J → ℝ)
    (hy : ∀ j, y j ∈ Set.Icc lam lam⁻¹) (j : J)
    {t : ℝ} (ht : t ∈ Set.Icc lam lam⁻¹) (w : ℝ) (hw : 0 ≤ w) :
    |w * ∑ k, (∑ i, B k i * (y i - m)) ^ 2 -
        w * ∑ k, (∑ i, B k i * (Function.update y j t i - m)) ^ 2| ≤
      w * (2 * lam⁻¹ ^ 2 * ∑ k, |B k j| * ∑ i, |B k i|) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (sum_sq_linearForm_update_le hlam B hm y hy j ht) hw

end LongRange
