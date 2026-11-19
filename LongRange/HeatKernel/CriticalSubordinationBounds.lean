import LongRange.HeatKernel.CriticalSubordination

/-!
# Bounds for quadratic-scale subordination

A block of subordination weights at a fixed scale contributes the expected
inverse-square mass.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- A coefficient in the block from `r` to `2r` is bounded below at cubic scale. -/
theorem criticalSubordinationCoefficient_block_lower {r j : ℕ} (hr : 1 ≤ r)
    (hjhi : j + 1 ≤ 2 * r) :
    1 / (18 * (r : ℝ) ^ 3) ≤ criticalSubordinationCoefficient j := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hjR : ((j : ℝ) + 1) ≤ 2 * r := by exact_mod_cast hjhi
  have h1 : 0 ≤ (j : ℝ) + 1 := by positivity
  have h2 : 0 ≤ 1 + ((j : ℝ) + 1) := by positivity
  have h3 : 1 + ((j : ℝ) + 1) ≤ 3 * r := by linarith
  have hsq : (1 + ((j : ℝ) + 1)) ^ 2 ≤ (3 * (r : ℝ)) ^ 2 :=
    pow_le_pow_left₀ h2 h3 2
  have hprod : ((j : ℝ) + 1) * (1 + ((j : ℝ) + 1)) ^ 2 ≤
      (2 * (r : ℝ)) * (3 * (r : ℝ)) ^ 2 :=
    mul_le_mul hjR hsq (sq_nonneg _) (by positivity)
  unfold criticalSubordinationCoefficient quadraticScale
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The coefficients in a dyadic block have inverse-square total mass. -/
theorem criticalSubordinationCoefficient_block_sum_lower {r : ℕ} (hr : 1 ≤ r) :
    1 / (18 * (r : ℝ) ^ 2) ≤
      ∑ j ∈ Finset.Ico (r - 1) (2 * r - 1), criticalSubordinationCoefficient j := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hsum : (∑ _j ∈ Finset.Ico (r - 1) (2 * r - 1),
      (1 / (18 * (r : ℝ) ^ 3))) ≤
      ∑ j ∈ Finset.Ico (r - 1) (2 * r - 1), criticalSubordinationCoefficient j := by
    apply Finset.sum_le_sum
    intro j hj
    have hh := Finset.mem_Ico.mp hj
    exact criticalSubordinationCoefficient_block_lower hr (by omega)
  have hcard : (Finset.Ico (r - 1) (2 * r - 1)).card = r := by
    rw [Nat.card_Ico]
    omega
  have heq : (∑ _j ∈ Finset.Ico (r - 1) (2 * r - 1),
      (1 / (18 * (r : ℝ) ^ 3))) = 1 / (18 * (r : ℝ) ^ 2) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  linarith

/-- A lower bound for each power in a block transfers to the subordinated density. -/
theorem criticalSubordinateDensity_ge_of_block {X : Type*} (m : X → ℝ≥0)
    (q : X → X → ℝ≥0∞) (x y : X) {r : ℕ} (hr : 1 ≤ r) (B : ℝ≥0∞)
    (hB : ∀ j ∈ Finset.Ico (r - 1) (2 * r - 1),
      B ≤ densityPower m q (2 * (j + 1) ^ 2) x y) :
    ((∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j))⁻¹ *
      ENNReal.ofReal (1 / (18 * (r : ℝ) ^ 2))) * B ≤
      criticalSubordinateDensity m q x y := by
  let s := Finset.Ico (r - 1) (2 * r - 1)
  let a := (∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j))⁻¹
  have hc : ENNReal.ofReal (1 / (18 * (r : ℝ) ^ 2)) ≤
      ∑ j ∈ s, ENNReal.ofReal (criticalSubordinationCoefficient j) := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · exact ENNReal.ofReal_le_ofReal (criticalSubordinationCoefficient_block_sum_lower hr)
    · intro j hj
      unfold criticalSubordinationCoefficient quadraticScale
      positivity
  calc
    _ ≤ (a * ∑ j ∈ s, ENNReal.ofReal (criticalSubordinationCoefficient j)) * B := by
      gcongr
    _ = ∑ j ∈ s, criticalSubordinationWeight j * B := by
      rw [Finset.mul_sum, Finset.sum_mul]
      rfl
    _ ≤ ∑ j ∈ s, criticalSubordinationWeight j *
        densityPower m q (2 * (j + 1) ^ 2) x y := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      exact hB j hj
    _ ≤ criticalSubordinateDensity m q x y := by
      exact ENNReal.sum_le_tsum s

end LatticeProb.Graph.LongRangeKernel
