import LongRangeHeat.UnscaledInvariance

/-!
# Scaling coefficients for the unscaled walk

The spacing and clock factors simplify to the normalization and Brownian variance in
Theorem 1.2.
-/

namespace LongRangeHeat

/-- The paper's spacing gives the spatial normalization of the unit walk. -/
theorem sqrt_mul_unscaledSpacing {A x : ℝ} (hA : 0 < A) :
    Real.sqrt (A / 2) * unscaledSpacing A x = (Real.sqrt (x * Real.log x))⁻¹ := by
  have hA' : 0 < A / 2 := by positivity
  have hs : 0 < Real.sqrt (A / 2) := Real.sqrt_pos.mpr hA'
  unfold unscaledSpacing
  have heq : A / 2 * x * Real.log x = A / 2 * (x * Real.log x) := by ring
  rw [heq, Real.sqrt_mul hA'.le, mul_inv_rev]
  field_simp

/-- The limiting spatial multiplier converts `d^(-1/2) W` to the stated covariance. -/
theorem sqrt_mul_dimension_rpow {A : ℝ} (hA : 0 ≤ A) {d : ℕ} :
    Real.sqrt (A / 2) * (d : ℝ) ^ (-(1 : ℝ) / 2) =
      Real.sqrt (A / (2 * d)) := by
  have hd' : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have he : -(1 : ℝ) / 2 = -((1 : ℝ) / 2) := by ring
  rw [he, Real.rpow_neg hd', ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
    ← Real.sqrt_div (by positivity)]
  congr 1
  ring

end LongRangeHeat
