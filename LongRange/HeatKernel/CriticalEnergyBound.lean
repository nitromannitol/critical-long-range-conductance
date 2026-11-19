import LongRange.HeatKernel.CriticalSubordination

/-!
# Finite energy of symmetric Markov kernels

The energy of a square-summable function is finite for a symmetric Markov
kernel on counting measure.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The unhalved kernel energy is at most four times the squared norm. -/
theorem symmetric_markov_energy_le {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ) :
    (∑' x, ∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) ≤
      4 * ∑' x, ENNReal.ofReal (f x ^ 2) := by
  let u : X → ℝ≥0∞ := fun x => ENNReal.ofReal (f x ^ 2)
  have hxy (x y : X) : ENNReal.ofReal ((f x - f y) ^ 2) ≤ 2 * (u x + u y) := by
    have h : (f x - f y) ^ 2 ≤ 2 * (f x ^ 2 + f y ^ 2) := by
      nlinarith [sq_nonneg (f x + f y)]
    have := ENNReal.ofReal_le_ofReal h
    simpa [u, ENNReal.ofReal_mul, ENNReal.ofReal_add (sq_nonneg (f x)) (sq_nonneg (f y))] using this
  have hrow : (∑' x, ∑' y, k x y * u x) = ∑' x, u x := by
    apply tsum_congr
    intro x
    rw [ENNReal.tsum_mul_right, hk x, one_mul]
  have hcol : (∑' x, ∑' y, k x y * u y) = ∑' y, u y := by
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro y
    simp_rw [hsym]
    rw [ENNReal.tsum_mul_right, hk y, one_mul]
  calc
    _ ≤ ∑' x, ∑' y, 2 * (k x y * u x + k x y * u y) := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply ENNReal.tsum_le_tsum
      intro y
      calc
        _ ≤ k x y * (2 * (u x + u y)) := by
          simpa only [mul_comm] using mul_le_mul_left (hxy x y) (k x y)
        _ = _ := by ring
    _ = 2 * ((∑' x, ∑' y, k x y * u x) + ∑' x, ∑' y, k x y * u y) := by
      simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ = _ := by rw [hrow, hcol]; simp only [u]; ring

/-- Square-summability makes the unhalved energy finite. -/
theorem symmetric_markov_energy_lt_top {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    (∑' x, ∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) < ∞ :=
  lt_of_le_of_lt (symmetric_markov_energy_le k hk hsym f)
    (ENNReal.mul_lt_top (by simp) hf)

end LatticeProb.Graph.LongRangeKernel
