import LongRange.HeatKernel.CriticalEnergyReal

/-!
# Comparing symmetric Markov energies

An off-diagonal kernel comparison transfers to the associated Dirichlet energies.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- Off-diagonal domination bounds the corresponding real kernel energies. -/
theorem realKernelEnergy_le_of_offDiag {X : Type*} (p q : X → X → ℝ≥0∞)
    (hp : ∀ x, ∑' y, p x y = 1) (hq : ∀ x, ∑' y, q x y = 1)
    (hps : ∀ x y, p x y = p y x) (hqs : ∀ x y, q x y = q y x)
    (C : ℝ)
    (hbound : ∀ x y, x ≠ y → (p x y).toReal ≤ C * (q x y).toReal)
    (f : X → ℝ) (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    realKernelEnergy p f ≤ C * realKernelEnergy q f := by
  have hrow (x : X) :
      (∑' y, (p x y).toReal * (f x - f y) ^ 2) ≤
        C * ∑' y, (q x y).toReal * (f x - f y) ^ 2 := by
    rw [← tsum_mul_left]
    apply (summable_real_kernel_energy_row p hp hps f hf x).tsum_le_tsum _
      ((summable_real_kernel_energy_row q hq hqs f hf x).mul_left C)
    intro y
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
    · have h := mul_le_mul_of_nonneg_right (hbound x y hxy) (sq_nonneg (f x - f y))
      nlinarith
  have houter := (summable_real_kernel_energy p hp hps f hf).tsum_le_tsum hrow
    ((summable_real_kernel_energy q hq hqs f hf).mul_left C)
  rw [tsum_mul_left] at houter
  unfold realKernelEnergy
  nlinarith

end LatticeProb.Graph.LongRangeKernel
