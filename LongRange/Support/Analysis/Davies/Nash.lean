import LongRange.Support.Analysis.Davies.FiniteForm

/-!
# Scaling the finite Nash inequality

The normalized Nash inequality implies its homogeneous form for nonzero finite functions.
-/

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] (F : FiniteJumpForm ι)

/-- Homogeneous form of the normalized finite Nash inequality. -/
theorem nash_scaled {θ : ℝ → ℝ} {δ : ℝ} (hN : F.Nash θ δ) (w : ι → ℝ)
    (hS : 0 < ∑ i, |w i|) (hB : 0 < ∑ i, (w i) ^ 2) :
    (∑ i, |w i|) ^ 2 * θ ((∑ i, (w i) ^ 2) / (∑ i, |w i|) ^ 2) ≤
      F.form w w + δ * ∑ i, (w i) ^ 2 := by
  let S := ∑ i, |w i|
  let B := ∑ i, (w i) ^ 2
  let g : ι → ℝ := S⁻¹ • w
  have hS0 : 0 < S := hS
  have hB0 : 0 < B := hB
  have hg1 : (∑ i, |g i|) = 1 := by
    dsimp [g]
    simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr hS0.le),
      ← Finset.mul_sum]
    change S⁻¹ * S = 1
    exact inv_mul_cancel₀ hS0.ne'
  have hg2 : (∑ i, (g i) ^ 2) = B / S ^ 2 := by
    dsimp [g]
    simp only [mul_pow, ← Finset.mul_sum]
    change S⁻¹ ^ 2 * B = B / S ^ 2
    field_simp
  have hgpos : 0 < ∑ i, (g i) ^ 2 := by
    rw [hg2]
    exact div_pos hB0 (sq_pos_of_pos hS0)
  have hform : F.form g g = (S⁻¹) ^ 2 * F.form w w := F.form_smul_smul S⁻¹ w w
  have h := hN g hg1.le hgpos
  rw [hg2, hform] at h
  have hSsq : 0 < S ^ 2 := sq_pos_of_pos hS0
  have hs := mul_le_mul_of_nonneg_left h hSsq.le
  change S ^ 2 * θ (B / S ^ 2) ≤ F.form w w + δ * B
  convert hs using 1; field_simp

end
end LatticeProb.Davies.FiniteJumpForm
