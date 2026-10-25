import LongRange.Poincare.Slab
import LongRange.Model.Kernel

/-!
# Euclidean kernel mass on the forward box

The Euclidean radius bound on the half-slab gives a lower bound for each kernel value.
Summing over its exact cardinality yields the required inverse-square scale mass.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- Every point of the forward box is nonzero. -/
theorem forwardBox_ne_zero {d k : ℕ} {z : Site (d + 1)}
    (hz : z ∈ forwardBox d k) : z ≠ 0 := by
  intro h
  have hp := (mem_forwardBox.mp hz).1
  rw [h, Pi.zero_apply] at hp
  exact (not_le_of_gt (pow_pos (by norm_num : (0 : ℤ) < 3) k)) hp

/-- The pointwise kernel lower bound uses the Euclidean radius, not the shell norm. -/
theorem forwardBox_kernel_lower {d k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {z : Site (d + 1)} (hz : z ∈ forwardBox d k) :
    ((3 * (d + 1 : ℕ) * (ε * 3 ^ k)) ^ (d + 3))⁻¹ ≤
      jumpKernel (physical ε z) := by
  rw [jumpKernel_of_ne_zero ((physical_eq_zero_iff hε z).not.mpr
    (forwardBox_ne_zero hz))]
  apply inv_anti₀ (pow_pos (radius_pos
    ((physical_eq_zero_iff hε z).not.mpr (forwardBox_ne_zero hz))) _)
  exact pow_le_pow_left₀ (radius_nonneg _) (forwardBox_radius_le hε hz) _

/-- Summing the pointwise bound gives a positive quantitative lower bound for slab mass. -/
theorem forwardBox_mass_lower (d k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (3 ^ k : ℝ) ^ (d + 1) *
        ((3 * (d + 1 : ℕ) * (ε * 3 ^ k)) ^ (d + 3))⁻¹ ≤
      ∑ z ∈ forwardBox d k, jumpKernel (physical ε z) := by
  calc
    _ = ∑ _z ∈ forwardBox d k,
        ((3 * (d + 1 : ℕ) * (ε * 3 ^ k)) ^ (d + 3))⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul, card_forwardBox]
      push_cast
      rfl
    _ ≤ _ := Finset.sum_le_sum (fun _ hz => forwardBox_kernel_lower hε hz)

end

end LongRange.Poincare
