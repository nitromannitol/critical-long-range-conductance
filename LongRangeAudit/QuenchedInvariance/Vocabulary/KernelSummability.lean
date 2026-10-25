import LongRangeAudit.QuenchedInvariance.Vocabulary.KappaPositivity

/-! # Independent KernelSummability vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The critical jump kernel is nonnegative. -/
theorem jumpKernel_nonneg (z : Fin d → ℝ) : 0 ≤ jumpKernel z := by
  unfold jumpKernel
  split
  · exact le_rfl
  · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)

/-- Physical scaling factors out of the critical kernel at nonzero integer sites. -/
theorem jumpKernel_physical {ε : ℝ} (hε : 0 < ε) {w : Site d} (hw : w ≠ 0) :
    jumpKernel (physical ε w) = (ε ^ (d + 2))⁻¹ *
      (radius (physical 1 w) ^ (d + 2))⁻¹ := by
  rw [jumpKernel_of_ne_zero (fun h => hw ((physical_eq_zero_iff hε w).mp h)),
    radius_physical_eq_mul hε.le, mul_pow, mul_inv_rev, mul_comm]

/-- A scaled kernel first moment is dominated by the unscaled Euclidean radial error. -/
theorem jumpKernel_weight_le {ε : ℝ} (hε : 0 < ε) {w : Site d} (hw : w ≠ 0) :
    jumpKernel (physical ε w) * (1 + radius (physical ε w)) ≤
      ((ε ^ (d + 2))⁻¹ * (1 + ε)) * (radius (physical 1 w) ^ (d + 1))⁻¹ := by
  have hr := lattice_radius_ge_one hw
  have hrpos : 0 < radius (physical 1 w) := lt_of_lt_of_le zero_lt_one hr
  rw [jumpKernel_physical hε hw, radius_physical_eq_mul hε.le]
  have hpow : radius (physical 1 w) ^ (d + 2) =
      radius (physical 1 w) ^ (d + 1) * radius (physical 1 w) := by
    rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
  have hbase : (1 + ε * radius (physical 1 w)) ≤
      (1 + ε) * radius (physical 1 w) := by nlinarith
  calc
    _ ≤ (ε ^ (d + 2))⁻¹ * (radius (physical 1 w) ^ (d + 2))⁻¹ *
        ((1 + ε) * radius (physical 1 w)) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _))
          (inv_nonneg.mpr (pow_nonneg hrpos.le _)))
    _ = _ := by
      rw [hpow, mul_inv_rev]
      calc
        _ = (ε ^ (d + 2))⁻¹ * (1 + ε) *
            (radius (physical 1 w) ^ (d + 1))⁻¹ *
              ((radius (physical 1 w))⁻¹ * radius (physical 1 w)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hrpos.ne', mul_one]

/-- The Euclidean kernel with its first physical moment is summable. -/
theorem summable_jumpKernel_weight (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun w : Site d =>
      jumpKernel (physical ε w) * (1 + radius (physical ε w))) := by
  have hexp : -(d : ℝ) - 1 = -((d + 1 : ℕ) : ℝ) := by push_cast; ring
  have herr : Summable (fun w : {w : Site d // w ≠ 0} =>
      (radius (physical 1 w.val) ^ (d + 1))⁻¹) := by
    have hs := LatticeProb.Euclidean.Summability.nonzero_radial_error_summable_real d hd
    refine hs.congr (fun w => ?_)
    rw [hexp, Real.rpow_eq_pow, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have hsub : Summable (fun w : {w : Site d // w ≠ 0} =>
      jumpKernel (physical ε w.val) * (1 + radius (physical ε w.val))) := by
    refine (herr.mul_left ((ε ^ (d + 2))⁻¹ * (1 + ε))).of_norm_bounded ?_
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (jumpKernel_nonneg _)
      (add_nonneg zero_le_one (radius_nonneg _)))]
    exact jumpKernel_weight_le hε w.property
  have hzero : jumpKernel (physical ε (0 : Site d)) *
      (1 + radius (physical ε (0 : Site d))) = 0 := by
    rw [(physical_eq_zero_iff hε 0).mpr rfl, jumpKernel_zero, zero_mul]
  have hsupp : Function.support (fun w : Site d =>
      jumpKernel (physical ε w) * (1 + radius (physical ε w))) ⊆ {w | w ≠ 0} := by
    intro w hw
    change w ≠ 0
    intro hz
    subst w
    exact hw hzero
  exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hsub.hasSum).summable

/-- The unweighted Euclidean jump kernel is summable. -/
theorem summable_jumpKernel (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun w : Site d => jumpKernel (physical ε w)) := by
  refine (summable_jumpKernel_weight hd hε).of_nonneg_of_le
    (fun w => jumpKernel_nonneg _) ?_
  intro w
  exact le_mul_of_one_le_right (jumpKernel_nonneg _) (by
    linarith [radius_nonneg (physical ε w)])

end LongRange
end

end LongRangeAudit.QuenchedInvariance
