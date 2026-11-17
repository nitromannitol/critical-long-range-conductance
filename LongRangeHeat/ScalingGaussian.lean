import LongRangeHeat.Continuum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Large-time Gaussian bound

The heat kernel is bounded above by its value at the origin, which tends to zero as time tends
to infinity in positive dimension.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb.Heat
open scoped Topology

noncomputable section

/-- A positive-time heat kernel is bounded by its Gaussian prefactor. -/
theorem heatKernel_le_gaussian_prefactor {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    (z : Fin d → ℝ) :
    heatKernel d t z ≤ ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2)) ^ d := by
  rw [heatKernel_of_pos ht]
  calc
    _ ≤ ∏ _i : Fin d, ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2)) := by
      refine Finset.prod_le_prod₀ (fun i _ => (heatKernel1_pos hd ht (z i)).le) ?_
      intro i hi
      unfold heatKernel1
      apply mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
      rw [Real.exp_le_one_iff]
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd0) (sq_nonneg _)) (by positivity)
    _ = _ := by simp

/-- The Gaussian prefactor tends to zero at large times in positive dimension. -/
theorem tendsto_gaussian_prefactor_atTop {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun t : ℝ => ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2)) ^ d)
      atTop (𝓝 0) := by
  have hc : 0 < 2 * Real.pi / (d : ℝ) := by positivity
  have ht : Tendsto (fun t : ℝ => 2 * Real.pi * t / d) atTop atTop := by
    convert Tendsto.const_mul_atTop hc tendsto_id using 1
    ext t
    simp only [id_eq]
    ring
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp ht).pow d
  simpa only [Function.comp_apply, neg_div, zero_pow (by omega : d ≠ 0)] using h


/-- The continuum heat flow of continuous compactly supported data tends to zero at large times. -/
theorem tendsto_continuumHeat_atTop {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : Fin d → ℝ) : Tendsto (fun t : ℝ => continuumHeat f t x) atTop (𝓝 0) := by
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hb (t : ℝ) (ht : 0 < t) :
      ‖continuumHeat f t x‖ ≤
        ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2)) ^ d * ∫ y, ‖f y‖ := by
    have hk : Continuous (fun y => heatKernel d t (x - y)) :=
      (continuous_heatKernel ht).comp (continuous_const.sub continuous_id)
    have hi : Integrable (fun y => heatKernel d t (x - y) * f y) :=
      (hk.mul hf).integrable_of_hasCompactSupport hfc.mul_left
    simp only [continuumHeat, ht.ne', ↓reduceIte]
    calc
      ‖∫ y, heatKernel d t (x - y) * f y‖ ≤
          ∫ y, ‖heatKernel d t (x - y) * f y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2)) ^ d * ‖f y‖ := by
        apply integral_mono hi.norm (hfint.norm.const_mul _)
        intro y
        change ‖heatKernel d t (x - y) * f y‖ ≤
          ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2)) ^ d * ‖f y‖
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hd t _)]
        exact mul_le_mul_of_nonneg_right (heatKernel_le_gaussian_prefactor hd ht _) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hb t ht
  · simpa only [zero_mul] using (tendsto_gaussian_prefactor_atTop hd).mul
      (tendsto_const_nhds (x := ∫ y, ‖f y‖))

end
end LongRangeHeat
