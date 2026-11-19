import LongRange.HeatKernel.CriticalAverageL1
import LongRange.HeatKernel.CriticalEnergyReal

/-!
# Energy bound for the Nash inequality

The energy of a symmetric Markov kernel is controlled by the square of the
absolute sum, as used in the choice of radius in the Nash inequality.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The square sum is at most the square of the absolute sum. -/
theorem tsum_sq_le_tsum_abs_sq {G : Type*} [AddCommGroup G]
    (f : G → ℝ) (hf : Summable (fun x => |f x|)) :
    (∑' x, f x ^ 2) ≤ (∑' x, |f x|) ^ 2 := by
  classical
  have h := finsetTranslateAverage_sq_tsum_le_abs_tsum ({0} : Finset G)
    (Finset.singleton_nonempty 0) f hf
  simpa [finsetTranslateAverage] using h.2

/-- The energy-to-absolute-sum bound used in the Nash optimization. -/
theorem realKernelEnergy_le_two_tsum_abs_sq {G : Type*} [AddCommGroup G]
    (k : G → G → ℝ≥0∞) (hk : ∀ x, ∑' y, k x y = 1)
    (hsym : ∀ x y, k x y = k y x) (f : lp (fun _ : G => ℝ) 2)
    (hf : Summable (fun x => |f x|)) :
    realKernelEnergy k f ≤ 2 * (∑' x, |f x|) ^ 2 := by
  have hs : Summable (fun x => f x ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have htop : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
    exact ENNReal.ofReal_lt_top
  have hb := symmetric_markov_energy_le k hk hsym f
  have hb' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) htop.ne) hb
  rw [realKernelEnergy_eq_toReal k hk hsym f htop]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.tsum_toReal_eq (fun x => ENNReal.ofReal_ne_top),
    tsum_congr (fun x => ENNReal.toReal_ofReal (sq_nonneg _))] at hb'
  have hsq := tsum_sq_le_tsum_abs_sq f hf
  linarith

end LatticeProb.Graph.LongRangeKernel
