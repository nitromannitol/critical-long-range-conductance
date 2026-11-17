import LongRange.HeatKernel.CriticalKernelPoincare
import LongRange.HeatKernel.CriticalLatticeAverageL1

/-!
# Two-term estimate for the critical Nash inequality

A ball average splits the square sum into a pseudo-Poincaré term and an
absolute-sum term.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The two-term critical estimate preceding Nash optimization. -/
theorem weightedLattice_critical_two_term {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (R : ℝ), 1 ≤ R → ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => |f x|) →
        (∑' x, f x ^ 2) ≤ A * (R ^ 2 / Real.log (1 + R)) * realKernelEnergy k f +
          B * (∑' x, |f x|) ^ 2 / latticeVolumeProfile d R := by
  obtain ⟨A, hA, hp⟩ := weightedLattice_critical_pseudoPoincare_all_radii hd C hC
  obtain ⟨B, hB, hb⟩ := latticeRealGraphBall_average_sq_le hd
  refine ⟨2 * A, 2 * B, by positivity, by positivity, ?_⟩
  intro k hk hsym hlower R hR f hf
  let a : Site d → ℝ := finsetTranslateAverage (latticeRealGraphBall d R) f
  have hlog : 0 < Real.log (1 + R) := Real.log_pos (by linarith)
  have hdiff := hp k hk hsym hlower R (by linarith) f
  have havg := hb R hR f hf
  have hsq : Summable (fun x => f x ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hmajor : Summable (fun x => 2 * (f x - a x) ^ 2 + 2 * (a x) ^ 2) :=
    (hdiff.1.mul_left 2).add (havg.1.mul_left 2)
  have hpoint (x : Site d) : f x ^ 2 ≤ 2 * (f x - a x) ^ 2 + 2 * (a x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 2 * a x)]
  have hsum := hsq.tsum_le_tsum hpoint hmajor
  rw [Summable.tsum_add (hdiff.1.mul_left 2) (havg.1.mul_left 2),
    tsum_mul_left, tsum_mul_left] at hsum
  have hD : (∑' x, (f x - a x) ^ 2) ≤
      (A * R ^ 2 * realKernelEnergy k f) / Real.log (1 + R) :=
    (le_div_iff₀ hlog).2 (by simpa only [mul_comm] using hdiff.2)
  have hh : (∑' x, f x ^ 2) ≤ 2 * ((A * R ^ 2 * realKernelEnergy k f) / Real.log (1 + R)) +
      2 * (B * (∑' x, |f x|) ^ 2 / latticeVolumeProfile d R) := by
    linarith [havg.2]
  convert hh using 1
  ring

end LatticeProb.Graph.LongRangeKernel
