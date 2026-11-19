import LongRange.HeatKernel.CriticalSubordinatePoincare
import LongRange.HeatKernel.CriticalSubordinationLog

/-!
# Logarithmic pseudo-Poincaré bound

The quadratic subordination gives the critical logarithmic improvement.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The subordinate energy controls ball averages with a logarithmic factor. -/
theorem weightedLattice_subordinate_pseudoPoincare {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ f : lp (fun _ : Site d => ℝ) 2,
      Summable (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
      Real.log (1 + R) *
          (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
        C * R ^ 2 * realKernelEnergy
          (criticalSubordinateDensity (weightedLattice d hd).mass
            (averagedDensity (weightedLattice d hd).mass
              (weightedLattice d hd).referenceDensity)) f := by
  obtain ⟨A, hA, henergy⟩ := weightedLattice_subordinate_energy_lower hd
  obtain ⟨c, hc, hlog⟩ := criticalSubordinationWeight_log_lower
  refine ⟨A / c, by positivity, ?_⟩
  intro R hR f
  have hD : 0 ≤ ∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2 :=
    tsum_nonneg (fun _ => sq_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_left (hlog R hR) hD
  have hsecond := (henergy R hR f).2
  have hprod : c * (Real.log (1 + R) *
      (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2)) ≤
      A * R ^ 2 * realKernelEnergy
        (criticalSubordinateDensity (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity)) f := by
    nlinarith
  refine ⟨(henergy R hR f).1, ?_⟩
  have hdiv := (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hprod)
  convert hdiv using 1
  ring

end LatticeProb.Graph.LongRangeKernel
