import LongRange.Support.Analysis.Davies.Comparison
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Constants for the Davies iteration

Geometric sums and bounds for the time grid used in the iteration.
-/

namespace LatticeProb.Davies

open Filter
open scoped Topology

noncomputable section

/-- The exponential correction on the geometric time grid has a finite sum. -/
theorem hasSum_davies_correction {l : ℝ} (hl : 2 < l) :
    HasSum (fun n : ℕ ↦ 3 * (2 / l) ^ (n + 1)) (6 / (l - 2)) := by
  have hlpos : 0 < l := by linarith
  have hq0 : 0 ≤ 2 / l := by positivity
  have hq1 : 2 / l < 1 := (div_lt_one hlpos).2 hl
  have hsum := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (3 * (2 / l))
  convert hsum using 1
  · ext n
    rw [pow_succ]
    ring
  · field_simp
    <;> ring

/-- The geometric sum controlling the contribution of the killing parameter. -/
theorem hasSum_davies_killing {l : ℝ} (hl : 2 < l) :
    HasSum (fun n : ℕ ↦ (1 / (2 * l)) ^ n) (2 * l / (2 * l - 1)) := by
  have hden : 0 < 2 * l := by linarith
  have hq0 : 0 ≤ 1 / (2 * l) := by positivity
  have hq1 : 1 / (2 * l) < 1 := (div_lt_one hden).2 (by linarith)
  have hsum := hasSum_geometric_of_lt_one hq0 hq1
  convert hsum using 1
  field_simp
  <;> ring

/-- The time-grid coefficient multiplying the killing parameter is at most one. -/
theorem davies_killing_coefficient_le_one {l : ℝ} (hl : 2 < l) :
    2 * (l - 1) / (2 * l - 1) ≤ 1 := by
  have hden : 0 < 2 * l - 1 := by linarith
  apply (div_le_one hden).2
  linarith

/-- The choice of the geometric parameter gives the desired perturbation exponent. -/
theorem davies_exponent_coefficient_le {l ε : ℝ} (hε : 0 < ε)
    (hl : 2 < l) (hchoice : 2 + 6 / ε ≤ l) :
    (l - 1) / l * (1 + 6 / (l - 2)) ≤ 1 + ε := by
  have hlpos : 0 < l := by linarith
  have hltwo : 0 < l - 2 := by linarith
  have hεbound : 6 ≤ ε * (l - 2) := by
    have := (div_le_iff₀ hε).1 (show 6 / ε ≤ l - 2 by linarith)
    nlinarith
  have hratio : (l - 1) / l ≤ 1 := (div_le_one hlpos).2 (by linarith)
  have hratio0 : 0 ≤ (l - 1) / l := div_nonneg (by linarith) hlpos.le
  have hcorr : 6 / (l - 2) ≤ ε := (div_le_iff₀ hltwo).2 hεbound
  nlinarith [mul_le_mul_of_nonneg_left hcorr hratio0,
    mul_le_mul_of_nonneg_right hratio hε.le]

end
end LatticeProb.Davies
