import LongRange.HeatKernel.CriticalSubordinationBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tail bound for quadratic subordination

The integral comparison controls the tail of the subordination coefficients.
-/

open scoped NNReal ENNReal
open Set MeasureTheory

namespace LatticeProb.Graph.LongRangeKernel

/-- The tail of the quadratic subordination coefficients has inverse-square decay. -/
theorem criticalSubordinationCoefficient_tail_le {r : ℕ} (hr : 1 ≤ r) :
    (∑' j : ℕ, criticalSubordinationCoefficient (j + r)) ≤ 1 / (2 * (r : ℝ) ^ 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let f : ℝ → ℝ := fun x => x ^ (-3 : ℝ)
  have ha : AntitoneOn f (Ici (r : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hrR.trans_le hx) hxy (by norm_num)
  have hi : IntegrableOn f (Ioi (r : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hrR
  have hn : ∀ t ∈ Ioi (r : ℝ), 0 ≤ f t := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (hrR.trans ht)) _
  have ht := ha.tsum_comp_add_le_integral r hi hn
  have hint : (∫ t in Ioi (r : ℝ), f t) = 1 / (2 * (r : ℝ) ^ 2) := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by norm_num) hrR]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    ring
  rw [hint] at ht
  apply le_trans _ ht
  apply Summable.tsum_le_tsum
  · intro j
    have hpos : (0 : ℝ) < (j : ℝ) + r + 1 := by positivity
    unfold criticalSubordinationCoefficient quadraticScale f
    push_cast
    rw [Real.rpow_neg, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [← one_div (((j : ℝ) + r + 1) ^ 3)]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      ((j : ℝ) + r + 1) ^ 3 = ((j : ℝ) + r + 1) * ((j : ℝ) + r + 1) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hpos.le (by linarith) 2) hpos.le
    positivity
  · exact summable_criticalSubordinationCoefficient.comp_injective (fun _ _ h => by omega)
  · exact (ha.summable_of_integrableOn_Ioi hi hn).comp_injective (fun _ _ h => by omega)

end LatticeProb.Graph.LongRangeKernel
