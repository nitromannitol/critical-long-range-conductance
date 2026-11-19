import LongRange.HeatKernel.CriticalOperatorHilbert
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positivity of Markov operator defects

The sum and difference of the identity and a symmetric Markov contraction are positive.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The defect of a symmetric Markov operator is positive. -/
theorem markovOperatorCLM_one_sub_positive {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) :
    (1 - markovOperatorCLM k hk hsym).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact (show IsSelfAdjoint (1 : lp (fun _ : X => ℝ) 2 →L[ℝ] lp (fun _ : X => ℝ) 2) by
      simp [IsSelfAdjoint]).sub (markovOperatorCLM_isSelfAdjoint k hk hsym)
  · intro f
    change 0 ≤ inner ℝ (f - markovOperatorCLM k hk hsym f) f
    rw [← realKernelEnergy_eq_inner k hk hsym f]
    unfold realKernelEnergy
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun x => tsum_nonneg (fun y =>
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))

/-- The identity plus a symmetric Markov operator is positive. -/
theorem markovOperatorCLM_one_add_positive {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) :
    (1 + markovOperatorCLM k hk hsym).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact (show IsSelfAdjoint (1 : lp (fun _ : X => ℝ) 2 →L[ℝ] lp (fun _ : X => ℝ) 2) by
      simp [IsSelfAdjoint]).add (markovOperatorCLM_isSelfAdjoint k hk hsym)
  · intro f
    change 0 ≤ inner ℝ (f + markovOperatorCLM k hk hsym f) f
    rw [inner_add_left, real_inner_self_eq_norm_sq]
    have h := neg_le_of_abs_le (abs_real_inner_le_norm (markovOperatorCLM k hk hsym f) f)
    have hc : ‖markovOperatorCLM k hk hsym f‖ ≤ ‖f‖ := norm_markovOperator_le k hk hsym f
    have hn := norm_nonneg f
    nlinarith

end LatticeProb.Graph.LongRangeKernel
