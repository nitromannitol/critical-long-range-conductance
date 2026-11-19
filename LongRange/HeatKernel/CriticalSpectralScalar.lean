import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

/-!
# Scalar estimate for powers of a symmetric contraction

The multiplier in the Dirichlet-form comparison is nonpositive on the
spectral interval of a symmetric Markov operator.
-/

namespace LatticeProb.Graph.LongRangeKernel

/-- The spectral multiplier in the comparison of iterated Dirichlet forms. -/
theorem one_sub_pow_le_nat_mul_one_sub {t : ℝ} (ht : |t| ≤ 1) (n : ℕ) :
    1 - t ^ n ≤ (n : ℝ) * (1 - t) := by
  have ht1 : t ≤ 1 := (le_abs_self t).trans ht
  have hp (m : ℕ) : t ^ m ≤ 1 := by
    calc
      t ^ m ≤ |t ^ m| := le_abs_self _
      _ = |t| ^ m := abs_pow t m
      _ ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
  induction n with
  | zero => simp
  | succ n ih =>
      have hm : t ^ n * (1 - t) ≤ 1 - t := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (hp n)) (sub_nonneg.mpr ht1)]
      rw [pow_succ, Nat.cast_succ]
      nlinarith

end LatticeProb.Graph.LongRangeKernel
