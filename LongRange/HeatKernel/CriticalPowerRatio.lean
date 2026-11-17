import LongRange.HeatKernel.CriticalPowerLoss

/-!
# Comparing losses at two times

A ceiling number of blocks controls the loss at a later time.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The loss at time `n` is bounded by twice the ratio `n / b` times the loss at time `b`. -/
theorem markovOperatorCLM_norm_sq_loss_le_ratio {V : Type*} (k : V → V → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (b n : ℕ) (hb : 0 < b) (hbn : b ≤ n) (f : lp (fun _ : V => ℝ) 2) :
    ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 ≤
      (2 * (n : ℝ) / b) * (‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ b) f‖ ^ 2) := by
  let m := n / b + 1
  have hmod := Nat.mod_lt n hb
  have hdiv := Nat.mod_add_div n b
  have hn : n ≤ m * b := by dsimp [m]; nlinarith
  have hmb : m * b ≤ 2 * n := by
    have h := Nat.div_mul_le_self n b
    dsimp [m]
    nlinarith
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hmbR : (m : ℝ) * b ≤ 2 * (n : ℝ) := by exact_mod_cast hmb
  have hratio : (m : ℝ) ≤ 2 * (n : ℝ) / b := (le_div_iff₀ hbR).2 hmbR
  have hloss : 0 ≤ ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ b) f‖ ^ 2 := by
    have h := markovOperatorCLM_pow_norm_sq_loss_le k hk hsym f (Nat.zero_le b)
    simpa only [pow_zero, one_apply_eq_self, sub_self] using h
  exact (markovOperatorCLM_norm_sq_loss_le_blocks k hk hsym b m n hn f).trans
    (mul_le_mul_of_nonneg_right hratio hloss)

end LatticeProb.Graph.LongRangeKernel
