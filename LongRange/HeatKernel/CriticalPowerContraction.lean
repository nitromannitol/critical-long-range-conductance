import LongRange.HeatKernel.CriticalPowerEnergy

/-!
# Contraction of iterated Markov operators

Squared norms of iterates decrease with time.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The norm of the iterates of a symmetric Markov operator is antitone in time. -/
theorem antitone_norm_markovOperatorCLM_pow {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : lp (fun _ : X => ℝ) 2) :
    Antitone (fun n : ℕ => ‖(markovOperatorCLM k hk hsym ^ n) f‖) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [pow_succ', mul_apply_eq_comp]
  exact norm_markovOperator_le k hk hsym _

/-- The loss of squared norm of Markov iterates increases with time. -/
theorem markovOperatorCLM_pow_norm_sq_loss_le {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : lp (fun _ : X => ℝ) 2) {m n : ℕ} (hmn : m ≤ n) :
    ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ m) f‖ ^ 2 ≤
      ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 := by
  have h := antitone_norm_markovOperatorCLM_pow k hk hsym f hmn
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 h
  exact sub_le_sub_left hs _

end LatticeProb.Graph.LongRangeKernel
