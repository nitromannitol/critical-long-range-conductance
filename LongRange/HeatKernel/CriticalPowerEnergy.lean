import LongRange.HeatKernel.CriticalOperatorPower

/-!
# Energies of even Markov powers

The Dirichlet energy of an even power is the loss of squared Hilbert norm.
-/

open scoped NNReal ENNReal InnerProductSpace

namespace LatticeProb.Graph.LongRangeKernel

/-- The energy of an even power equals the loss of squared norm at half the time. -/
theorem realKernelEnergy_densityPower_two_mul {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (n : ℕ) (f : lp (fun _ : X => ℝ) 2) :
    realKernelEnergy (densityPower (fun _ => 1) k (2 * n)) f =
      ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 := by
  let T := markovOperatorCLM k hk hsym
  have hp : ∀ x, ∑' y, densityPower (fun _ => 1) k (2 * n) x y = 1 := by
    have h := densityPower_isMarkov (fun _ : X => 1) (by simp) k
      (by simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using hk) (2 * n)
    simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using h
  have hs := densityPower_symmetric (fun _ : X => 1) (by simp) k hsym (2 * n)
  rw [realKernelEnergy_eq_inner _ hp hs f]
  have heq : markovOperatorCLM (densityPower (fun _ => 1) k (2 * n)) hp hs f =
      (T ^ (2 * n)) f := by
    apply lp.ext
    funext x
    exact densityPower_apply_eq_operator_pow k hk hsym (2 * n) f x
  rw [heq, inner_sub_left, real_inner_self_eq_norm_sq]
  have hsympow : IsSelfAdjoint (T ^ n) :=
    (markovOperatorCLM_isSelfAdjoint k hk hsym).pow n
  have hi := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsympow) ((T ^ n) f) f
  change ⟪(T ^ n) ((T ^ n) f), f⟫_ℝ = ⟪(T ^ n) f, (T ^ n) f⟫_ℝ at hi
  rw [show 2 * n = n + n by omega, pow_add, mul_apply_eq_comp, hi,
    real_inner_self_eq_norm_sq]

end LatticeProb.Graph.LongRangeKernel
