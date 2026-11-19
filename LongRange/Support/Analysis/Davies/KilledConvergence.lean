import LongRange.Support.Prob.JumpChain.PositionFdd
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Exhaustion of killed jump kernels

Killed transition powers and their Poisson averages converge to their unrestricted
counterparts along the directed family of finite subsets of the state space.
-/

namespace LatticeProb.Davies

open Filter Set ProbabilityTheory
open scoped Topology NNReal

noncomputable section

variable {S : Type*} (rates : JumpChain.BoundedRates S)

/-- Killed embedded-chain powers converge under finite-set exhaustion. -/
theorem tendsto_kernelPow_killedP (m : ℕ) (x y : S) :
    Tendsto (fun U : Finset S ↦ kernelPow (rates.killedP (U : Set S)) m x y)
      atTop (𝓝 (kernelPow rates.p m x y)) := by
  classical
  induction m generalizing x y with
  | zero => simpa only [kernelPow] using (tendsto_const_nhds :
      Tendsto (fun _ : Finset S ↦ if x = y then (1 : ℝ) else 0) atTop
        (𝓝 (if x = y then 1 else 0)))
  | succ m ih =>
    change Tendsto (fun U : Finset S ↦ ∑' z, kernelPow (rates.killedP (U : Set S)) m x z *
      rates.killedP (U : Set S) z y) atTop
      (𝓝 (∑' z, kernelPow rates.p m x z * rates.p z y))
    apply tendsto_tsum_of_dominated_convergence
      (kernelPow_summable rates.p_nonneg rates.hasSum_p m x)
    · intro z
      have hp : Tendsto (fun U : Finset S ↦ rates.killedP (U : Set S) z y) atTop
          (𝓝 (rates.p z y)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ({y} : Finset S)] with U hU
        have hy : y ∈ U := hU (Finset.mem_singleton_self y)
        simp [JumpChain.BoundedRates.killedP, hy]
      exact (ih x z).mul hp
    · filter_upwards with U z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (kernelPow_nonneg (rates.killedP_nonneg (U : Set S)) m x z)
        (rates.killedP_nonneg (U : Set S) z y))]
      exact (mul_le_of_le_one_right
        (kernelPow_nonneg (rates.killedP_nonneg (U : Set S)) m x z)
        ((rates.killedP_le_p (U : Set S) z y).trans
          (kernel_entry_le_one rates.p_nonneg rates.hasSum_p z y))).trans
        (rates.kernelPow_killedP_le (U : Set S) m x z)

/-- Killed kernels converge to the full transition kernel along finite-set exhaustion. -/
theorem tendsto_killedKernel [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (t : ℝ≥0) (x y : S) :
    Tendsto (fun U : Finset S ↦ rates.killedKernel (U : Set S) t x y) atTop
      (𝓝 ((rates.transitionKernel t x).real {y})) := by
  classical
  rw [← rates.killedKernel_univ t x y]
  simp only [JumpChain.BoundedRates.killedKernel, rates.killedP_univ]
  have hR := rates.R_pos
  apply tendsto_tsum_of_dominated_convergence
    ((hasSum_one_poissonMeasure
      (⟨rates.R * t, mul_nonneg rates.R_pos.le t.coe_nonneg⟩ : ℝ≥0)).summable)
  · intro m
    exact tendsto_const_nhds.mul (tendsto_kernelPow_killedP rates m x y)
  · filter_upwards with U m
    rw [Real.norm_eq_abs, abs_of_nonneg (rates.killedKernel_term_nonneg (U : Set S) t x y m)]
    exact mul_le_of_le_one_right (by positivity)
      ((rates.kernelPow_killedP_le (U : Set S) m x y).trans
        (kernel_entry_le_one (kernelPow_nonneg rates.p_nonneg m)
          (kernelPow_hasSum rates.p_nonneg rates.hasSum_p m) x y))

end
end LatticeProb.Davies
