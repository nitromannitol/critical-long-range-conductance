import LongRange.Support.Analysis.Semigroup.HeatForm
import LongRange.Support.Analysis.Semigroup.LogConvex

/-!
# Exponential lower bound for the semigroup quadratic form

For symmetric bounded rates and a nonzero square-summable `f`, the quadratic form
`a(t) = ∑ᵢ f i (P_t f)(i)` is nonnegative, midpoint log-convex and equal to
`‖f‖² - t E(f) + O(t²)` near zero. Hence `a(t) ≥ ‖f‖² exp(-t E(f) / ‖f‖²)` for every `t ≥ 0`;
at time `2t` this reads `‖P_t f‖² ≥ ‖f‖² exp(-2 t E(f) / ‖f‖²)`.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory
open scoped NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The semigroup quadratic form decays at most exponentially, at rate given by the energy. -/
theorem mul_exp_le_heatForm (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (hr : 0 < ∑' i, f i ^ 2) (t : ℝ≥0) :
    (∑' i, f i ^ 2) * Real.exp (-(t * rates.energy f / ∑' i, f i ^ 2)) ≤
      rates.heatForm f t :=
  mul_exp_le_of_midpoint_sq_le hr (rates.heatForm_zero f) (rates.heatForm_nonneg hs hf)
    (rates.heatForm_midpoint_sq_le hs hf) (rates.heatForm_lower hs hf) t

/-- The squared norm of the evolved function decays at most exponentially. -/
theorem mul_exp_le_tsum_kernelApply_sq (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2)
    (hr : 0 < ∑' i, f i ^ 2) (t : ℝ≥0) :
    (∑' i, f i ^ 2) * Real.exp (-(2 * t * rates.energy f / ∑' i, f i ^ 2)) ≤
      ∑' i, kernelApply (rates.heatKernel t) f i ^ 2 := by
  have h := rates.mul_exp_le_heatForm hs hf hr (t + t)
  rw [rates.heatForm_add_self hs hf] at h
  convert h using 4
  push_cast
  ring

end

end LatticeProb.JumpChain.BoundedRates
