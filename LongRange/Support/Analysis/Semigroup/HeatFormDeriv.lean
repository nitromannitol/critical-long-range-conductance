import LongRange.Support.Analysis.Semigroup.HeatForm
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Right derivative of the semigroup quadratic form at zero

For symmetric bounded rates and square-summable `f`, the quadratic form
`a(t) = ∑ᵢ f i (P_t f)(i)` satisfies `|a(t) - ‖f‖² + t E(f)| ≤ K t²` with an explicit `K`.
Hence `a` has right derivative `-E(f)` at zero, and `t ↦ ‖P_t f‖² = a(2t)` has right
derivative `-2 E(f)` at zero.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory Asymptotics Filter Topology
open scoped NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Quadratic error in the first-order expansion of the semigroup quadratic form. -/
theorem abs_heatForm_sub_le (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) (h : ℝ≥0) :
    |rates.heatForm f h - (∑' i, f i ^ 2 - h * rates.energy f)| ≤
      (2 * rates.R ^ 2 * ∑' i, f i ^ 2 + rates.R * rates.energy f) * h ^ 2 := by
  have hl := rates.heatForm_lower hs hf h
  have hu := rates.heatForm_upper hs hf h
  have hE := rates.energy_nonneg f
  have hr : 0 ≤ ∑' i, f i ^ 2 := tsum_nonneg fun i ↦ sq_nonneg _
  have h1 : 0 ≤ 2 * rates.R ^ 2 * (∑' i, f i ^ 2) * (h : ℝ) ^ 2 := by positivity
  have h2 : 0 ≤ rates.R * (h : ℝ) ^ 2 * rates.energy f :=
    mul_nonneg (mul_nonneg rates.R_pos.le (sq_nonneg _)) hE
  rw [abs_le]
  constructor <;> nlinarith

/-- The semigroup quadratic form has right derivative `-E(f)` at zero. -/
theorem hasDerivWithinAt_heatForm (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) :
    HasDerivWithinAt (fun t : ℝ ↦ rates.heatForm f t.toNNReal) (-rates.energy f)
      (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_isLittleO]
  have hO : (fun t : ℝ ↦ rates.heatForm f t.toNNReal - rates.heatForm f (0 : ℝ).toNNReal -
      (t - 0) • (-rates.energy f)) =O[𝓝[Set.Ici 0] 0] fun t ↦ t ^ 2 := by
    refine IsBigO.of_bound (2 * rates.R ^ 2 * ∑' i, f i ^ 2 + rates.R * rates.energy f) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h := rates.abs_heatForm_sub_le hs hf t.toNNReal
    rw [Real.coe_toNNReal t ht] at h
    rw [Real.toNNReal_zero, rates.heatForm_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    convert h using 2
    ring
  refine hO.trans_isLittleO ?_
  simpa only [sub_zero] using (isLittleO_pow_id (𝕜 := ℝ) one_lt_two).mono nhdsWithin_le_nhds

/-- The squared norm of the evolved function has right derivative `-2 E(f)` at zero. -/
theorem hasDerivWithinAt_tsum_kernelApply_sq (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) {f : S → ℝ} (hf : Summable fun i ↦ f i ^ 2) :
    HasDerivWithinAt (fun t : ℝ ↦ ∑' i, kernelApply (rates.heatKernel t.toNNReal) f i ^ 2)
      (-2 * rates.energy f) (Set.Ici 0) 0 := by
  have hfun : (fun t : ℝ ↦ ∑' i, kernelApply (rates.heatKernel t.toNNReal) f i ^ 2) =
      (fun t : ℝ ↦ rates.heatForm f t.toNNReal) ∘ fun t ↦ 2 * t := by
    funext t
    rw [Function.comp_apply, ← rates.heatForm_add_self hs hf]
    congr 1
    rcases le_total 0 t with ht | ht
    · apply NNReal.eq
      simp only [NNReal.coe_add, Real.coe_toNNReal _ ht,
        Real.coe_toNNReal _ (mul_nonneg zero_le_two ht)]
      ring
    · rw [Real.toNNReal_of_nonpos ht, Real.toNNReal_of_nonpos (by linarith), add_zero]
  rw [hfun]
  have h := (rates.hasDerivWithinAt_heatForm hs hf).comp_of_eq 0
    ((hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).const_mul 2)
    (fun t (ht : t ∈ Set.Ici (0 : ℝ)) ↦ by
      simp only [id, Set.mem_Ici] at ht ⊢
      linarith) (by simp)
  rw [show -2 * rates.energy f = -rates.energy f * (2 * 1) by ring]
  exact h

end

end LatticeProb.JumpChain.BoundedRates
