import LongRangeHeat.WalkSemigroup

/-!
# Pointwise bounds for the walk semigroup in terms of the `ℓ²` norm

For a bounded-rate walk with symmetric jump rates, the value `(e^{tL} V)(x)` of the semigroup is
controlled by the `ℓ²` norm of `V`, with the constant `√ P_x[X_{2h} = x]` for every `h ≤ t`. This
is the Markov property at time `h` followed by the Cauchy–Schwarz inequality, using that the
sum of the squared transition probabilities is the return probability at the doubled time.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
open scoped NNReal ENNReal

noncomputable section

section Series

variable {S : Type*}

/-- The Cauchy–Schwarz inequality for series: both the product series and its absolute value
are controlled by the `ℓ²` norms. -/
theorem summable_mul_and_abs_tsum_mul_le {w v : S → ℝ} (hw : Summable fun y => w y ^ 2)
    (hv : Summable fun y => v y ^ 2) :
    Summable (fun y => w y * v y) ∧
      |∑' y, w y * v y| ≤ Real.sqrt (∑' y, w y ^ 2) * Real.sqrt (∑' y, v y ^ 2) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hw' : Summable fun y => |w y| ^ (2 : ℝ) := by
    simpa only [Real.rpow_two, sq_abs] using hw
  have hv' : Summable fun y => |v y| ^ (2 : ℝ) := by
    simpa only [Real.rpow_two, sq_abs] using hv
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hp
    (fun y => abs_nonneg _) (fun y => abs_nonneg _) hw' hv'
  have hs' : Summable fun y => w y * v y :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs, abs_mul] using hs)
  refine ⟨hs', ?_⟩
  calc |∑' y, w y * v y| = ‖∑' y, w y * v y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' y, ‖w y * v y‖ := norm_tsum_le_tsum_norm hs'.norm
    _ = ∑' y, |w y| * |v y| := by simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ _ := by
      refine hle.trans (le_of_eq ?_)
      simp only [Real.rpow_two, sq_abs, one_div, Real.sqrt_eq_rpow, Real.rpow_two]

end Series

section Semigroup

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The semigroup does not increase the supremum norm. -/
theorem abs_walkOp_le (rates : BoundedRates S) (t : ℝ≥0) {v : S → ℝ} {M : ℝ}
    (hv : ∀ y, |v y| ≤ M) (x : S) : |walkOp rates t v x| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := rates.transitionKernel t x) (f := v) (C := M)
    (Filter.Eventually.of_forall hv)
  simpa [walkOp] using h

/-- The semigroup property of `walkOp` for bounded observables. -/
theorem walkOp_add (rates : BoundedRates S) (s t : ℝ≥0) {v : S → ℝ} {M : ℝ}
    (hv : ∀ y, |v y| ≤ M) (x : S) :
    walkOp rates (s + t) v x = walkOp rates s (walkOp rates t v) x := by
  unfold walkOp
  rw [transitionKernel_add, Kernel.integral_comp]
  exact integrable_of_abs_le _ v hv

/-- The semigroup at time `0` is the identity. -/
theorem walkOp_zero (rates : BoundedRates S) (v : S → ℝ) (x : S) : walkOp rates 0 v x = v x := by
  unfold walkOp
  rw [BoundedRates.transitionKernel_zero, Kernel.id_apply, integral_dirac]

/-- The squared transition probabilities from a site are summable. -/
theorem summable_sq_transitionKernel_real_singleton (rates : BoundedRates S) (t : ℝ≥0) (x : S) :
    Summable fun y => ((rates.transitionKernel t x).real {y}) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun y => sq_nonneg _) (fun y => ?_)
    (hasSum_measureReal_singleton (rates.transitionKernel t x)).summable
  have h0 : 0 ≤ (rates.transitionKernel t x).real {y} := measureReal_nonneg
  have h1 : (rates.transitionKernel t x).real {y} ≤ 1 := measureReal_le_one
  nlinarith

/-- The value at `x` of the semigroup applied to `V ∈ ℓ²`, at time `h`: the Markov property at
time `h` and the Cauchy–Schwarz inequality, with `∑_y P_x[X_h = y]² = P_x[X_{2h} = x]`. -/
theorem abs_walkOp_le_sqrt (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    (h : ℝ≥0) {V : S → ℝ} (hV : Summable fun y => V y ^ 2) (x : S) :
    |walkOp rates h V x| ≤
      Real.sqrt ((rates.transitionKernel (h + h) x).real {x}) * Real.sqrt (∑' y, V y ^ 2) := by
  have hb : ∀ y, |V y| ≤ Real.sqrt (∑' y, V y ^ 2) := fun y =>
    Real.abs_le_sqrt (hV.le_tsum y (fun _ _ => sq_nonneg _))
  have hop : walkOp rates h V x = ∑' y, (rates.transitionKernel h x).real {y} * V y :=
    integral_eq_tsum_real_singleton _ hb
  rw [hop, ← tsum_sq_transitionKernel_real_singleton rates hs h x]
  exact (summable_mul_and_abs_tsum_mul_le (summable_sq_transitionKernel_real_singleton rates h x)
    hV).2

/-- For `V ∈ ℓ²` and every time `t ≥ h`, the value at `x` of `e^{tL} V` is bounded by the `ℓ²`
norm of `V` times `√ P_x[X_{2h} = x]`. -/
theorem abs_walkOp_le_sqrt_of_le (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    {h t : ℝ≥0} (hht : h ≤ t) {V : S → ℝ} (hV : Summable fun y => V y ^ 2) (x : S) :
    |walkOp rates t V x| ≤
      Real.sqrt ((rates.transitionKernel (h + h) x).real {x}) * Real.sqrt (∑' y, V y ^ 2) := by
  have hb : ∀ y, |V y| ≤ Real.sqrt (∑' y, V y ^ 2) := fun y =>
    Real.abs_le_sqrt (hV.le_tsum y (fun _ _ => sq_nonneg _))
  obtain ⟨hW, hWle⟩ := summable_sq_walkOp_and_tsum_sq_walkOp_le rates hs (t - h) hV
  have ht : t = h + (t - h) := by rw [add_tsub_cancel_of_le hht]
  rw [ht, walkOp_add rates h (t - h) hb x]
  refine (abs_walkOp_le_sqrt rates hs h hW x).trans ?_
  gcongr

end Semigroup

end

end LongRangeHeat
