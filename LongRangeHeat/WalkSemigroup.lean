import LongRangeHeat.Defs
import LongRange.Walk.Rates
import LongRange.Support.Prob.JumpChain.Operator
import LongRange.Support.Prob.JumpChain.OperatorExponential
import LongRange.Support.Prob.JumpChain.Duhamel
import LongRange.Support.Prob.JumpChain.Semigroup
import LongRange.Support.Analysis.KernelPowerBridge

/-!
# The transition kernel of the walk: symmetry and the Chapman–Kolmogorov identity

For symmetric jump rates, the transition probabilities of the uniformized walk are symmetric,
and the kernels at times `s` and `t` compose to the kernel at time `s + t`. In particular
`∑_y p_h(0, y)² = p_{2h}(0, 0)` for the singleton masses `p_h(x, y) = P_x[X_h = y]`.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
open scoped NNReal ENNReal

noncomputable section

section Contraction

variable {S : Type*}

/-- The square of a weighted average is at most the weighted average of the squares. -/
theorem sq_tsum_mul_le_tsum_mul_sq {w v : S → ℝ} (hw : ∀ y, 0 ≤ w y) (hw1 : HasSum w 1)
    {M : ℝ} (hv : ∀ y, |v y| ≤ M) :
    Summable (fun y => w y * v y ^ 2) ∧
      (∑' y, w y * v y) ^ 2 ≤ ∑' y, w y * v y ^ 2 := by
  have hvM : ∀ y, |v y| ≤ |M| := fun y => (hv y).trans (le_abs_self M)
  have h1 : Summable (fun y => w y * v y) := by
    refine Summable.of_norm_bounded (hw1.summable.mul_right |M|) fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw y)]
    exact mul_le_mul_of_nonneg_left (hvM y) (hw y)
  have h2 : Summable (fun y => w y * v y ^ 2) := by
    refine Summable.of_norm_bounded (hw1.summable.mul_right (|M| ^ 2)) fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw y), abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hvM y) 2) (hw y)
  refine ⟨h2, ?_⟩
  set s := ∑' y, w y * v y with hs
  have hsum := (h2.hasSum.sub (h1.hasSum.mul_left (2 * s))).add (hw1.mul_left (s ^ 2))
  have hnn := hsum.nonneg fun y => by
    have : w y * v y ^ 2 - 2 * s * (w y * v y) + s ^ 2 * w y = w y * (v y - s) ^ 2 := by ring
    show 0 ≤ w y * v y ^ 2 - 2 * s * (w y * v y) + s ^ 2 * w y
    rw [this]
    exact mul_nonneg (hw y) (sq_nonneg _)
  rw [← hs] at hnn
  nlinarith [hnn]

/-- A doubly stochastic matrix contracts `ℓ²`. -/
theorem tsum_sq_tsum_mul_le {m : S → S → ℝ} (hm0 : ∀ x y, 0 ≤ m x y)
    (hrow : ∀ x, HasSum (m x) 1) (hcol : ∀ y, HasSum (fun x => m x y) 1) {v : S → ℝ}
    (hv : Summable fun y => v y ^ 2) :
    Summable (fun x => (∑' y, m x y * v y) ^ 2) ∧
      ∑' x, (∑' y, m x y * v y) ^ 2 ≤ ∑' y, v y ^ 2 := by
  have hb : ∀ y, |v y| ≤ Real.sqrt (∑' y, v y ^ 2) := fun y =>
    Real.abs_le_sqrt (hv.le_tsum y (fun _ _ => sq_nonneg _))
  have hrowS := fun x => sq_tsum_mul_le_tsum_mul_sq (hm0 x) (hrow x) hb
  have hf : Summable (fun p : S × S => m p.2 p.1 * v p.1 ^ 2) := by
    have hnn : (0 : S × S → ℝ) ≤ fun p : S × S => m p.2 p.1 * v p.1 ^ 2 :=
      fun p => mul_nonneg (hm0 _ _) (sq_nonneg _)
    refine (summable_prod_of_nonneg hnn).mpr ⟨fun x => ?_, ?_⟩
    · show Summable fun y : S => m y x * v x ^ 2
      exact (hcol x).summable.mul_right _
    · show Summable fun x : S => ∑' y : S, m y x * v x ^ 2
      have : ∀ x : S, ∑' y : S, m y x * v x ^ 2 = v x ^ 2 := fun x => by
        rw [tsum_mul_right, (hcol x).tsum_eq, one_mul]
      simpa only [this] using hv
  have hg : Summable (fun p : S × S => m p.1 p.2 * v p.2 ^ 2) := hf.prod_symm
  have hB : Summable (fun x => ∑' y, m x y * v y ^ 2) := hg.prod
  have hsm : Summable (fun x => (∑' y, m x y * v y) ^ 2) :=
    hB.of_nonneg_of_le (fun x => sq_nonneg _) fun x => (hrowS x).2
  have hle : ∑' x, (∑' y, m x y * v y) ^ 2 ≤ ∑' x, ∑' y, m x y * v y ^ 2 :=
    hsm.tsum_le_tsum (fun x => (hrowS x).2) hB
  have hcomm : ∑' x, ∑' y, m x y * v y ^ 2 = ∑' y, ∑' x, m x y * v y ^ 2 :=
    (Summable.tsum_comm (f := fun x y => m x y * v y ^ 2) hg).symm
  have hcolS : ∑' y, ∑' x, m x y * v y ^ 2 = ∑' y, v y ^ 2 :=
    tsum_congr fun y => by rw [tsum_mul_right, (hcol y).tsum_eq, one_mul]
  exact ⟨hsm, hle.trans (hcomm.trans hcolS).le⟩

end Contraction

section Generic

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Symmetric jump rates give a symmetric transition probability at every time. -/
theorem transitionKernel_real_singleton_symm (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) (i j : S) :
    (rates.transitionKernel t i).real {j} = (rates.transitionKernel t j).real {i} := by
  rw [rates.transitionKernel_real_singleton, rates.transitionKernel_real_singleton]
  refine tsum_congr fun n => ?_
  have h (x y : S) : ((rates.kernel ^ n) x).real {y} = kernelPow rates.p n x y := by
    rw [measureReal_def, rates.kernel_pow_singleton, ENNReal.toReal_ofReal
      (kernelPow_nonneg rates.p_nonneg n x y)]
  rw [h, h, kernelPow_symm rates.p_nonneg rates.hasSum_p (rates.p_symm hs) n i j]

theorem poissonKernel_mul_add (κ : Kernel S S) [IsMarkovKernel κ] (r s t : ℝ≥0) :
    poissonKernel κ (r * (s + t)) = poissonKernel κ (r * t) ∘ₖ poissonKernel κ (r * s) := by
  rw [mul_add]
  exact poissonKernel_add κ _ _

/-- The transition kernels at times `s` and `t` compose to the kernel at time `s + t`. -/
theorem transitionKernel_add (rates : BoundedRates S) (s t : ℝ≥0) :
    rates.transitionKernel (s + t) = rates.transitionKernel t ∘ₖ rates.transitionKernel s := by
  unfold BoundedRates.transitionKernel
  exact poissonKernel_mul_add rates.kernel _ s t

/-- The Chapman–Kolmogorov identity for singleton masses. -/
theorem transitionKernel_real_singleton_add (rates : BoundedRates S) (s t : ℝ≥0) (x z : S) :
    (rates.transitionKernel (s + t) x).real {z} =
      ∑' y, (rates.transitionKernel s x).real {y} * (rates.transitionKernel t y).real {z} := by
  rw [transitionKernel_add, measureReal_def, Kernel.comp_apply' _ _ _ (measurableSet_singleton z),
    lintegral_countable']
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun y => ?_
    rw [ENNReal.toReal_mul, measureReal_def, measureReal_def, mul_comm]
  · intro y
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- The sum of the squared transition probabilities from `x` is the return probability at
twice the time. -/
theorem tsum_sq_transitionKernel_real_singleton (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (h : ℝ≥0) (x : S) :
    ∑' y, ((rates.transitionKernel h x).real {y}) ^ 2 =
      (rates.transitionKernel (h + h) x).real {x} := by
  rw [transitionKernel_real_singleton_add]
  refine tsum_congr fun y => ?_
  rw [sq, transitionKernel_real_singleton_symm rates hs h y x]

/-- The singleton masses of a probability measure on a countable space sum to one. -/
theorem hasSum_measureReal_singleton (μ : Measure S) [IsProbabilityMeasure μ] :
    HasSum (fun y => μ.real {y}) 1 := by
  have hs : Summable (fun y => μ.real {y}) := by
    refine summable_of_sum_le (c := 1) (fun y => measureReal_nonneg) fun u => ?_
    rw [sum_measureReal_singleton]
    exact measureReal_le_one
  have h := integral_countable (μ := μ) (integrable_const (1 : ℝ))
  have h1 : ∑' y, μ.real {y} = 1 := by
    simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h.symm
  exact hs.hasSum_iff.mpr h1

/-- The expectation under a transition row, as a series over sites, for bounded observables. -/
theorem integral_eq_tsum_real_singleton (μ : Measure S) [IsProbabilityMeasure μ] {v : S → ℝ}
    {M : ℝ} (hv : ∀ y, |v y| ≤ M) :
    ∫ y, v y ∂μ = ∑' y, μ.real {y} * v y := by
  rw [integral_countable (integrable_of_abs_le μ v hv)]
  simp only [smul_eq_mul]

end Generic

section Walk

variable {d : ℕ} {ε lam : ℝ} {a : LongRange.Edge d → ℝ}

/-- The rates of the walk are symmetric. -/
theorem walkRates_q_symm (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) :
    (LongRange.walkRates hd hε hlam a ha).q x y = (LongRange.walkRates hd hε hlam a ha).q y x :=
  LongRange.walkRate_symm ε a x y

/-- The bounded generator of the walk is the operator `L^ε` of (1.3). -/
theorem generatorOperator_walkRates_apply (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (w : BoundedObservable (Site d)) (x : Site d) :
    (LongRange.walkRates hd hε hlam a ha).generatorOperator w x = LongRange.generator ε a w x := by
  rw [BoundedRates.generatorOperator_apply, LongRange.generator_eq_walkRate_tsum]
  rfl

/-- The `n`-th power of the bounded generator acts as the `n`-th iterate of `L^ε`. -/
theorem generatorOperator_pow_apply (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (w : BoundedObservable (Site d)) (n : ℕ) :
    ⇑(((LongRange.walkRates hd hε hlam a ha).generatorOperator ^ n) w) =
      (LongRange.generator ε a)^[n] ⇑w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    have hmul : ((LongRange.walkRates hd hε hlam a ha).generatorOperator ^ (n + 1)) w =
        (LongRange.walkRates hd hε hlam a ha).generatorOperator
          (((LongRange.walkRates hd hε hlam a ha).generatorOperator ^ n) w) := by
      rw [pow_succ']
      rfl
    rw [hmul, Function.iterate_succ_apply', ← ih w]
    funext x
    exact generatorOperator_walkRates_apply hd hε hlam ha _ x

/-- The solution `e^{tL^ε} f` of (1.4) is the expectation of `f` at time `t` under the walk,
for every bounded restriction of `f` to `εℤ^d`. -/
theorem latticeHeat_eq_integral (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : (Fin d → ℝ) → ℝ} {M : ℝ}
    (hf : ∀ q : Site d, |restrict ε f q| ≤ M) (t : ℝ≥0) (q : Site d) :
    latticeHeat ε a f t q =
      ∫ y, restrict ε f y ∂((LongRange.walkRates hd hε hlam a ha).transitionKernel t q) := by
  set rates := LongRange.walkRates hd hε hlam a ha with hrates
  let v : BoundedObservable (Site d) :=
    ⟨restrict ε f, memℓp_infty ⟨M, by rintro _ ⟨k, rfl⟩; exact hf k⟩⟩
  have h1 := rates.exp_generatorOperator_apply t v q
  rw [NormedSpace.exp_eq_tsum ℝ] at h1
  have hsum := NormedSpace.expSeries_summable' (𝕂 := ℝ) ((t : ℝ) • rates.generatorOperator)
  have h2 := ContinuousLinearMap.map_tsum
    ((lp.evalCLM ℝ (fun _ : Site d => ℝ) ∞ q).comp (ContinuousLinearMap.apply ℝ _ v)) hsum
  beta_reduce at h1
  have h3 : ∀ n : ℕ,
      ((lp.evalCLM ℝ (fun _ : Site d => ℝ) ∞ q).comp (ContinuousLinearMap.apply ℝ _ v))
        ((n.factorial : ℝ)⁻¹ • ((t : ℝ) • rates.generatorOperator) ^ n) =
      (t : ℝ) ^ n / n.factorial * (LongRange.generator ε a)^[n] (restrict ε f) q := by
    intro n
    have hp := congrFun (generatorOperator_pow_apply hd hε hlam ha v n) q
    have e : ((n.factorial : ℝ)⁻¹ • ((t : ℝ) • rates.generatorOperator) ^ n) v =
        ((n.factorial : ℝ)⁻¹ * (t : ℝ) ^ n) • ((rates.generatorOperator ^ n) v) := by
      change (n.factorial : ℝ)⁻¹ • ((((t : ℝ) • rates.generatorOperator) ^ n) v) = _
      rw [operator_smul_pow_apply, smul_smul]
    change (((n.factorial : ℝ)⁻¹ • ((t : ℝ) • rates.generatorOperator) ^ n) v) q = _
    rw [e, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hp]
    have hv : ⇑v = restrict ε f := rfl
    rw [hv]
    ring
  unfold latticeHeat
  calc ∑' n : ℕ, (t : ℝ) ^ n / n.factorial * (LongRange.generator ε a)^[n] (restrict ε f) q
      = ∑' n : ℕ, ((lp.evalCLM ℝ (fun _ : Site d => ℝ) ∞ q).comp
          (ContinuousLinearMap.apply ℝ _ v))
          ((n.factorial : ℝ)⁻¹ • ((t : ℝ) • rates.generatorOperator) ^ n) :=
        tsum_congr fun n => (h3 n).symm
    _ = _ := h2.symm
    _ = _ := h1

end Walk

section Operator

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The semigroup `e^{tL^ε}` as an operator on functions on the sites: the expectation of the
observable at time `t` under the walk. -/
def walkOp (rates : BoundedRates S) (t : ℝ≥0) (v : S → ℝ) (x : S) : ℝ :=
  ∫ y, v y ∂rates.transitionKernel t x

/-- The semigroup contracts `ℓ²` when the jump rates are symmetric. -/
theorem summable_sq_walkOp_and_tsum_sq_walkOp_le (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) {v : S → ℝ}
    (hv : Summable fun y => v y ^ 2) :
    Summable (fun x => (walkOp rates t v x) ^ 2) ∧
      ∑' x, (walkOp rates t v x) ^ 2 ≤ ∑' y, v y ^ 2 := by
  have hb : ∀ y, |v y| ≤ Real.sqrt (∑' y, v y ^ 2) := fun y =>
    Real.abs_le_sqrt (hv.le_tsum y (fun _ _ => sq_nonneg _))
  have hop : ∀ x, walkOp rates t v x = ∑' y, (rates.transitionKernel t x).real {y} * v y :=
    fun x => integral_eq_tsum_real_singleton _ hb
  simp only [hop]
  refine tsum_sq_tsum_mul_le (fun x y => measureReal_nonneg)
    (fun x => hasSum_measureReal_singleton _) (fun y => ?_) hv
  convert hasSum_measureReal_singleton (rates.transitionKernel t y) using 2 with x
  exact transitionKernel_real_singleton_symm rates hs t x y

end Operator

end

end LongRangeHeat
