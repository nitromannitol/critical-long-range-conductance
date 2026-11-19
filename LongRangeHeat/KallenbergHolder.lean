import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# A finite Hölder bound

A common bound on finitely many nonnegative integrals bounds the integral of
their geometric mean.
-/

namespace LatticeProb.Cadlag.HalfLine

open MeasureTheory
open scoped ENNReal

/-- A finite geometric mean is bounded by a common bound on its factor integrals. -/
theorem lintegral_geometricMean_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 0 < n) (f : Fin n → Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) P) (hB : ∀ i, ∫⁻ w, f i w ∂P ≤ B) :
    ∫⁻ w, ∏ i : Fin n, f i w ^ ((n : ℝ)⁻¹) ∂P ≤ B := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  calc
    _ ≤ ∏ i : Fin n, (∫⁻ w, f i w ∂P) ^ ((n : ℝ)⁻¹) := by
      apply ENNReal.lintegral_prod_norm_pow_le Finset.univ
      · exact fun i _ => hf i
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_inv_cancel₀ hn'
      · exact fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)
    _ ≤ ∏ _i : Fin n, B ^ ((n : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      intro i _
      exact ENNReal.rpow_le_rpow (hB i) (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = B := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, inv_mul_cancel₀ hn', ENNReal.rpow_one]


/-- A nonnegative random variable has a bounded exponential moment in terms of
its lower-tail probability. -/
theorem lintegral_exp_neg_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Ω → ℝ) (hξ : Measurable ξ)
    (hξ0 : ∀ w, 0 ≤ ξ w) {a c : ℝ} (ha : 0 ≤ a) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (-a * ξ w)) ∂P ≤
      ENNReal.ofReal (Real.exp (-a * c)) + P {w | ξ w < c} := by
  let A := {w | ξ w < c}
  let b := ENNReal.ofReal (Real.exp (-a * c))
  have hA : MeasurableSet A := measurableSet_lt hξ measurable_const
  calc
    _ ≤ ∫⁻ w, b + A.indicator (fun _ => (1 : ℝ≥0∞)) w ∂P := by
      apply lintegral_mono
      intro w
      change ENNReal.ofReal (Real.exp (-a * ξ w)) ≤ b + A.indicator (fun _ => 1) w
      by_cases hw : w ∈ A
      · rw [Set.indicator_of_mem hw]
        refine le_trans ?_ (le_add_left le_rfl)
        exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by nlinarith [hξ0 w]))
      · rw [Set.indicator_of_notMem hw, add_zero]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hcw : c ≤ ξ w := le_of_not_gt hw
        nlinarith
    _ = b + P A := by
      rw [lintegral_add_right _ (measurable_const.indicator hA), lintegral_const,
        measure_univ, mul_one, lintegral_indicator_const hA, one_mul]


/-- Kallenberg's exponential bound for a sum of nonnegative random variables. -/
theorem lintegral_exp_neg_sum_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ i)) (hξ0 : ∀ i w, 0 ≤ ξ i w) (c : ℝ) (p : ℝ≥0∞)
    (hp : ∀ i, P {w | ξ i w < c} ≤ p) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (-(∑ i, ξ i w))) ∂P ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) + p := by
  let f : Fin n → Ω → ℝ≥0∞ := fun i w => ENNReal.ofReal (Real.exp (-(n : ℝ) * ξ i w))
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) + p
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hf (i : Fin n) : AEMeasurable (f i) P := by
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp ((hξ i).const_mul (-(n : ℝ))))).aemeasurable
  have hbound (i : Fin n) : ∫⁻ w, f i w ∂P ≤ B := by
    exact (lintegral_exp_neg_le P (ξ i) (hξ i) (hξ0 i)
      (a := (n : ℝ)) (c := c) (Nat.cast_nonneg n)).trans
      (add_le_add le_rfl (hp i))
  have heq (w : Ω) : ENNReal.ofReal (Real.exp (-(∑ i, ξ i w))) =
      ∏ i : Fin n, f i w ^ ((n : ℝ)⁻¹) := by
    have hi (i : Fin n) : f i w ^ ((n : ℝ)⁻¹) =
        ENNReal.ofReal (Real.exp (-(ξ i w))) := by
      dsimp [f]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      field_simp
    simp_rw [hi]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← Real.exp_sum, ← Finset.sum_neg_distrib]
  simpa only [heq] using lintegral_geometricMean_le P hn f B hf hbound


/-- The exponential sum bound controls the probability that the sum stays below
an arbitrary threshold. -/
theorem measure_sum_le_of_lower_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ i)) (hξ0 : ∀ i w, 0 ≤ ξ i w) (t c : ℝ) (p : ℝ≥0∞)
    (hp : ∀ i, P {w | ξ i w < c} ≤ p) :
    P {w | ∑ i, ξ i w ≤ t} ≤ ENNReal.ofReal (Real.exp t) *
      (ENNReal.ofReal (Real.exp (-(n : ℝ) * c)) + p) := by
  let A := {w | ∑ i, ξ i w ≤ t}
  let F : Ω → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (-(∑ i, ξ i w)))
  have hA : MeasurableSet A := measurableSet_le (Finset.measurable_sum _ fun i _ => hξ i)
    measurable_const
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun i _ => hξ i).neg)
  calc
    P A = ∫⁻ w, A.indicator (fun _ => (1 : ℝ≥0∞)) w ∂P := by
      rw [lintegral_indicator_const hA, one_mul]
    _ ≤ ∫⁻ w, ENNReal.ofReal (Real.exp t) * F w ∂P := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ A
      · rw [Set.indicator_of_mem hw]
        dsimp only [F]
        rw [← ENNReal.ofReal_mul (Real.exp_pos t).le, ← Real.exp_add]
        have hw' : ∑ i, ξ i w ≤ t := hw
        exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (by linarith))
      · rw [Set.indicator_of_notMem hw]
        exact zero_le
    _ = ENNReal.ofReal (Real.exp t) * ∫⁻ w, F w ∂P := lintegral_const_mul _ hF
    _ ≤ _ := by gcongr; exact lintegral_exp_neg_sum_le P hn ξ hξ hξ0 c p hp

end LatticeProb.Cadlag.HalfLine
