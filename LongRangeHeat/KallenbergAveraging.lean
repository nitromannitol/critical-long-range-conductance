import LongRange.Support.Prob.Cadlag.HalfLine.TerminalJump
import LongRange.Support.Prob.Cadlag.HalfLine.RestrictionTight

/-!
# Averaging bounded path increments

An increment between two nearby times is controlled by averaged forward increments.
-/

namespace LatticeProb.Cadlag.HalfLine

open MeasureTheory Set
open scoped ENNReal

variable {E : Type} [MetricSpace E]

/-- The bounded distance satisfies the triangle inequality. -/
theorem boundedDistance_triangle (a b c : E) :
    boundedDistance a c ≤ boundedDistance a b + boundedDistance b c := by
  have hq (x y : E) : q x y ≠ ∞ :=
    ne_of_lt ((min_le_right (edist x y) (1 : ℝ≥0∞)).trans_lt ENNReal.one_lt_top)
  simp only [boundedDistance_eq_toReal_q, ← ENNReal.toReal_add (hq a b) (hq b c)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hq a b, hq b c⟩) (q_triangle a b c)

variable [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]

/-- Averaging the triangle inequality gives the pathwise bound in Lemma 16.12. -/
theorem averaged_boundedDistance_le (x : D E) (σ τ : Time) {δ : ℝ} (hδ : 0 ≤ δ)
    (hστ : σ ≤ τ) (hnear : (τ : ℝ) ≤ (σ : ℝ) + δ) :
    δ * boundedDistance (x.1 σ) (x.1 τ) ≤
      (∫ h in (0 : ℝ)..2 * δ,
        boundedDistance (x.1 σ) (x.1 ((σ : ℝ) + h).toNNReal)) +
      ∫ h in (0 : ℝ)..δ,
        boundedDistance (x.1 τ) (x.1 ((τ : ℝ) + h).toNNReal) := by
  let f : ℝ → ℝ := fun t => boundedDistance (x.1 σ) (x.1 t.toNNReal)
  let g : ℝ → ℝ := fun t => boundedDistance (x.1 τ) (x.1 t.toNNReal)
  have hfi (a b : ℝ) : IntervalIntegrable f volume a b := by
    simpa only [f, Real.toNNReal_coe] using
      intervalIntegrable_boundedDistance x (σ : ℝ) a b
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b := by
    simpa only [g, Real.toNNReal_coe] using
      intervalIntegrable_boundedDistance x (τ : ℝ) a b
  have hshiftf : IntervalIntegrable (fun h => f ((τ : ℝ) + h)) volume 0 δ := by
    simpa only [add_zero, add_sub_cancel_left, sub_self] using
      (hfi ((τ : ℝ) + 0) ((τ : ℝ) + δ)).comp_add_left (τ : ℝ)
  have hshiftg : IntervalIntegrable (fun h => g ((τ : ℝ) + h)) volume 0 δ := by
    simpa only [add_zero, add_sub_cancel_left, sub_self] using
      (hgi ((τ : ℝ) + 0) ((τ : ℝ) + δ)).comp_add_left (τ : ℝ)
  have htri : δ * boundedDistance (x.1 σ) (x.1 τ) ≤
      ∫ h in (0 : ℝ)..δ, f ((τ : ℝ) + h) + g ((τ : ℝ) + h) := by
    have h := intervalIntegral.integral_mono_on hδ intervalIntegrable_const
      (hshiftf.add hshiftg) (fun h _ => by
        have hh := boundedDistance_triangle (x.1 σ) (x.1 ((τ : ℝ) + h).toNNReal) (x.1 τ)
        simpa only [f, g, boundedDistance, dist_comm] using hh)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      f, g, boundedDistance, dist_comm] using h
  have hcompare : (∫ h in (0 : ℝ)..δ, f ((τ : ℝ) + h)) ≤
      ∫ h in (0 : ℝ)..2 * δ, f ((σ : ℝ) + h) := by
    rw [intervalIntegral.integral_comp_add_left, intervalIntegral.integral_comp_add_left]
    apply intervalIntegral.integral_mono_interval _ (by linarith) _
      (Filter.Eventually.of_forall fun t => boundedDistance_nonneg _ _) (hfi _ _)
    · simpa only [add_zero] using (show (σ : ℝ) ≤ (τ : ℝ) by exact_mod_cast hστ)
    · linarith
  calc
    _ ≤ (∫ h in (0 : ℝ)..δ, f ((τ : ℝ) + h)) +
        ∫ h in (0 : ℝ)..δ, g ((τ : ℝ) + h) := by
      simpa only [intervalIntegral.integral_add hshiftf hshiftg] using htri
    _ ≤ _ := add_le_add hcompare le_rfl


/-- Integrating a uniform forward-increment bound over the time window. -/
theorem integral_averaged_stopped_increment_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → D E) (hY : Measurable Y) (τ : Ω → Time) (hτ : Measurable τ)
    {δ c : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ h : ℝ, 0 < h → h ≤ δ →
      ∫ w, boundedDistance ((Y w).1 (τ w)) ((Y w).1 (τ w + h.toNNReal)) ∂P ≤ c) :
    Integrable (fun w => ∫ h in (0 : ℝ)..δ,
      boundedDistance ((Y w).1 (τ w)) ((Y w).1 (τ w + h.toNNReal))) P ∧
    (∫ w, (∫ h in (0 : ℝ)..δ,
      boundedDistance ((Y w).1 (τ w)) ((Y w).1 (τ w + h.toNNReal))) ∂P) ≤ δ * c := by
  let ρ : Measure ℝ := volume.restrict (Ioc 0 δ)
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let F : Ω × ℝ → ℝ := fun z =>
    boundedDistance ((Y z.1).1 (τ z.1)) ((Y z.1).1 (τ z.1 + z.2.toNNReal))
  have hfirst : Measurable (fun z : Ω × ℝ => (Y z.1).1 (τ z.1)) := by
    exact measurable_eval_uncurry.comp
      ((hτ.comp measurable_fst).prodMk (hY.comp measurable_fst))
  have hsecond : Measurable (fun z : Ω × ℝ =>
      (Y z.1).1 (τ z.1 + z.2.toNNReal)) := by
    exact measurable_eval_uncurry.comp
      (((hτ.comp measurable_fst).add
        (continuous_real_toNNReal.measurable.comp measurable_snd)).prodMk (hY.comp measurable_fst))
  have hF : Measurable F := continuous_boundedDistance.measurable.comp (hfirst.prodMk hsecond)
  have hFi : Integrable F (P.prod ρ) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ fun z => norm_boundedDistance_le_one _ _)
  have hmass : ρ.real univ = δ := by
    simp only [ρ, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hδ]
  have hmem : ∀ᵐ t ∂ρ, t ∈ Ioc 0 δ := ae_restrict_mem measurableSet_Ioc
  constructor
  · simpa only [intervalIntegral.integral_of_le hδ] using hFi.integral_prod_left
  · calc
      _ = ∫ w, ∫ h, F (w, h) ∂ρ ∂P := by
        simp only [intervalIntegral.integral_of_le hδ, F, ρ]
      _ = ∫ h, ∫ w, F (w, h) ∂P ∂ρ := integral_integral_swap hFi
      _ ≤ ∫ _h, c ∂ρ := by
        apply integral_mono_ae hFi.integral_prod_right (integrable_const c)
        filter_upwards [hmem] with t ht
        exact hb t ht.1 ht.2
      _ = δ * c := by rw [integral_const, smul_eq_mul, hmass]


/-- Two nearby random times are controlled by forward increments at each time. -/
theorem integral_boundedDistance_le_three_mul
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → D E) (hY : Measurable Y) (σ τ : Ω → Time)
    (hσ : Measurable σ) (hτ : Measurable τ) {δ c : ℝ} (hδ : 0 < δ)
    (hστ : ∀ w, σ w ≤ τ w) (hnear : ∀ w, (τ w : ℝ) ≤ (σ w : ℝ) + δ)
    (hσbound : ∀ h : ℝ, 0 < h → h ≤ 2 * δ →
      ∫ w, boundedDistance ((Y w).1 (σ w)) ((Y w).1 (σ w + h.toNNReal)) ∂P ≤ c)
    (hτbound : ∀ h : ℝ, 0 < h → h ≤ δ →
      ∫ w, boundedDistance ((Y w).1 (τ w)) ((Y w).1 (τ w + h.toNNReal)) ∂P ≤ c) :
    ∫ w, boundedDistance ((Y w).1 (σ w)) ((Y w).1 (τ w)) ∂P ≤ 3 * c := by
  have hA := integral_averaged_stopped_increment_le P Y hY σ hσ (by linarith) hσbound
  have hB := integral_averaged_stopped_increment_le P Y hY τ hτ hδ.le hτbound
  have hxs : Measurable (fun w => (Y w).1 (σ w)) :=
    measurable_eval_uncurry.comp (hσ.prodMk hY)
  have hxt : Measurable (fun w => (Y w).1 (τ w)) :=
    measurable_eval_uncurry.comp (hτ.prodMk hY)
  have hC : Integrable (fun w => boundedDistance ((Y w).1 (σ w)) ((Y w).1 (τ w))) P :=
    Integrable.of_bound (continuous_boundedDistance.measurable.comp (hxs.prodMk hxt)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun w => norm_boundedDistance_le_one _ _)
  have hconv (v : Ω → Time) (w : Ω) {b : ℝ} (hb : 0 ≤ b) :
      (∫ h in (0 : ℝ)..b, boundedDistance ((Y w).1 (v w))
        ((Y w).1 ((v w : ℝ) + h).toNNReal)) =
      ∫ h in (0 : ℝ)..b, boundedDistance ((Y w).1 (v w))
        ((Y w).1 (v w + h.toNNReal)) := by
    apply intervalIntegral.integral_congr
    intro h hh
    have hh0 : 0 ≤ h := (show h ∈ Icc (0 : ℝ) b by simpa only [uIcc_of_le hb] using hh).1
    have heq0 : ((v w : ℝ)).toNNReal = v w := Real.toNNReal_coe
    have heq : ((v w : ℝ) + h).toNNReal = v w + h.toNNReal :=
      (Real.toNNReal_add (v w).2 hh0).trans (congrArg (fun t : Time => t + h.toNNReal) heq0)
    simp only [heq]
  have hpoint (w : Ω) :
      δ * boundedDistance ((Y w).1 (σ w)) ((Y w).1 (τ w)) ≤
        (∫ h in (0 : ℝ)..2 * δ, boundedDistance ((Y w).1 (σ w))
          ((Y w).1 (σ w + h.toNNReal))) +
        ∫ h in (0 : ℝ)..δ, boundedDistance ((Y w).1 (τ w))
          ((Y w).1 (τ w + h.toNNReal)) := by
    have hh := averaged_boundedDistance_le (Y w) (σ w) (τ w) hδ.le (hστ w) (hnear w)
    rw [hconv σ w (by linarith), hconv τ w hδ.le] at hh
    exact hh
  have hint := integral_mono (hC.const_mul δ) (hA.1.add hB.1) hpoint
  have hint' : δ * (∫ w, boundedDistance ((Y w).1 (σ w)) ((Y w).1 (τ w)) ∂P) ≤
      (∫ w, (∫ h in (0 : ℝ)..2 * δ, boundedDistance ((Y w).1 (σ w))
        ((Y w).1 (σ w + h.toNNReal))) ∂P) +
      (∫ w, (∫ h in (0 : ℝ)..δ, boundedDistance ((Y w).1 (τ w))
        ((Y w).1 (τ w + h.toNNReal))) ∂P) := by
    simpa only [Pi.add_apply, integral_const_mul, integral_add hA.1 hB.1] using hint
  nlinarith [hA.2, hB.2]

end LatticeProb.Cadlag.HalfLine
