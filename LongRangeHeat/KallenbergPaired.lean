import LongRangeHeat.KallenbergOptional
import LongRangeHeat.KallenbergAveraging

/-!
# Paired stopping-time increments

Averaging forward increments controls the distance between two nearby bounded
stopping times.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory
open scoped Topology ENNReal

variable {E : Type} [MetricSpace E] [TopologicalSpace.SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]

omit [TopologicalSpace.SeparableSpace E] in
/-- A natural stopping time of a measurable process is measurable. -/
theorem naturalStopping.measurable {Ω : Type} [MeasurableSpace Ω] {Y : Ω → D E}
    (hY : Measurable Y) {H : ℝ} {τ : Ω → Time} (hτ : naturalStopping Y H τ) :
    Measurable τ := by
  apply measurable_of_Iic
  intro t
  exact naturalSigma_le Y (fun s => (measurable_eval s).comp hY) t _ (hτ.2 t)

/-- The bounded distance at two measurable random times is integrable. -/
theorem integrable_boundedDistance_stopped {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) {Y : Ω → D E} (hY : Measurable Y)
    {σ τ : Ω → Time} (hσ : Measurable σ) (hτ : Measurable τ) :
    Integrable (fun w => boundedDistance ((Y w).1 (σ w)) ((Y w).1 (τ w)))
      (P : Measure Ω) := by
  have hs : Measurable (fun w => (Y w).1 (σ w)) := measurable_eval_uncurry.comp (hσ.prodMk hY)
  have ht : Measurable (fun w => (Y w).1 (τ w)) := measurable_eval_uncurry.comp (hτ.prodMk hY)
  exact Integrable.of_bound (continuous_boundedDistance.measurable.comp (hs.prodMk ht)).aestronglyMeasurable
    1 (Filter.Eventually.of_forall fun w => norm_boundedDistance_le_one _ _)

variable {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]

/-- Sequential optional-increment convergence implies the paired stopping-time
expectation bound of Kallenberg, Lemma 16.12. -/
theorem exists_pos_eventually_uniform_paired_expectation
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E) (hY : ∀ n, Measurable (Y n))
    {H : ℝ} (hH : 0 < H)
    (h : ∀ η : ℝ, 0 < η → ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ σ τ : Ω n → Time, naturalStopping (Y n) H σ → naturalStopping (Y n) H τ →
      (∀ w, σ w ≤ τ w) → (∀ w, (τ w : ℝ) ≤ (σ w : ℝ) + δ) →
      (∫ w, boundedDistance ((Y n w).1 (σ w)) ((Y n w).1 (τ w))
        ∂(P n : Measure (Ω n))) < ε := by
  have hr : 0 < ε / 4 := by linarith
  obtain ⟨d, hd, N, hN⟩ := exists_pos_eventually_uniform_optional_expectation P Y hH h
    (ENNReal.ofReal_pos.mpr hr)
  refine ⟨d / 2, half_pos hd, N, ?_⟩
  intro n hn σ τ hσ hτ hστ hnear
  have hs := hσ.measurable (hY n)
  have ht := hτ.measurable (hY n)
  have hbound (v : Ω n → Time) (hv : naturalStopping (Y n) H v)
      (u : ℝ) (hu : 0 < u) (hud : u ≤ d) :
      ∫ w, boundedDistance ((Y n w).1 (v w)) ((Y n w).1 (v w + u.toNNReal))
        ∂(P n : Measure (Ω n)) ≤ ε / 4 := by
    have hm : Measurable (fun w => v w + u.toNNReal) := (hv.measurable (hY n)).add measurable_const
    have hi := integrable_boundedDistance_stopped (P n) (hY n) (hv.measurable (hY n)) hm
    have hb := hN n hn v hv u.toNNReal (by simpa only [Real.coe_toNNReal _ hu.le] using hud)
    have hconverted : ENNReal.ofReal (∫ w, boundedDistance ((Y n w).1 (v w))
        ((Y n w).1 (v w + u.toNNReal)) ∂(P n : Measure (Ω n))) < ENNReal.ofReal (ε / 4) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun w => boundedDistance_nonneg _ _)]
      simpa only [boundedDistance, dist_comm] using hb
    exact ((ENNReal.ofReal_lt_ofReal_iff hr).mp hconverted).le
  have hpaired := integral_boundedDistance_le_three_mul (P n : Measure (Ω n))
    (Y n) (hY n) σ τ hs ht (half_pos hd) hστ hnear
    (fun u hu hud => hbound σ hσ u hu (by linarith))
    (fun u hu hud => hbound τ hτ u hu (by linarith))
  linarith

end LatticeProb.Cadlag.HalfLine
