import LongRangeHeat.KallenbergHitting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Probability bounds for oscillation times

The paired stopping-time estimate controls the probability of a short interval
between successive oscillation times.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal

variable {E : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
  {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]

/-- A uniform paired-time expectation bound controls short gaps between
successive oscillation times before the cap. -/
theorem exists_pos_eventually_oscillation_gap_le
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (hY : ∀ n, Measurable (Y n)) {T : Time} {ζ : ℝ} (hζ : 0 < ζ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ σ τ : Ω n → Time,
        weakNaturalStopping (Y n) (T : ℝ) σ → weakNaturalStopping (Y n) (T : ℝ) τ →
        (∀ w, σ w ≤ τ w) → (∀ w, (τ w : ℝ) ≤ (σ w : ℝ) + δ) →
        (∫ w, boundedDistance ((Y n w).1 (σ w)) ((Y n w).1 (τ w))
          ∂(P n : Measure (Ω n))) < ε)
    {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℕ,
      (P n : Measure (Ω n)) {w | oscillationTime (Y n) T ζ (k + 1) w < T ∧
        (oscillationTime (Y n) T ζ (k + 1) w : ℝ) ≤
          (oscillationTime (Y n) T ζ k w : ℝ) + δ} < p := by
  obtain ⟨r, _, hr', hrp⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr'
  let a := min ζ 1
  have ha : 0 < a := lt_min hζ zero_lt_one
  have hsmall : 0 < a * r / 2 := by positivity
  obtain ⟨δ, hδ, N, hN⟩ := hbound (a * r / 2) hsmall
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn k
  let σ := oscillationTime (Y n) T ζ k
  let τ := oscillationTime (Y n) T ζ (k + 1)
  let u : Time := δ.toNNReal
  let ρ : Ω n → Time := fun w => min (τ w) (σ w + u)
  have hσ : weakNaturalStopping (Y n) (T : ℝ) σ := weakNaturalStopping_oscillationTime _ _ _ _
  have hτ : weakNaturalStopping (Y n) (T : ℝ) τ := weakNaturalStopping_oscillationTime _ _ _ _
  have hρ : weakNaturalStopping (Y n) (T : ℝ) ρ := hτ.min_left (hσ.add_const u)
  have hστ (w : Ω n) : σ w ≤ τ w := oscillationTime_le_succ _ _ _ _ _
  have hσρ (w : Ω n) : σ w ≤ ρ w := le_min (hστ w) (le_add_of_nonneg_right zero_le)
  have hρnear (w : Ω n) : (ρ w : ℝ) ≤ (σ w : ℝ) + δ := by
    have hh := NNReal.coe_le_coe.mpr (min_le_right (τ w) (σ w + u))
    simpa only [NNReal.coe_add, u, Real.coe_toNNReal _ hδ.le] using hh
  have hexp := hN n hn σ ρ hσ hρ hσρ hρnear
  have hi := integrable_boundedDistance_stopped (P n) (hY n)
    (hσ.measurable (hY n)) (hρ.measurable (hY n))
  let F : Ω n → ℝ≥0∞ := fun w => ENNReal.ofReal
    (boundedDistance ((Y n w).1 (σ w)) ((Y n w).1 (ρ w)))
  have hF : AEMeasurable F (P n : Measure (Ω n)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have hFbound : (∫⁻ w, F w ∂(P n : Measure (Ω n))) ≤ ENNReal.ofReal (a * r / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun w => boundedDistance_nonneg _ _)]
    exact ENNReal.ofReal_le_ofReal hexp.le
  have hsubset : {w | τ w < T ∧ (τ w : ℝ) ≤ (σ w : ℝ) + δ} ⊆
      {w | ENNReal.ofReal a ≤ F w} := by
    intro w hw
    have hτle : τ w ≤ σ w + u := by
      apply NNReal.coe_le_coe.mp
      simpa only [NNReal.coe_add, u, Real.coe_toNNReal _ hδ.le] using hw.2
    have hρeq : ρ w = τ w := min_eq_left hτle
    have hdist := le_dist_oscillationTime_succ (Y n) T ζ k w hw.1
    change ENNReal.ofReal a ≤ ENNReal.ofReal
      (boundedDistance ((Y n w).1 (σ w)) ((Y n w).1 (ρ w)))
    apply ENNReal.ofReal_le_ofReal
    rw [hρeq]
    exact le_min ((min_le_left ζ 1).trans hdist) (min_le_right ζ 1)
  calc
    _ ≤ (P n : Measure (Ω n)) {w | ENNReal.ofReal a ≤ F w} := measure_mono hsubset
    _ ≤ (∫⁻ w, F w ∂(P n : Measure (Ω n))) / ENNReal.ofReal a :=
      meas_ge_le_lintegral_div hF (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (a * r / 2) / ENNReal.ofReal a := ENNReal.div_le_div_right hFbound _
    _ = ENNReal.ofReal (r / 2) := by
      rw [← ENNReal.ofReal_div_of_pos ha]
      congr 1
      field_simp
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)
    _ < p := hrp

end LatticeProb.Cadlag.HalfLine
