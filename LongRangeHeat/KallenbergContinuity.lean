import LongRangeHeat.KallenbergIdentification
import LongRange.Support.Prob.Cadlag.HalfLine.RestrictionTight
import LongRange.Support.Prob.Cadlag.HalfLine.TerminalJump
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Continuity times of càdlàg laws

Joint measurability of left samples allows the pathwise countability of jumps
to be integrated over a path law.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

noncomputable section

variable {E : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]

private def leftSample (n : ℕ) (t : ℝ) : Time := (t - 1 / (n + 1 : ℝ)).toNNReal

private theorem tendsto_leftSample (t : ℝ) :
    Tendsto (fun n => leftSample n t) atTop (𝓝 t.toNNReal) := by
  have h : Tendsto (fun n : ℕ => t - 1 / (n + 1 : ℝ)) atTop (𝓝 t) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => t - 1 / (n + 1 : ℝ)) atTop (𝓝 (t - 0)))
  simpa only [leftSample, sub_zero] using tendsto_real_toNNReal (f := atTop) (m := fun n : ℕ =>
    t - 1 / (n + 1 : ℝ)) h

private theorem tendsto_leftSample_left {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => leftSample n t) atTop (𝓝[<] t.toNNReal) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_leftSample t, ?_⟩
  have hsmall := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds ht)
  filter_upwards [hsmall] with n hn
  have hpos : 0 < (1 / (n + 1 : ℝ)) := by positivity
  change (t - 1 / (n + 1 : ℝ)).toNNReal < t.toNNReal
  apply (Real.toNNReal_lt_iff_lt_coe (by linarith : 0 ≤ t - 1 / (n + 1 : ℝ))).mpr
  rw [Real.coe_toNNReal t ht.le]
  linarith

omit [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuousAt_iff_leftSample (x : D E) {t : ℝ} (ht : 0 < t) :
    ContinuousAt x.1 t.toNNReal ↔
      Tendsto (fun n => x.1 (leftSample n t)) atTop (𝓝 (x.1 t.toNNReal)) := by
  constructor
  · intro hx
    exact hx.tendsto.comp (tendsto_leftSample t)
  · intro hx
    obtain ⟨l, hl⟩ := x.2.2 t.toNNReal (Real.toNNReal_pos.mpr ht)
    have hl' := hl.comp (tendsto_leftSample_left ht)
    have heq : l = x.1 t.toNNReal := tendsto_nhds_unique hl' hx
    apply continuousAt_iff_continuous_left_right.mpr
    constructor
    · apply continuousWithinAt_Iio_iff_Iic.mp
      simpa only [ContinuousWithinAt, heq] using hl
    · exact x.2.1 t.toNNReal


private theorem measurable_positive_continuity :
    MeasurableSet {p : D E × ℝ | 0 < p.2 → ContinuousAt p.1.1 p.2.toNNReal} := by
  have hs (n : ℕ) : Measurable (fun p : D E × ℝ => p.1.1 (leftSample n p.2)) := by
    have hm : Measurable (fun p : D E × ℝ => (leftSample n p.2, p.1)) :=
      ((continuous_real_toNNReal.comp (continuous_snd.sub continuous_const)).measurable.prodMk
        measurable_fst)
    exact (measurable_eval_uncurry (E := E)).comp hm
  have ht : Measurable (fun p : D E × ℝ => p.1.1 p.2.toNNReal) := by
    have hm : Measurable (fun p : D E × ℝ => (p.2.toNNReal, p.1)) :=
      (continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst
    exact (measurable_eval_uncurry (E := E)).comp hm
  have hm := measurableSet_tendsto_fun (l := atTop) hs ht
  have hm' : MeasurableSet {p : D E × ℝ | p.2 ≤ 0 ∨
      Tendsto (fun n => p.1.1 (leftSample n p.2)) atTop (𝓝 (p.1.1 p.2.toNNReal))} :=
    (measurableSet_le measurable_snd measurable_const).union hm
  convert hm' using 1
  ext p
  simp only [mem_ofPred_eq]
  by_cases hp : 0 < p.2
  · simp only [hp, true_implies, not_le_of_gt hp, false_or]
    exact continuousAt_iff_leftSample p.1 hp
  · simp only [hp, false_implies, le_of_not_gt hp, true_or]

/-- For almost every positive time, a càdlàg path is continuous under the given law. -/
theorem ae_continuousAt_of_ae_time (μ : ProbabilityMeasure (D E)) :
    ∀ᵐ t : ℝ ∂volume, 0 < t →
      ∀ᵐ x ∂(μ : Measure (D E)), ContinuousAt x.1 t.toNNReal := by
  have hx : ∀ᵐ x ∂(μ : Measure (D E)), ∀ᵐ t : ℝ ∂volume,
      0 < t → ContinuousAt x.1 t.toNNReal := by
    filter_upwards with x
    filter_upwards [ae_continuousAt_time x] with t ht htpos
    exact ht htpos.le
  have hy := (Measure.ae_ae_comm (μ := (μ : Measure (D E))) (ν := volume)
    measurable_positive_continuity).mp hx
  filter_upwards [hy] with t ht htpos
  exact ht.mono fun x h => h htpos

/-- Every càdlàg law has a dense set of positive almost-sure continuity times. -/
theorem exists_dense_positive_ae_continuous (μ : ProbabilityMeasure (D E)) :
    ∃ T : Set Time, Dense T ∧ T ⊆ Ioi 0 ∧
      ∀ t ∈ T, ∀ᵐ x ∂(μ : Measure (D E)), ContinuousAt x.1 t := by
  let T : Set Time := {t | 0 < t ∧ ∀ᵐ x ∂(μ : Measure (D E)), ContinuousAt x.1 t}
  refine ⟨T, ?_, (fun t ht => ht.1), (fun t ht => ht.2)⟩
  have hdense : Dense {t : ℝ | 0 < t →
      ∀ᵐ x ∂(μ : Measure (D E)), ContinuousAt x.1 t.toNNReal} :=
    Measure.dense_of_ae (μ := (volume : Measure ℝ)) (ae_continuousAt_of_ae_time μ)
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨u, _, hu, hlim⟩ := hdense.exists_seq_strictAnti_tendsto (t : ℝ)
  have ht : Tendsto (fun n => (u n).toNNReal) atTop (𝓝 t) := by
    simpa only [Real.toNNReal_coe] using tendsto_real_toNNReal hlim
  apply mem_closure_of_tendsto ht
  refine Eventually.of_forall fun n => ?_
  have hu0 : 0 < u n := lt_of_le_of_lt t.2 (hu n).1
  exact ⟨Real.toNNReal_pos.mpr hu0, (hu n).2 hu0⟩


/-- Relative compactness and positive-time joint-law convergence imply weak
convergence of half-line càdlàg path laws. -/
theorem tendsto_of_compact_of_jointLaw_tendsto_positive
    {μ : ℕ → ProbabilityMeasure (D E)} {ν : ProbabilityMeasure (D E)}
    (hcompact : IsCompact (closure (Set.range μ)))
    (h : ∀ (k : ℕ) (ts : Fin k → Time), (∀ i, 0 < ts i) →
      Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply tendsto_of_compact_of_jointLaw_tendsto hcompact
    (S := Ioi 0) (fun ρ _ => exists_dense_positive_ae_continuous ρ)
  exact h

end

end LatticeProb.Cadlag.HalfLine
