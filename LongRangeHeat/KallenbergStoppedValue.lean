import LongRangeHeat.KallenbergWeakStopping
import LongRange.Support.Prob.Cadlag.HalfLine.RestrictionTight

/-!
# Stopped values in the raw filtration

A weakly optional time clipped at a fixed horizon has a stopped value measurable
in the information available at that horizon.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology NNReal

variable {E Ω : Type} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SeparableSpace E]

omit [BorelSpace E] [SeparableSpace E] in
/-- A weakly optional time, clipped at a deterministic horizon, is measurable
in the natural information at that horizon. -/
theorem weakNaturalStopping.measurable_min {Y : Ω → D E} {H : ℝ}
    {τ : Ω → Time} (hτ : weakNaturalStopping Y H τ) (t : Time) :
    Measurable[naturalSigma Y t] (fun w => min (τ w) t) := by
  apply measurable_of_Iio
  intro s
  by_cases hts : t < s
  · have heq : (fun w => min (τ w) t) ⁻¹' Iio s = univ := by
      ext w
      simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
      exact (min_le_right _ _).trans_lt hts
    rw [heq]
    exact MeasurableSet.univ
  · have hst : s ≤ t := le_of_not_gt hts
    have heq : (fun w => min (τ w) t) ⁻¹' Iio s = {w | τ w < s} := by
      ext w
      simp only [mem_preimage, mem_Iio, mem_ofPred_eq, min_lt_iff,
        not_lt_of_ge hst, or_false]
    rw [heq]
    exact naturalSigma_mono Y hst _ (hτ.2 s)

/-- A clipped weakly optional time has a measurable stopped value at the
clipping horizon. -/
theorem weakNaturalStopping.measurable_stopped_min {Y : Ω → D E} {H : ℝ}
    {τ : Ω → Time} (hτ : weakNaturalStopping Y H τ) (t : Time) :
    Measurable[naturalSigma Y t] (fun w => (Y w).1 (min (τ w) t)) := by
  let : MeasurableSpace Ω := naturalSigma Y t
  let v : Ω → Time := fun w => min (τ w) t
  have hv : Measurable v := hτ.measurable_min t
  have hstep (n : ℕ) : Measurable (fun w => (Y w).1 (min (gridAbove n (v w)) t)) := by
    have hG : Measurable (fun p : Ω × ℕ =>
        (Y p.1).1 (min (((p.2 + 1 : ℕ) : Time) / (n + 1)) t)) := by
      apply measurable_from_prod_countable_left
      intro j
      rw [measurable_iff_comap_le]
      exact le_iSup_of_le (min (((j + 1 : ℕ) : Time) / (n + 1)) t)
        (le_iSup_of_le (min_le_right _ _) le_rfl)
    have hk : Measurable (fun w => (w, ⌊v w * (n + 1)⌋₊)) :=
      measurable_id.prodMk ((hv.mul_const _).nat_floor)
    exact hG.comp hk
  apply measurable_of_tendsto_metrizable hstep
  apply tendsto_pi_nhds.mpr
  intro w
  have hvt : v w ≤ t := min_le_right _ _
  have hvlim : Tendsto (fun n => min (gridAbove n (v w)) t) atTop (𝓝[Ici (v w)] (v w)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n => le_min (lt_gridAbove n (v w)).le hvt⟩
    have hg := ((tendsto_gridAbove (v w)).mono_right nhdsWithin_le_nhds).min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
    simpa only [min_eq_left hvt] using hg
  exact ((Y w).2.1 (v w)).tendsto.comp hvlim

end LatticeProb.Cadlag.HalfLine
