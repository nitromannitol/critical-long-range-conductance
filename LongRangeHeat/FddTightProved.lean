import LongRangeHeat.FddTight
import LongRangeHeat.Statements.HeatKernelBoundsProved

/-!
# Tightness of finite-dimensional distributions

The uniform displacement estimate gives tightness of the annealed laws.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.JumpChain LatticeProb.Euclidean.Lattice Set Filter
open scoped NNReal ENNReal Topology
open LongRange (Edge walkRates walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The finite-dimensional laws of the annealed walk are tight, uniformly in `ε ∈ (0, 1/2)`. -/
theorem isTightMeasureSet_fddLaw_proved
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {lam : ℝ}
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {k : ℕ} (t : Fin k → ℝ≥0) {ι : Type*}
    (ε : ι → ℝ) (hε : ∀ i, ε i ∈ Ioo (0 : ℝ) (1 / 2)) :
    IsTightMeasureSet (range fun i =>
      (fddLaw hd P a hP (hε i).1 t : Measure (Fin k → EuclideanSpace ℝ (Fin d)))) := by
  have hPm := hP.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ := Statements.heat_kernel_bounds_proved hNash hDavies hd hP.lam_mem
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt]
  set T : ℝ := ∑ j, (t j : ℝ) with hT
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal (2 * C * T / R)) atTop (𝓝 0) := by
    have : Tendsto (fun R : ℝ => 2 * C * T / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using ENNReal.tendsto_ofReal this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun R => bot_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  refine iSup₂_le fun ν hν => ?_
  obtain ⟨i, rfl⟩ := hν
  have hmeas : MeasurableSet {x : Fin k → EuclideanSpace ℝ (Fin d) | R < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hεR : ε i ≤ R := by linarith [(hε i).2]
  have hfdd : (fddLaw hd P a hP (hε i).1 t : Measure (Fin k → EuclideanSpace ℝ (Fin d))) =
      Measure.map (pathEval t) (annealedLaw hd P a hP (hε i).1 : Measure (PathSpace d)) := rfl
  dsimp only
  rw [hfdd, Measure.map_apply (measurable_pathEval t) hmeas]
  have hsub : pathEval (d := d) t ⁻¹' {x : Fin k → EuclideanSpace ℝ (Fin d) | R < ‖x‖} ⊆
      ⋃ j, {X : PathSpace d | R < ‖X.1 (t j)‖} := by
    intro X hX
    by_contra hcon
    simp only [mem_iUnion, not_exists, mem_ofPred_eq, not_lt] at hcon
    have : ‖pathEval (d := d) t X‖ ≤ R :=
      (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => hcon j
    exact absurd hX (not_lt.2 this)
  calc _ ≤ ((annealedLaw hd P a hP (hε i).1 : Measure (PathSpace d))
        (⋃ j, {X : PathSpace d | R < ‖X.1 (t j)‖})) := measure_mono hsub
    _ ≤ ∑ j, (annealedLaw hd P a hP (hε i).1 : Measure (PathSpace d))
        {X : PathSpace d | R < ‖X.1 (t j)‖} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j, ENNReal.ofReal (2 * C * (t j : ℝ) / R) :=
        Finset.sum_le_sum fun j _ => annealedLaw_norm_gt_le hd P a hP (hε i).1 hC.le
          (fun r => (hbound (ε i) (hε i) (a r) (hP.bounds r) 0 0).2) (t j) hR hεR
    _ = ENNReal.ofReal (∑ j, 2 * C * (t j : ℝ) / R) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm
    _ = ENNReal.ofReal (2 * C * T / R) := by
        rw [hT, Finset.mul_sum, Finset.sum_div]

end

end LongRangeHeat
