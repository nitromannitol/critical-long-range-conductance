import LongRangeHeat.FddLimit
import LongRangeHeat.Statements.HeatKernelBounds
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Tightness of the finite-dimensional laws

The displacement bound of Proposition 4.1 gives
`P^a_0[|X^ε_h| > R] ≤ 2 C h / R` for every `R ≥ 1`, every `h ≥ 0`, every `ε ≤ 1/2` and every
realization of the conductances. Hence the laws of `(X^ε_{t_1}, …, X^ε_{t_k})` under the annealed
measure form a tight family of probability measures on `(ℝ^d)^k`, uniformly in `ε`.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.JumpChain LatticeProb.Euclidean.Lattice Set Filter
open scoped NNReal ENNReal Topology
open LongRange (Edge walkRates walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The vector of the observations `(X_{t_1}, …, X_{t_k})` of a path. -/
def pathEval {k : ℕ} (t : Fin k → ℝ≥0) (X : PathSpace d) : Fin k → EuclideanSpace ℝ (Fin d) :=
  fun j => X.1 (t j)

theorem measurable_pathEval {k : ℕ} (t : Fin k → ℝ≥0) : Measurable (pathEval (d := d) t) :=
  measurable_pi_iff.mpr fun j => measurable_eval (t j)

/-- The law of `(X^ε_{t_1}, …, X^ε_{t_k})` under the annealed law. -/
def fddLaw (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {lam : ℝ}
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (t : Fin k → ℝ≥0) : ProbabilityMeasure (Fin k → EuclideanSpace ℝ (Fin d)) :=
  ProbabilityMeasure.map (annealedLaw hd P a hP hε) (pathEval t)

theorem walkEmbed_preimage_norm_gt {ε : ℝ} (R : ℝ) :
    walkEmbed ε ⁻¹' {y : EuclideanSpace ℝ (Fin d) | R < ‖y‖} =
      {z : Site d | R < radius (physical ε (z - 0))} := by
  ext z
  have hphys : physical ε (z - 0) = physical ε z - physical ε 0 := by
    funext k
    simp [physical]
  have h0 : walkEmbed ε (0 : Site d) = 0 := by
    simp [walkEmbed, physical_zero_site]
  simp only [mem_preimage, mem_ofPred_eq, hphys]
  rw [← LongRange.dist_walkEmbed ε z 0, h0, dist_zero_right]

/-- The tail of the transition kernel at the origin, uniformly in the time. -/
theorem kernel_tail_le (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C : ℝ} (hC : 0 ≤ C)
    (hdisp : DisplacementBound hd hε hlam ha C) (h : ℝ≥0) {R : ℝ} (hR : 1 ≤ R)
    (hεR : ε ≤ R) :
    ((walkRates hd hε hlam a ha).transitionKernel h 0).real
        {z | R < radius (physical ε (z - 0))} ≤ 2 * C * h / R := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rcases eq_zero_or_pos h with rfl | hh
  · rw [BoundedRates.transitionKernel_zero, Kernel.id_apply]
    have : (0 : Site d) ∉ {z : Site d | R < radius (physical ε (z - 0))} := by
      simp only [mem_ofPred_eq, sub_zero, physical_zero_site, not_lt]
      simp [radius, hR0.le]
    rw [Measure.real, Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
      Set.indicator_of_notMem this]
    simp
  · refine (hdisp h hh R hεR).trans ?_
    have hlog : Real.log (1 + R) ≤ R := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + R by linarith)
      linarith
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : C * h * (1 + Real.log (1 + R)) ≤ C * h * (2 * R) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc C * h * (1 + Real.log (1 + R)) * R ≤ C * h * (2 * R) * R :=
          mul_le_mul_of_nonneg_right this hR0.le
      _ = 2 * C * h * R ^ 2 := by ring

/-- The annealed marginal at time `t` has tail `P^ann_0[|X^ε_t| > R] ≤ 2 C t / R`. -/
theorem annealedLaw_norm_gt_le (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {lam : ℝ} (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC : 0 ≤ C) (hdisp : ∀ r, DisplacementBound hd hε hP.lam_mem.1 (hP.bounds r) C) (t : ℝ≥0)
    {R : ℝ} (hR : 1 ≤ R) (hεR : ε ≤ R) :
    (annealedLaw hd P a hP hε : Measure (PathSpace d)) {X | R < ‖X.1 t‖} ≤
      ENNReal.ofReal (2 * C * t / R) := by
  have hPm := hP.isProbabilityMeasure
  have hB : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | R < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have h1 := annealedLaw_eval_apply hd P a hP hε t hB
  have h2 : {X : PathSpace d | R < ‖X.1 t‖} = (fun X : PathSpace d => X.1 t) ⁻¹'
      {y : EuclideanSpace ℝ (Fin d) | R < ‖y‖} := rfl
  rw [h2, h1]
  calc ∫⁻ r, (walkRates hd hε hP.lam_mem.1 (a r) (hP.bounds r)).transitionKernel t 0
        (walkEmbed ε ⁻¹' {y : EuclideanSpace ℝ (Fin d) | R < ‖y‖}) ∂P
      ≤ ∫⁻ _r, ENNReal.ofReal (2 * C * t / R) ∂P := by
        refine lintegral_mono fun r => ?_
        rw [walkEmbed_preimage_norm_gt, ← ofReal_measureReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal
          (kernel_tail_le hd hε hP.lam_mem.1 (hP.bounds r) hC (hdisp r) t hR hεR)
    _ = ENNReal.ofReal (2 * C * t / R) := by simp

/-- The finite-dimensional laws of the annealed walk are tight, uniformly in `ε ∈ (0, 1/2)`. -/
theorem isTightMeasureSet_fddLaw
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {lam : ℝ}
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {k : ℕ} (t : Fin k → ℝ≥0) {ι : Type*}
    (ε : ι → ℝ) (hε : ∀ i, ε i ∈ Ioo (0 : ℝ) (1 / 2)) :
    IsTightMeasureSet (range fun i =>
      (fddLaw hd P a hP (hε i).1 t : Measure (Fin k → EuclideanSpace ℝ (Fin d)))) := by
  have hPm := hP.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ := Statements.heat_kernel_bounds hMSC hNash hDavies hd hP.lam_mem
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
