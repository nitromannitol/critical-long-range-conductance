import LongRange.Walk.Compactness
import LatticeProb.Prob.Cadlag.HalfLine.RestrictionTight
import LatticeProb.External.BillingsleySkorokhod

/-!
# Tightness of the rescaled walks on a finite horizon

The half-line path laws of the rescaled walks are relatively compact, and their expected
increments across any fixed time vanish uniformly with the time increment. Hence no limit law
has a fixed jump at the horizon, and the restrictions to `[0,T]` are tight in the Polish
finite-horizon Skorokhod space.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Cadlag.HalfLine
open scoped NNReal ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- Tight embedded initial laws put uniformly small mass outside large physical radii. -/
theorem initial_radius_tail_of_isTight (μ : Set.Ioo (0 : ℝ) 1 → Measure (Site d))
    (hμ : IsTightMeasureSet {Measure.map (walkEmbed ε.1) (μ ε) | (ε : Set.Ioo (0 : ℝ) 1)}) :
    ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ ε,
      μ ε {x | R < radius (physical ε x)} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨K, hKc, hKb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμ
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  refine ⟨R, fun ε => ?_⟩
  have h := hKb _ ⟨ε, rfl⟩
  rw [Measure.map_apply (measurable_of_countable _) hKc.isClosed.measurableSet.compl] at h
  refine le_trans (measure_mono ?_) h
  intro x hx hxK
  have hx' := hR hxK
  rw [Metric.mem_closedBall, dist_zero_right, walkEmbed, ← radius_norm] at hx'
  exact (not_le.mpr hx) hx'

/-- Expected truncated increments of the rescaled walk over a short time are uniformly small. -/
theorem walk_lintegral_increment_le (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (μ : Measure (Site d)) [IsProbabilityMeasure μ] (t u : ℝ≥0)
      (δ : ℝ), 0 < δ → δ < 1 → (u : ℝ) ≤ δ →
      ∫⁻ h, ENNReal.ofReal (min (dist (walkEmbed ε (h.position (t + u)))
          (walkEmbed ε (h.position t))) 1) ∂(walkRates hd hε.1 hlam a ha).regularLaw μ ≤
        ENNReal.ofReal (δ ^ (1 / 3 : ℝ) + K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) := by
  obtain ⟨K, hK, htail⟩ := walk_displacement_tail hMSC hNash hDavies hd hlam a ha
  refine ⟨K, hK.le, ?_⟩
  intro ε hε μ _ t u δ hδ hδ1 hu
  have hβ : ∀ v x η, 0 < η → (walkRates hd hε.1 hlam a ha).transitionKernel v x
      {y | η < dist (walkEmbed ε y) (walkEmbed ε x)} ≤
        ENNReal.ofReal (K * v * (1 + Real.log (2 + η)) / η ^ 2) := by
    intro v x η hη
    simpa only [dist_walkEmbed] using htail ε hε v x η hη
  exact (JumpChain.BoundedRates.lintegral_increment_le _ (walkEmbed ε) _ hβ μ t u
    (Real.rpow_pos_of_pos hδ _)).trans
    (JumpChain.BoundedRates.increment_cutoff_le _ hK.le (fun _ _ _ => le_rfl) hδ hδ1 u hu)

/-- The width-dependent bound for the expected averaged increments of the rescaled walks. -/
def averagedIncrementBound (K h : ℝ) : ℝ :=
  if h < 1 / 2 then (2 * h) ^ (1 / 3 : ℝ) + K * (2 * h) ^ (1 / 3 : ℝ) * (1 + Real.log 3) else 1

/-- The averaged-increment bound vanishes as the width tends to zero. -/
theorem tendsto_averagedIncrementBound (K : ℝ) :
    Tendsto (averagedIncrementBound K) (𝓝[>] 0) (𝓝 0) := by
  have h2 : Tendsto (fun h : ℝ => 2 * h) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => by
      simp only [Set.mem_Ioi]; linarith⟩
    simpa only [mul_zero] using
      ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
  refine ((walk_increment_bound_tendsto K).comp h2).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with h hh
  simp only [Function.comp_apply, averagedIncrementBound, if_pos hh.2]

/-- Expected averaged increments of the rescaled walk laws obey the uniform width bound. -/
theorem walk_averagedIncrement_le (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (μ : Measure (Site d)) [IsProbabilityMeasure μ] (T : Time) (h : ℝ), 0 < h →
      ∫ x, averagedIncrement T h x
          ∂(pathLaw (walkRates hd hε.1 hlam a ha) μ (walkEmbed ε) :
            Measure (D (EuclideanSpace ℝ (Fin d)))) ≤ averagedIncrementBound K h := by
  obtain ⟨K, hK, hinc⟩ := walk_lintegral_increment_le hMSC hNash hDavies hd hlam a ha
  refine ⟨K, hK, ?_⟩
  intro ε hε μ _ T h hh
  apply integral_averagedIncrement_le _ T hh
  intro s t hs1 hs2 ht1 ht2
  have hm : Measurable (fun x : D (EuclideanSpace ℝ (Fin d)) =>
      boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal)) :=
    continuous_boundedDistance.measurable.comp
      ((measurable_eval _).prodMk (measurable_eval _))
  have hint : Integrable (fun x : D (EuclideanSpace ℝ (Fin d)) =>
      boundedDistance (x.1 s.toNNReal) (x.1 t.toNNReal))
      (pathLaw (walkRates hd hε.1 hlam a ha) μ (walkEmbed ε) : Measure _) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ fun x => norm_boundedDistance_le_one _ _)
  by_cases hsmall : h < 1 / 2
  · rw [averagedIncrementBound, if_pos hsmall]
    have hT0 : (0 : ℝ) ≤ T := T.2
    have hst : s.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal (by linarith)
    let u : ℝ≥0 := t.toNNReal - s.toNNReal
    have htu : t.toNNReal = s.toNNReal + u := (add_tsub_cancel_of_le hst).symm
    have hu : (u : ℝ) ≤ 2 * h := by
      rw [NNReal.coe_sub hst, Real.coe_toNNReal _ (by linarith)]
      have := Real.le_coe_toNNReal s
      linarith
    have hl := hinc ε hε μ s.toNNReal u (2 * h) (by linarith) (by linarith) hu
    rw [pathLaw, ProbabilityMeasure.toMeasure_map,
      integral_map (measurable_halfLinePath _).aemeasurable hm.aestronglyMeasurable]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => boundedDistance_nonneg _ _)
      (hm.comp (measurable_halfLinePath _)).aestronglyMeasurable]
    apply ENNReal.toReal_le_of_le_ofReal
    · have h0 : (0 : ℝ) ≤ (2 * h) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
      have h1 : 0 ≤ 1 + Real.log 3 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
        linarith
      positivity
    · refine le_trans (le_of_eq ?_) hl
      congr 1
      funext x
      simp only [JumpChain.RegularHistory.halfLinePath_apply, htu, boundedDistance, dist_comm]
  · rw [averagedIncrementBound, if_neg hsmall]
    calc
      _ ≤ ∫ _x, (1 : ℝ) ∂(pathLaw (walkRates hd hε.1 hlam a ha) μ (walkEmbed ε) :
          Measure (D (EuclideanSpace ℝ (Fin d)))) :=
        integral_mono hint (integrable_const 1) (fun x => min_le_right _ _)
      _ = 1 := by simp

/-- Proposition 6.1: for tight initial laws, the restrictions of the rescaled walks to a positive
finite horizon are tight in the finite-horizon Skorokhod space. -/
theorem walk_restrict_isTight (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (hRC : External.EthierKurtzRelativeCompactness)
    (hPol : External.BillingsleySkorokhodPolish) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (T : ℝ) (hT : 0 < T) (μ : Set.Ioo (0 : ℝ) 1 → Measure (Site d))
    [∀ ε, IsProbabilityMeasure (μ ε)]
    (hμ : IsTightMeasureSet {Measure.map (walkEmbed ε.1) (μ ε) | (ε : Set.Ioo (0 : ℝ) 1)}) :
    IsTightMeasureSet {(((pathLaw (walkRates hd ε.2.1 hlam a ha) (μ ε) (walkEmbed ε)).map
      (measurable_restrict T).aemeasurable : ProbabilityMeasure
        (Cadlag.D T (EuclideanSpace ℝ (Fin d)))) : Measure (Cadlag.D T (EuclideanSpace ℝ (Fin d))))
        | ε} := by
  have hK := walk_pathLaws_relativelyCompact hMSC hNash hDavies hRC hd hlam a ha μ
    (initial_radius_tail_of_isTight μ hμ)
  obtain ⟨K, _, hinc⟩ := walk_averagedIncrement_le hMSC hNash hDavies hd hlam a ha
  obtain ⟨hsep, hcm⟩ := hPol (EuclideanSpace ℝ (Fin d)) T hT
  exact isTightMeasureSet_restrict_of_averagedIncrement (T := ⟨T, hT.le⟩) hT hsep hcm
    (fun ε => pathLaw (walkRates hd ε.2.1 hlam a ha) (μ ε) (walkEmbed ε)) hK
    (averagedIncrementBound K) (tendsto_averagedIncrementBound K)
    (fun ε h hh _ => hinc ε.1 ε.2 (μ ε) ⟨T, hT.le⟩ h hh)

end

end LongRange
