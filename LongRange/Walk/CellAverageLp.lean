import LongRange.Walk.CellAverage
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import LatticeProb.Analysis.TaylorHolder

/-!
# Cell averages on square-integrable equivalence classes

The discrete carrier uses physical cell volume times counting measure restricted to
lattice sites in the domain.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Counting measure on the domain lattice, weighted by physical cell volume. -/
def latticeMeasure (ε : ℝ) (U : Set (Fin d → ℝ)) : Measure (Site d) :=
  ENNReal.ofReal (ε ^ d) • Measure.count.restrict (latticeSet ε U)

/-- The real square-integrable discrete carrier. -/
abbrev discreteL2 (ε : ℝ) (U : Set (Fin d → ℝ)) :=
  Lp ℝ 2 (latticeMeasure ε U)

/-- Every function on a bounded domain lattice is square-integrable. -/
theorem memLp_latticeMeasure {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (g : Site d → ℝ) :
    MemLp g 2 (latticeMeasure ε U) := by
  classical
  have hs := latticeSet_finite hε hb
  haveI : IsFiniteMeasure (Measure.count.restrict (latticeSet ε U)) :=
    ⟨by
      simp only [Measure.restrict_apply_univ, Measure.count_apply_finite _ hs]
      exact ENNReal.natCast_lt_top _⟩
  haveI : IsFiniteMeasure (latticeMeasure ε U) :=
    ⟨by
      rw [latticeMeasure, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  obtain ⟨C, hC⟩ := (hs.image (fun q => ‖g q‖)).bddAbove
  apply MemLp.of_bound (measurable_of_countable g).aestronglyMeasurable C
  apply Measure.ae_smul_measure _ _
  exact (ae_restrict_mem hs.measurableSet).mono (fun q hq => hC ⟨q, hq, rfl⟩)

/-- The squared real L² norm is the integral of the square. -/
theorem norm_sq_toLp_real {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The discrete carrier norm has exactly the paper's volume normalization. -/
theorem norm_sq_toLp_latticeMeasure {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (g : Site d → ℝ) :
    ‖(memLp_latticeMeasure hε hb g).toLp g‖ ^ 2 = l2NormSq ε U g := by
  rw [norm_sq_toLp_real, latticeMeasure, integral_smul_measure]
  have hs := latticeSet_finite hε hb
  have hi : IntegrableOn (fun q => g q ^ 2) (latticeSet ε U) Measure.count := by
    have hm := memLp_latticeMeasure hε hb g
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr
      (pow_pos hε d)) ENNReal.ofReal_ne_top).mp hm.integrable_sq
  rw [setIntegral_countable _ hs.countable hi]
  simp only [Measure.real, Measure.count_singleton, ENNReal.toReal_one,
    one_mul, ENNReal.toReal_ofReal (pow_nonneg hε.le _), smul_eq_mul, l2NormSq]

/-- Cell averaging is additive on square-integrable representatives. -/
theorem cellAverage_add {ε : ℝ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U)
    {f g : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) :
    cellAverage ε U (f + g) = cellAverage ε U f + cellAverage ε U g := by
  funext q
  have hi := (memLp_indicator_iff_restrict hU).mpr hf
  have hj := (memLp_indicator_iff_restrict hU).mpr hg
  have hv : volume (cellCube ε q) ≠ ⊤ := by
    rw [cellCube_eq_pi, Real.volume_pi_Ico]
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  haveI : IsFiniteMeasure (volume.restrict (cellCube ε q)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hv.lt_top⟩
  simp only [cellAverage, Set.indicator_add', Pi.add_apply,
    integral_add ((hi.restrict _).integrable (by norm_num))
      ((hj.restrict _).integrable (by norm_num)), mul_add]

/-- Cell averaging respects real scalar multiplication. -/
theorem cellAverage_smul (ε : ℝ) (U : Set (Fin d → ℝ))
    (c : ℝ) (f : (Fin d → ℝ) → ℝ) :
    cellAverage ε U (c • f) = c • cellAverage ε U f := by
  funext q
  change (ε ^ d)⁻¹ * (∫ y in cellCube ε q, U.indicator (fun y => c • f y) y) =
    c * cellAverage ε U f q
  rw [Set.indicator_const_smul, integral_smul]
  simp only [cellAverage, smul_eq_mul]
  ring

/-- Cell averaging as a linear map on almost-everywhere classes. -/
def cellAverageLinearMap {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U) :
    Lp ℝ 2 (volume.restrict U) →ₗ[ℝ] discreteL2 ε U where
  toFun f := (memLp_latticeMeasure hε hb (cellAverage ε U f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro q
    rw [cellAverage_congr_ae hU (Lp.coeFn_add f g),
      cellAverage_add hU (Lp.memLp f) (Lp.memLp g)]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro q
    rw [cellAverage_congr_ae hU (Lp.coeFn_smul c f), cellAverage_smul]
    rfl

/-- The linear comparison map contracts the real L² norm. -/
theorem norm_cellAverageLinearMap_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (f : Lp ℝ 2 (volume.restrict U)) :
    ‖cellAverageLinearMap hε hU hb f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(memLp_latticeMeasure hε hb (cellAverage ε U f)).toLp _‖ ^ 2 ≤ _
  rw [norm_sq_toLp_latticeMeasure hε hb]
  have hn : ‖f‖ ^ 2 = ∫ y in U, f y ^ 2 := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_real (Lp.memLp f)
  rw [hn]
  exact l2NormSq_cellAverage_le hε hU hb (Lp.memLp f)

/-- Full-cell averaging as a contraction between real L² spaces. -/
def cellAverageLp {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] discreteL2 ε U :=
  (cellAverageLinearMap hε hU hb).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using norm_cellAverageLinearMap_le hε hU hb f)

/-- The comparison operators have norm at most one, uniformly in scale. -/
theorem norm_cellAverageLp_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U) :
    ‖cellAverageLp hε hU hb‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Applying the comparison operator to a representative gives its full-cell averages. -/
theorem cellAverageLp_toLp {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    cellAverageLp hε hU hb (hf.toLp f) =
      (memLp_latticeMeasure hε hb (cellAverage ε U f)).toLp _ := by
  change (memLp_latticeMeasure hε hb (cellAverage ε U (hf.toLp f))).toLp _ = _
  exact MemLp.toLp_congr _ _
    (Filter.Eventually.of_forall (cellAverage_congr_ae hU hf.coeFn_toLp))

/-- A bound on oscillation within one full cell bounds its sampling error. -/
theorem abs_cellAverage_sub_sample_le_of_cell_bound {ε : ℝ} (hε : 0 < ε)
    (U : Set (Fin d → ℝ)) {F : (Fin d → ℝ) → ℝ} (hF : Continuous F)
    (hzero : ∀ y, y ∉ U → F y = 0) (q : Site d) (a : ℝ)
    (hm : ∀ y ∈ cellCube ε q, |F y - F (physical ε q)| ≤ a) :
    |cellAverage ε U F q - F (physical ε q)| ≤ a := by
  classical
  have hext : U.indicator F = F := by
    funext y
    by_cases hy : y ∈ U
    · exact Set.indicator_of_mem hy F
    · rw [Set.indicator_of_notMem hy, hzero y hy]
  have hv : volume (cellCube ε q) ≠ ⊤ := by
    rw [volume_cellCube hε]
    exact ENNReal.ofReal_ne_top
  have hi : IntegrableOn F (cellCube ε q) volume := by
    apply Measure.integrableOn_of_bounded hv hF.aestronglyMeasurable
    apply (ae_restrict_mem (measurableSet_cellCube ε q)).mono
    intro y hy
    have := hm y hy
    have ht := abs_add_le (F y - F (physical ε q)) (F (physical ε q))
    rw [Real.norm_eq_abs]
    simp only [sub_add_cancel] at ht
    exact ht.trans (add_le_add this le_rfl)
  have hid : cellAverage ε U F q - F (physical ε q) =
      (ε ^ d)⁻¹ * ∫ y in cellCube ε q, (F y - F (physical ε q)) := by
    rw [cellAverage, hext, integral_sub hi (integrableOn_const hv),
      integral_const, Measure.real, Measure.restrict_apply_univ, volume_cellCube hε,
      ENNReal.toReal_ofReal (pow_nonneg hε.le _), smul_eq_mul]
    field_simp [ne_of_gt (pow_pos hε d)]
  have hn := norm_setIntegral_le_of_norm_le_const hv.lt_top
    (fun y hy => (show ‖F y - F (physical ε q)‖ ≤ a from hm y hy))
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  have hvreal : volume.real (cellCube ε q) = ε ^ d := by
    rw [Measure.real, volume_cellCube hε, ENNReal.toReal_ofReal (pow_nonneg hε.le _)]
  rw [hvreal, Real.norm_eq_abs] at hn
  calc
    (ε ^ d)⁻¹ * |∫ y in cellCube ε q, F y - F (physical ε q)| ≤
        (ε ^ d)⁻¹ * (a * ε ^ d) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (pow_nonneg hε.le _))
    _ = a := by field_simp

/-- Uniform continuity alone makes the discrete cell sampling error vanish. -/
theorem tendsto_cellAverage_sub_sample_of_uniformContinuous
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    {F : (Fin d → ℝ) → ℝ} (hF : UniformContinuous F)
    (hzero : ∀ y, y ∉ U → F y = 0) :
    Tendsto (fun ε => l2NormSq ε U
      (fun q => cellAverage ε U F q - F (physical ε q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  classical
  obtain ⟨C, hC, hc⟩ := ncard_latticeSet_le d (euclideanDiam U)
  have hr : Tendsto (fun ε : ℝ => Real.sqrt d * ε / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hi : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero, zero_div] using
      ((tendsto_const_nhds (x := Real.sqrt (d : ℝ))).mul hi).div_const (2 : ℝ)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ha.trans_le (mul_nonneg (pow_nonneg (le_of_lt hε) _)
      (tsum_nonneg (fun _ => sq_nonneg _)))
  · intro b hbpos
    let η := Real.sqrt (b / (C + 1)) / 2
    have hη : 0 < η := div_pos (Real.sqrt_pos.mpr
      (div_pos hbpos (by linarith))) (by norm_num)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hF η hη
    have he : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ε ∈ Set.Ioo (0 : ℝ) 1 ∧ Real.sqrt d * ε / 2 < δ := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds, hr.eventually (eventually_lt_nhds hδ)] with ε hp h1 hd
      exact ⟨⟨hp, h1⟩, hd⟩
    filter_upwards [he] with ε hε
    have hcount : ε ^ d * (latticeSet ε U).ncard ≤ C := by
      have hh := mul_le_mul_of_nonneg_left
        (hc U hb le_rfl ε hε.1) (pow_nonneg hε.1.1.le d)
      rw [Real.rpow_neg hε.1.1.le, Real.rpow_natCast] at hh
      have hp : ε ^ d ≠ 0 := (pow_pos hε.1.1 d).ne'
      calc
        ε ^ d * (latticeSet ε U).ncard ≤ ε ^ d * (C * (ε ^ d)⁻¹) := hh
        _ = C := by field_simp
    have herr (q : Site d) :
        |cellAverage ε U F q - F (physical ε q)| ≤ η := by
      apply abs_cellAverage_sub_sample_le_of_cell_bound hε.1.1 U hF.continuous
        hzero q η
      intro y hy
      apply le_of_lt
      apply hmod
      rw [dist_eq_norm]
      exact (TaylorHolder.norm_le_radius _).trans_lt
        ((radius_sub_physical_le hε.1.1 q hy).trans_lt hε.2)
    letI := (latticeSet_finite hε.1.1 hb).fintype
    have hsq (q : Site d) :
        (cellAverage ε U F q - F (physical ε q)) ^ 2 ≤ η ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hη.le).mpr (herr q)
    have hbound : l2NormSq ε U
        (fun q => cellAverage ε U F q - F (physical ε q)) ≤ C * η ^ 2 := by
      rw [l2NormSq, tsum_fintype]
      calc
        _ ≤ ε ^ d * ∑ _q : latticeSet ε U, η ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hsq q))
            (pow_nonneg hε.1.1.le _)
        _ = (ε ^ d * (latticeSet ε U).ncard) * η ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Set.fintypeCard_eq_ncard]
          ring
        _ ≤ C * η ^ 2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    apply hbound.trans_lt
    have hroot : (Real.sqrt (b / (C + 1))) ^ 2 = b / (C + 1) :=
      Real.sq_sqrt (le_of_lt (div_pos hbpos (by linarith)))
    have hηsq : η ^ 2 = b / (C + 1) / 4 := by
      dsimp [η]
      rw [div_pow, hroot]
      norm_num
    rw [hηsq]
    have hden : 0 < C + 1 := by linarith
    have hquot : (C + 1) * (b / (C + 1)) = b :=
      mul_div_cancel₀ b hden.ne'
    have hquotpos := div_pos hbpos hden
    nlinarith only [hquot, hquotpos, hbpos]

end

end LongRange
