import LongRange.Walk.CellAverageLp
import LatticeProb.Walk.RiemannLattice
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Norms and pairings of full-cell averages

Compactly supported continuous functions that vanish off the domain have the expected
sampling limit. Density and contraction extend the norm limit to every L² class on a
bounded measurable domain with null frontier. Polarization then gives convergence of pairings.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped ENNReal NNReal Topology

noncomputable section

variable {d : ℕ}

/-- Restricting a sampled square to the domain loses no terms for a function zero outside it. -/
theorem l2NormSq_sample_eq_tsum {U : Set (Fin d → ℝ)}
    {F : (Fin d → ℝ) → ℝ} (hzero : ∀ y, y ∉ U → F y = 0) (ε : ℝ) :
    l2NormSq ε U (fun q => F (physical ε q)) =
      ε ^ d * ∑' q : Site d, F (physical ε q) ^ 2 := by
  unfold l2NormSq
  congr 1
  apply tsum_subtype_eq_of_support_subset
    (f := fun q : Site d => F (physical ε q) ^ 2) (s := latticeSet ε U)
  intro q hq
  by_contra hnot
  apply hq
  change F (physical ε q) ^ 2 = 0
  rw [hzero _ hnot, zero_pow (by decide)]

/-- The squared sampling norm converges to the integral with the physical volume factor. -/
theorem tendsto_l2NormSq_sample {U : Set (Fin d → ℝ)}
    {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) (hc : HasCompactSupport F)
    (hzero : ∀ y, y ∉ U → F y = 0) :
    Tendsto (fun ε => l2NormSq ε U (fun q => F (physical ε q)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ y in U, F y ^ 2)) := by
  have hs : HasCompactSupport (fun y => F y ^ 2) := by
    have heq : (fun y => F y ^ 2) = F * F := by
      funext y
      exact sq (F y)
    rw [heq]
    exact hc.mul_right
  have ht := (LatticeProb.Walk.tendsto_latticeSum_mul_rpow (hF.pow 2) hs).comp
    tendsto_inv_nhdsGT_zero
  simp only [Pi.pow_apply] at ht
  have hi : (∫ y in U, F y ^ 2) = ∫ y, F y ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hzero y hy]
    norm_num
  rw [hi]
  convert ht using 1
  funext ε
  rw [l2NormSq_sample_eq_tsum hzero]
  simp only [Function.comp_apply, one_div, inv_inv]
  simp only [div_inv_eq_mul]
  calc
    ε ^ d * (∑' q : Site d, F (physical ε q) ^ 2) =
        (∑' q : Site d, F (physical ε q) ^ 2) * ε ^ d := mul_comm _ _
    _ = (∑' q : Site d, F (fun i => (q i : ℝ) * ε) ^ 2) * ε ^ d := by
      congr 1
      apply tsum_congr
      intro q
      apply congrArg (fun y => F y ^ 2)
      funext i
      exact mul_comm ε (q i : ℝ)


/-- Continuous compactly supported functions vanishing off a domain with null frontier
approximate every square-integrable class on that domain. -/
theorem exists_continuous_memLp_zero_off_eLpNorm_sub_le
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U)
    (hfront : volume (frontier U) = 0)
    {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict U))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : (Fin d → ℝ) → ℝ, eLpNorm (f - g) 2 (volume.restrict U) ≤ ε ∧
      Continuous g ∧ MemLp g 2 (volume.restrict U) ∧ HasCompactSupport g ∧
      (∀ y, y ∉ U → g y = 0) := by
  let μ := volume.restrict U
  have hmem : ∀ᵐ y ∂μ, y ∈ interior U := by
    have hi := interior_ae_eq_of_null_frontier hfront
    filter_upwards [ae_restrict_of_ae hi, ae_restrict_mem hU] with y hy hyU
    exact hy.mpr hyU
  apply hf.induction_dense (by norm_num)
    (fun g => Continuous g ∧ MemLp g 2 μ ∧ HasCompactSupport g ∧
      (∀ y, y ∉ U → g y = 0)) _ _ _ hε
  · intro c t ht htμ δ hδ
    obtain ⟨η, hη, hhalf⟩ := exists_Lp_half (μ := μ) (ε := ℝ) 2 hδ
    obtain ⟨a, ha, hsmall⟩ : ∃ a : NNReal, 0 < a ∧
        ∀ s : Set (Fin d → ℝ), μ s ≤ a →
          eLpNorm (s.indicator (fun _ => c)) 2 μ ≤ η :=
      exists_eLpNorm_indicator_le (p := (2 : ℝ≥0∞)) (μ := μ) (by norm_num) c hη.ne'
    obtain ⟨s, hst, hsc, hsclosed, hdiff⟩ :=
      (ht.inter isOpen_interior.measurableSet).exists_isCompact_isClosed_sdiff_lt
        ((measure_mono Set.inter_subset_left).trans_lt htμ).ne
        (ENNReal.coe_pos.mpr ha).ne'
    have hst' : s ⊆ t := hst.trans Set.inter_subset_left
    have hsU : s ⊆ interior U := hst.trans Set.inter_subset_right
    have hdiff' : μ (t \ s) < a := by
      have heq : (t \ s : Set (Fin d → ℝ)) =ᵐ[μ]
          ((t ∩ interior U) \ s : Set (Fin d → ℝ)) := by
        filter_upwards [hmem] with y hy
        change (y ∈ t ∧ y ∉ s) = ((y ∈ t ∧ y ∈ interior U) ∧ y ∉ s)
        simp only [hy, and_true]
      rwa [measure_congr heq]
    have hfirst : eLpNorm
        ((s.indicator (fun _ => c)) - t.indicator (fun _ => c)) 2 μ ≤ η := by
      rw [← eLpNorm_neg, neg_sub, ← Set.indicator_sdiff hst']
      exact hsmall _ hdiff'.le
    obtain ⟨k, hkc, hsk⟩ := exists_compact_superset hsc
    obtain ⟨g, hgc, hgerr, _, hgsupp, hgm⟩ :=
      exists_continuous_eLpNorm_sub_le_of_closed (μ := μ) (p := (2 : ℝ≥0∞))
        (by norm_num) hsclosed
        (isOpen_interior.inter isOpen_interior) (Set.subset_inter hsk hsU)
        ((measure_mono hst').trans_lt htμ).ne c hη.ne'
    refine ⟨g, ?_, hgc, hgm, ?_, ?_⟩
    · have herr := hhalf (g - s.indicator (fun _ => c))
        (s.indicator (fun _ => c) - t.indicator (fun _ => c))
        (hgm.aestronglyMeasurable.sub
          (aestronglyMeasurable_const.indicator hsclosed.measurableSet))
        ((aestronglyMeasurable_const.indicator hsclosed.measurableSet).sub
          (aestronglyMeasurable_const.indicator ht)) hgerr hfirst
      simpa only [sub_add_sub_cancel] using herr.le
    · apply HasCompactSupport.intro hkc
      intro y hy
      exact Function.notMem_support.mp (fun hg => hy (interior_subset (hgsupp hg).1))
    · intro y hy
      exact Function.notMem_support.mp (fun hg => hy (interior_subset (hgsupp hg).2))
  · intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, ?_⟩
    intro y hy
    simp only [Pi.add_apply, hf.2.2.2 y hy, hg.2.2.2 y hy, add_zero]
  · intro g hg
    exact hg.2.1.aestronglyMeasurable

/-- Full-cell averaging is asymptotically isometric on continuous compactly supported
functions which vanish outside the domain. -/
theorem tendsto_norm_cellAverageLp_of_continuous
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) (hc : HasCompactSupport F)
    (hzero : ∀ y, y ∉ U → F y = 0) (hf : MemLp F 2 (volume.restrict U)) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      ‖cellAverageLp ε.property hU hb (hf.toLp F)‖)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 ‖hf.toLp F‖) := by
  let l := comap (Subtype.val : {ε : ℝ // 0 < ε} → ℝ) (𝓝[>] (0 : ℝ))
  let A (ε : {ε : ℝ // 0 < ε}) := cellAverageLp ε.property hU hb (hf.toLp F)
  let S (ε : {ε : ℝ // 0 < ε}) :=
    (memLp_latticeMeasure ε.property hb (fun q => F (physical ε.val q))).toLp _
  have hval : Tendsto (Subtype.val : {ε : ℝ // 0 < ε} → ℝ) l (𝓝[>] 0) :=
    tendsto_comap
  have hs : Tendsto (fun ε => ‖S ε‖) l (𝓝 ‖hf.toLp F‖) := by
    have ht := (Real.continuous_sqrt.tendsto _).comp
      ((tendsto_l2NormSq_sample hF hc hzero).comp hval)
    have he (ε : {ε : ℝ // 0 < ε}) :
        Real.sqrt (l2NormSq ε.val U (fun q => F (physical ε.val q))) = ‖S ε‖ := by
      rw [← norm_sq_toLp_latticeMeasure ε.property hb, Real.sqrt_sq_eq_abs, abs_norm]
    rw [← norm_sq_toLp_real hf] at ht
    simpa only [Function.comp_def, he, Real.sqrt_sq_eq_abs, abs_norm] using ht
  have hu : UniformContinuous F :=
    hF.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  have he : Tendsto (fun ε => ‖A ε - S ε‖) l (𝓝 0) := by
    have ht := (Real.continuous_sqrt.tendsto _).comp
      ((tendsto_cellAverage_sub_sample_of_uniformContinuous hb hu hzero).comp hval)
    have hid (ε : {ε : ℝ // 0 < ε}) :
        Real.sqrt (l2NormSq ε.val U
          (fun q => cellAverage ε.val U F q - F (physical ε.val q))) = ‖A ε - S ε‖ := by
      rw [← norm_sq_toLp_latticeMeasure ε.property hb, Real.sqrt_sq_eq_abs, abs_norm]
      dsimp [A, S]
      rw [cellAverageLp_toLp ε.property hU hb hf, ← MemLp.toLp_sub]
      rfl
    simpa only [Function.comp_def, hid, Real.sqrt_zero] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hs.sub he)
    (by simpa only [add_zero] using hs.add he)
  · intro ε
    have ht := norm_sub_norm_le (S ε) (A ε)
    rw [norm_sub_rev] at ht
    linarith
  · intro ε
    have ht := norm_sub_norm_le (A ε) (S ε)
    linarith

/-- Full-cell averaging preserves the L² norm asymptotically on bounded measurable
domains with Lebesgue-null frontier. -/
theorem tendsto_norm_cellAverageLp
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (hfront : volume (frontier U) = 0) (f : Lp ℝ 2 (volume.restrict U)) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} => ‖cellAverageLp ε.property hU hb f‖)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 ‖f‖) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hquarter : 0 < δ / 4 := by positivity
  obtain ⟨g, happrox, hgc, hgm, hgs, hgzero⟩ :=
    exists_continuous_memLp_zero_off_eLpNorm_sub_le hU hfront (Lp.memLp f)
      (ENNReal.ofReal_ne_zero_iff.mpr hquarter)
  let G := hgm.toLp g
  have hdist : ‖f - G‖ ≤ δ / 4 := by
    have hn := Lp.norm_toLp (⇑f - g) ((Lp.memLp f).sub hgm)
    rw [MemLp.toLp_sub (Lp.memLp f) hgm, Lp.toLp_coeFn] at hn
    rw [hn]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top happrox).trans_eq
      (ENNReal.toReal_ofReal hquarter.le)
  have ht := tendsto_norm_cellAverageLp_of_continuous hU hb hgc hgs hgzero hgm
  filter_upwards [Metric.tendsto_nhds.mp ht (δ / 2) (by positivity)] with ε hε
  have hcontract :
      ‖cellAverageLp ε.property hU hb f - cellAverageLp ε.property hU hb G‖ ≤
        ‖f - G‖ := by
    rw [← map_sub]
    exact norm_cellAverageLinearMap_le ε.property hU hb (f - G)
  have hfirst := (dist_norm_norm_le
    (cellAverageLp ε.property hU hb f) (cellAverageLp ε.property hU hb G)).trans
      (hcontract.trans hdist)
  have hlast : dist ‖G‖ ‖f‖ ≤ δ / 4 := by
    exact (dist_norm_norm_le G f).trans (by simpa only [norm_sub_rev] using hdist)
  have htriangle := (dist_triangle
    ‖cellAverageLp ε.property hU hb f‖ ‖cellAverageLp ε.property hU hb G‖ ‖f‖).trans
      (add_le_add_right (dist_triangle ‖cellAverageLp ε.property hU hb G‖ ‖G‖ ‖f‖) _)
  change dist ‖cellAverageLp ε.property hU hb f‖ ‖f‖ < δ
  change dist ‖cellAverageLp ε.property hU hb G‖ ‖G‖ < δ / 2 at hε
  linarith

/-- Norm and pairing convergence are equivalent for the full-cell linear operators.
This is an algebraic reduction; it does not assert either convergence statement. -/
theorem tendsto_inner_cellAverageLp_iff_norm
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U) :
    (∀ f h : Lp ℝ 2 (volume.restrict U),
      Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
        inner ℝ (cellAverageLp ε.property hU hb f) (cellAverageLp ε.property hU hb h))
        (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (inner ℝ f h))) ↔
    (∀ f : Lp ℝ 2 (volume.restrict U),
      Tendsto (fun ε : {ε : ℝ // 0 < ε} => ‖cellAverageLp ε.property hU hb f‖)
        (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 ‖f‖)) := by
  constructor
  · intro h f
    have ht := (Real.continuous_sqrt.tendsto _).comp (h f f)
    simpa only [Function.comp_def, real_inner_self_eq_norm_sq,
      Real.sqrt_sq_eq_abs, abs_norm] using ht
  · intro h f g
    have ht := (((h (f + g)).mul (h (f + g))).sub ((h f).mul (h f))).sub
      ((h g).mul (h g)) |>.div_const (2 : ℝ)
    simpa only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
      map_add] using ht

/-- Pairings of full-cell averages converge to the continuum L² pairing. -/
theorem tendsto_inner_cellAverageLp
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (hfront : volume (frontier U) = 0) (f h : Lp ℝ 2 (volume.restrict U)) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      inner ℝ (cellAverageLp ε.property hU hb f) (cellAverageLp ε.property hU hb h))
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (inner ℝ f h)) :=
  (tendsto_inner_cellAverageLp_iff_norm hU hb).mpr
    (tendsto_norm_cellAverageLp hU hb hfront) f h

end

end LongRange
