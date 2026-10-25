import LongRange.Walk.CellAverageLp

/-!
# Boundary cells of Euclidean balls

Cells centered in a ball that meet its complement lie in a thin Euclidean shell.
Disjointness of full cells converts their number into a volume bound.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Sites in the domain whose full cell is not contained in the domain. -/
def boundaryCells (ε : ℝ) (U : Set (Fin d → ℝ)) : Set (Site d) :=
  {q ∈ latticeSet ε U | ¬ cellCube ε q ⊆ U}

/-- Boundary sites form a finite set whenever the domain is bounded. -/
theorem boundaryCells_finite {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) :
    (boundaryCells ε U).Finite :=
  (latticeSet_finite hε hU).subset (fun _ hq => hq.1)

/-- Every boundary cell of a Euclidean ball lies in its diagonal-width shell. -/
theorem cellCube_boundaryCells_subset_shell {ε R : ℝ} (hε : 0 < ε)
    {q : Site d} (hq : q ∈ boundaryCells ε {x : Fin d → ℝ | radius x < R}) :
    cellCube ε q ⊆ {y | R - Real.sqrt d * ε ≤ radius y ∧
      radius y ≤ R + Real.sqrt d * ε} := by
  classical
  obtain ⟨z, hz, hzout⟩ := Set.not_subset.mp hq.2
  have hc : radius (physical ε q) < R := hq.1
  have hzR : R ≤ radius z := le_of_not_gt hzout
  have hzdist := radius_sub_physical_le hε q hz
  have hzdiff := (abs_le.mp (radius_difference z (physical ε q))).2
  intro y hy
  have hydist := radius_sub_physical_le hε q hy
  have hydiff := abs_le.mp (radius_difference y (physical ε q))
  have hwidth : 0 ≤ Real.sqrt (d : ℝ) * ε :=
    mul_nonneg (Real.sqrt_nonneg _) hε.le
  constructor <;> dsimp only [Set.mem_setOf_eq] at * <;> linarith

/-- The weighted number of boundary cells is bounded by the volume of any containing set. -/
theorem boundaryCells_volume_le {ε : ℝ} (hε : 0 < ε)
    {U S : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hS : ∀ q ∈ boundaryCells ε U, cellCube ε q ⊆ S) :
    ENNReal.ofReal (ε ^ d) * (boundaryCells ε U).ncard ≤ volume S := by
  classical
  letI := (boundaryCells_finite hε hU).fintype
  have hd : Pairwise (fun q q' : boundaryCells ε U =>
      Disjoint (cellCube ε q.val) (cellCube ε q'.val)) := by
    intro q q' hne
    exact cellCube_disjoint hε (fun h => hne (Subtype.ext h))
  calc
    _ = ∑' q : boundaryCells ε U, volume (cellCube ε q.val) := by
      simp only [volume_cellCube hε, tsum_fintype, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, Set.fintypeCard_eq_ncard]
      rw [mul_comm]
    _ = volume (⋃ q : boundaryCells ε U, cellCube ε q.val) :=
      (measure_iUnion hd (fun q => measurableSet_cellCube ε q.val)).symm
    _ ≤ volume S := measure_mono (Set.iUnion_subset (fun q => hS q.val q.property))

/-- A Euclidean radius sublevel is bounded also in the ambient product topology. -/
theorem isBounded_radius_le (R : ℝ) :
    Bornology.IsBounded {x : Fin d → ℝ | radius x ≤ R} := by
  apply (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := R)).subset
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (TaylorHolder.norm_le_radius x).trans hx

/-- The real weighted boundary-cell count is at most the volume of the radial shell. -/
theorem boundaryCells_weight_le_shell_volume {ε R : ℝ} (hε : 0 < ε) :
    ε ^ d * ((boundaryCells ε {x : Fin d → ℝ | radius x < R}).ncard : ℝ) ≤
      volume.real {y : Fin d → ℝ | R - Real.sqrt d * ε ≤ radius y ∧
        radius y ≤ R + Real.sqrt d * ε} := by
  have hfinite : volume {y : Fin d → ℝ | R - Real.sqrt d * ε ≤ radius y ∧
      radius y ≤ R + Real.sqrt d * ε} ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      ((isBounded_radius_le (d := d) (R + Real.sqrt d * ε)).measure_lt_top
        (μ := volume)).ne
    exact measure_mono (fun _ hy => hy.2)
  have h := boundaryCells_volume_le hε (U := {x : Fin d → ℝ | radius x < R})
    ((isBounded_radius_le (d := d) R).subset (fun x hx => (show radius x < R from hx).le))
    (fun _ hq => cellCube_boundaryCells_subset_shell hε hq)
  have hh := ENNReal.toReal_mono hfinite h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hε.le d),
    ENNReal.toReal_natCast, Measure.real] using hh

/-- A positive-radius Euclidean sphere has zero product Lebesgue volume. -/
theorem volume_radius_eq_zero {R : ℝ} (hR : 0 < R) :
    volume {x : Fin d → ℝ | radius x = R} = 0 := by
  have he : {x : Fin d → ℝ | radius x = R} =
      WithLp.toLp 2 ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) R := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_sphere,
      dist_zero_right, ← radius_norm]
  rw [he, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
  exact Measure.addHaar_sphere_of_ne_zero volume 0 hR.ne'

/-- Volumes of closed shells around a positive-radius sphere tend to zero. -/
theorem tendsto_volume_radius_shell {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ => volume {x : Fin d → ℝ |
      R - t ≤ radius x ∧ radius x ≤ R + t})
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let s := fun t : ℝ => {x : Fin d → ℝ |
    R - t ≤ radius x ∧ radius x ≤ R + t}
  have hs (t : ℝ) : MeasurableSet (s t) :=
    (isClosed_le continuous_const (radius_continuous d)).measurableSet.inter
      (isClosed_le (radius_continuous d) continuous_const).measurableSet
  have hm : ∀ i j : ℝ, 0 < i → i ≤ j → s i ⊆ s j := by
    intro i j _ hij x hx
    constructor <;> dsimp only [s, Set.mem_setOf_eq] at * <;> linarith [hx.1, hx.2]
  have hf : ∃ t > (0 : ℝ), volume (s t) ≠ ⊤ := by
    refine ⟨1, zero_lt_one, ?_⟩
    have hfinite := (isBounded_radius_le (d := d) (R + 1)).measure_lt_top
      (μ := volume)
    apply ne_top_of_le_ne_top hfinite.ne
    exact measure_mono (fun _ hx => hx.2)
  have he : (⋂ t > (0 : ℝ), s t) = {x : Fin d → ℝ | radius x = R} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      apply le_antisymm
      · by_contra! h
        have ht := hx ((radius x - R) / 2) (by linarith)
        dsimp only [s, Set.mem_setOf_eq] at ht
        linarith [ht.2]
      · by_contra! h
        have ht := hx ((R - radius x) / 2) (by linarith)
        dsimp only [s, Set.mem_setOf_eq] at ht
        linarith [ht.1]
    · intro hx t ht
      dsimp only [s, Set.mem_setOf_eq]
      constructor <;> linarith
  have h := tendsto_measure_biInter_gt (μ := volume)
    (fun t _ => (hs t).nullMeasurableSet) hm hf
  rw [he, volume_radius_eq_zero hR] at h
  exact h

/-- The volume of the diagonal-width shell vanishes with the lattice spacing. -/
theorem tendsto_volume_boundary_shell {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => volume {x : Fin d → ℝ |
      R - Real.sqrt d * ε ≤ radius x ∧ radius x ≤ R + Real.sqrt d * ε})
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hc : 0 < Real.sqrt (d : ℝ) + 1 := by positivity
  have hi : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : ℝ => (Real.sqrt d + 1) * ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using tendsto_const_nhds.mul hi
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hc hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((tendsto_volume_radius_shell (d := d) hR).comp ht)
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono
  intro x hx
  have hpos : 0 < ε := hε
  constructor <;> dsimp only [Set.mem_setOf_eq] at * <;> nlinarith [hx.1, hx.2]

/-- The physical volume of boundary cells of a positive-radius ball tends to zero. -/
theorem tendsto_boundaryCells_volume {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ d) *
      (boundaryCells ε {x : Fin d → ℝ | radius x < R}).ncard)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_volume_boundary_shell (d := d) hR)
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact boundaryCells_volume_le hε
    ((isBounded_radius_le (d := d) R).subset (fun x hx => (show radius x < R from hx).le))
    (fun _ hq => cellCube_boundaryCells_subset_shell hε hq)

/-- The real weighted count of boundary cells tends to zero. -/
theorem tendsto_boundaryCells_weight {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ε ^ d *
      ((boundaryCells ε {x : Fin d → ℝ | radius x < R}).ncard : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_boundaryCells_volume (d := d) hR)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change (ENNReal.ofReal (ε ^ d) *
    ((boundaryCells ε {x : Fin d → ℝ | radius x < R}).ncard : ℝ≥0∞)).toReal = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hε) d),
    ENNReal.toReal_natCast]

/-- A cellwise bound on the zero-extension oscillation bounds the averaging error. -/
theorem abs_sample_sub_cellAverage_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}
    (hi : Integrable (U.indicator F) volume) (q : Site d) (a : ℝ)
    (ha : ∀ y ∈ cellCube ε q,
      |F (physical ε q) - U.indicator F y| ≤ a) :
    |F (physical ε q) - cellAverage ε U F q| ≤ a := by
  have hv : volume (cellCube ε q) ≠ ⊤ := by
    rw [volume_cellCube hε]
    exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : Fin d → ℝ => F (physical ε q))
      (cellCube ε q) volume := integrableOn_const hv
  have he : F (physical ε q) - cellAverage ε U F q =
      (ε ^ d)⁻¹ * ∫ y in cellCube ε q,
        (F (physical ε q) - U.indicator F y) := by
    rw [cellAverage, integral_sub hconst hi.integrableOn,
      integral_const, Measure.real, Measure.restrict_apply_univ, volume_cellCube hε,
      ENNReal.toReal_ofReal (pow_nonneg hε.le _), smul_eq_mul]
    field_simp [ne_of_gt (pow_pos (show 0 < ε from hε) d)]
  have hn := norm_setIntegral_le_of_norm_le_const hv.lt_top
    (fun y hy => (show ‖F (physical ε q) - U.indicator F y‖ ≤ a from ha y hy))
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  have hvreal : volume.real (cellCube ε q) = ε ^ d := by
    rw [Measure.real, volume_cellCube hε, ENNReal.toReal_ofReal (pow_nonneg hε.le _)]
  rw [hvreal, Real.norm_eq_abs] at hn
  calc
    _ ≤ (ε ^ d)⁻¹ * (a * ε ^ d) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (pow_nonneg hε.le _))
    _ = a := by field_simp

/-- Splitting lattice sites into boundary and interior sites bounds the total error. -/
theorem sample_sub_cellAverage_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    {F : (Fin d → ℝ) → ℝ} (η M : ℝ)
    (hinterior : ∀ q ∈ latticeSet ε U, q ∉ boundaryCells ε U →
      (F (physical ε q) - cellAverage ε U F q) ^ 2 ≤ η ^ 2)
    (hboundary : ∀ q ∈ boundaryCells ε U,
      (F (physical ε q) - cellAverage ε U F q) ^ 2 ≤ M ^ 2) :
    l2NormSq ε U (fun q => F (physical ε q) - cellAverage ε U F q) ≤
      ε ^ d * (latticeSet ε U).ncard * η ^ 2 +
        ε ^ d * (boundaryCells ε U).ncard * M ^ 2 := by
  classical
  letI := (latticeSet_finite hε hb).fintype
  letI := (boundaryCells_finite hε hb).fintype
  let b : Finset (latticeSet ε U) := Finset.univ.filter
    (fun q => q.val ∈ boundaryCells ε U)
  have hcard : b.card = (boundaryCells ε U).ncard := by
    have he : {q : latticeSet ε U // q ∈ b} ≃ boundaryCells ε U :=
      { toFun := fun q => ⟨q.val.val, (Finset.mem_filter.mp q.property).2⟩
        invFun := fun q => ⟨⟨q.val, q.property.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Set.fintypeCard_eq_ncard, ← Fintype.card_congr he, Fintype.card_coe]
  have hsum : (∑ q : latticeSet ε U,
      (F (physical ε q) - cellAverage ε U F q) ^ 2) ≤
      (latticeSet ε U).ncard * η ^ 2 + b.card * M ^ 2 := by
    calc
      _ ≤ ∑ q : latticeSet ε U, (η ^ 2 + if q ∈ b then M ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : q ∈ b
        · simp only [if_pos hq]
          exact (hboundary q.val (Finset.mem_filter.mp hq).2).trans
            (le_add_of_nonneg_left (sq_nonneg η))
        · simp only [if_neg hq, add_zero]
          apply hinterior q.val q.property
          intro h
          exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Set.fintypeCard_eq_ncard, ← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [l2NormSq, tsum_fintype]
  have hh := mul_le_mul_of_nonneg_left hsum (pow_nonneg hε.le d)
  rw [hcard] at hh
  simpa only [mul_add, mul_assoc] using hh

/-- Sampling a continuous function and averaging its zero extension agree asymptotically. -/
theorem tendsto_sample_sub_cellAverage_of_continuous {R : ℝ} (hR : 0 < R)
    {F : (Fin d → ℝ) → ℝ} (hF : Continuous F) :
    Tendsto (fun ε => l2NormSq ε {x : Fin d → ℝ | radius x < R}
      (fun q => F (physical ε q) - cellAverage ε {x : Fin d → ℝ | radius x < R} F q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  classical
  let U := {x : Fin d → ℝ | radius x < R}
  let K := {x : Fin d → ℝ | radius x ≤ R + 1}
  have hb : Bornology.IsBounded U :=
    (isBounded_radius_le (d := d) R).subset (fun x hx => (show radius x < R from hx).le)
  have hU : MeasurableSet U :=
    (isOpen_lt (radius_continuous d) continuous_const).measurableSet
  have hK : IsCompact K :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_le (radius_continuous d) continuous_const, isBounded_radius_le (R + 1)⟩
  have hUK : U ⊆ K := fun x hx =>
    (show radius x < R from hx).le.trans (le_add_of_nonneg_right zero_le_one)
  have hi : Integrable (U.indicator F) volume :=
    (integrable_indicator_iff hU).mpr
      ((hF.continuousOn.integrableOn_compact hK).mono_set hUK)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hbound (x) (hx : x ∈ K) : |F x| ≤ |M| :=
    (hM x hx).trans (le_abs_self M)
  obtain ⟨C, hC, hc⟩ := ncard_latticeSet_le d (euclideanDiam U)
  have hr : Tendsto (fun ε : ℝ => Real.sqrt d * ε / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hi' : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero, zero_div] using
      ((tendsto_const_nhds (x := Real.sqrt (d : ℝ))).mul hi').div_const (2 : ℝ)
  have hw : Tendsto (fun ε : ℝ =>
      ε ^ d * ((boundaryCells ε U).ncard : ℝ) * (2 * |M|) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_boundaryCells_weight (d := d) hR).mul_const ((2 * |M|) ^ 2)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ha.trans_le (mul_nonneg (pow_nonneg (le_of_lt hε) _)
      (tsum_nonneg (fun _ => sq_nonneg _)))
  · intro b hbpos
    let η := Real.sqrt (b / (C + 1)) / 4
    have hden : 0 < C + 1 := by linarith
    have hη : 0 < η := div_pos (Real.sqrt_pos.mpr (div_pos hbpos hden)) (by norm_num)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous hF.continuousOn) η hη
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds,
      hr.eventually (eventually_lt_nhds hδ),
      hr.eventually (eventually_lt_nhds zero_lt_one),
      hw.eventually (eventually_lt_nhds (show (0 : ℝ) < b / 2 by linarith))]
      with ε hε hε1 hεδ hεsmall hwε
    have hcount : ε ^ d * (latticeSet ε U).ncard ≤ C := by
      have hh := mul_le_mul_of_nonneg_left (hc U hb le_rfl ε ⟨hε, hε1⟩)
        (pow_nonneg (le_of_lt hε) d)
      rw [Real.rpow_neg (le_of_lt hε), Real.rpow_natCast] at hh
      calc
        _ ≤ ε ^ d * (C * (ε ^ d)⁻¹) := hh
        _ = C := by field_simp [ne_of_gt (pow_pos (show 0 < ε from hε) d)]
    have hcell (q : Site d) (hq : q ∈ latticeSet ε U) {y}
        (hy : y ∈ cellCube ε q) : y ∈ K := by
      have hyerr := (abs_le.mp (radius_difference y (physical ε q))).2
      have hyclose := radius_sub_physical_le hε q hy
      have hcenter : radius (physical ε q) < R := hq
      change radius y ≤ R + 1
      linarith
    have hinterior (q : Site d) (hq : q ∈ latticeSet ε U)
        (hqb : q ∉ boundaryCells ε U) :
        (F (physical ε q) - cellAverage ε U F q) ^ 2 ≤ η ^ 2 := by
      have hsub : cellCube ε q ⊆ U := by
        by_contra h
        exact hqb ⟨hq, h⟩
      have he := abs_sample_sub_cellAverage_le hε hi q η (fun y hy => by
        rw [Set.indicator_of_mem (hsub hy)]
        apply le_of_lt
        rw [← Real.dist_eq]
        apply hmod _ (hUK hq) _ (hcell q hq hy)
        rw [dist_comm, dist_eq_norm]
        exact (TaylorHolder.norm_le_radius _).trans_lt
          ((radius_sub_physical_le hε q hy).trans_lt hεδ))
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hη.le).mpr he
    have hboundary (q : Site d) (hq : q ∈ boundaryCells ε U) :
        (F (physical ε q) - cellAverage ε U F q) ^ 2 ≤ (2 * |M|) ^ 2 := by
      have he := abs_sample_sub_cellAverage_le hε hi q (2 * |M|) (fun y _hy => by
        have hcenter := hbound _ (hUK hq.1)
        have hybound : |U.indicator F y| ≤ |M| := by
          by_cases hyU : y ∈ U
          · rw [Set.indicator_of_mem hyU]
            exact hbound y (hUK hyU)
          · rw [Set.indicator_of_notMem hyU, abs_zero]
            exact abs_nonneg M
        exact (abs_sub _ _).trans (by linarith))
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr he
    have hh := (sample_sub_cellAverage_le hε hb η (2 * |M|)
      hinterior hboundary).trans
      (add_le_add (mul_le_mul_of_nonneg_right hcount (sq_nonneg η)) le_rfl)
    apply hh.trans_lt
    have hηsq : η ^ 2 = b / (C + 1) / 16 := by
      dsimp [η]
      rw [div_pow, Real.sq_sqrt (le_of_lt (div_pos hbpos hden))]
      norm_num
    have hquot : (C + 1) * (b / (C + 1)) = b := mul_div_cancel₀ b hden.ne'
    have hquotpos := div_pos hbpos hden
    rw [hηsq]
    nlinarith only [hquot, hquotpos, hwε, hbpos]

/-- Continuity on the closed ball suffices for sampling versus zero-extension averaging. -/
theorem tendsto_sample_sub_cellAverage {R : ℝ} (hR : 0 < R)
    {F : (Fin d → ℝ) → ℝ}
    (hF : ContinuousOn F (closure {x : Fin d → ℝ | radius x < R})) :
    Tendsto (fun ε => l2NormSq ε {x : Fin d → ℝ | radius x < R}
      (fun q => F (physical ε q) - cellAverage ε {x : Fin d → ℝ | radius x < R} F q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let U := {x : Fin d → ℝ | radius x < R}
  let f : C(closure U, ℝ) := ⟨fun x => F x, hF.restrict⟩
  obtain ⟨G, hG⟩ := f.exists_restrict_eq isClosed_closure
  have he (x) (hx : x ∈ U) : G x = F x :=
    congrArg (fun g : C(closure U, ℝ) => g ⟨x, subset_closure hx⟩) hG
  have hU : MeasurableSet U :=
    (isOpen_lt (radius_continuous d) continuous_const).measurableSet
  have hae : (fun x => G x) =ᵐ[volume.restrict U] F :=
    (ae_restrict_mem hU).mono (fun x hx => he x hx)
  have heq (ε : ℝ) : l2NormSq ε U
      (fun q => F (physical ε q) - cellAverage ε U F q) =
      l2NormSq ε U (fun q => G (physical ε q) - cellAverage ε U G q) := by
    unfold l2NormSq
    congr 1
    apply tsum_congr
    intro q
    change (F (physical ε q) - cellAverage ε U F q) ^ 2 =
      (G (physical ε q) - cellAverage ε U G q) ^ 2
    rw [he _ q.property, cellAverage_congr_ae hU hae]
  exact (tendsto_sample_sub_cellAverage_of_continuous hR G.continuous).congr
    (fun ε => (heq ε).symm)

/-- The constant-one sampling error vanishes, including cells cut by the ball boundary. -/
theorem tendsto_one_sub_cellAverage {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε => l2NormSq ε {x : Fin d → ℝ | radius x < R}
      (fun q => 1 - cellAverage ε {x : Fin d → ℝ | radius x < R} (fun _ => 1) q))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  tendsto_sample_sub_cellAverage_of_continuous (d := d)
    (F := fun _ : Fin d → ℝ => (1 : ℝ)) hR continuous_const

end

end LongRange
