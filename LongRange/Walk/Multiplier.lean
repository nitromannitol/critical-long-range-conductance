import LongRange.Walk.CellAverageLp
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded multiplication on continuum and lattice L²

Multipliers act on almost-everywhere classes with their pointwise meaning preserved.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped BoundedContinuousFunction

noncomputable section

variable {d : ℕ}

/-- A bounded measurable scalar function preserves square integrability. -/
theorem memLp_bounded_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (hC : ∀ x, ‖g x‖ ≤ C) (f : Lp ℝ 2 μ) :
    MemLp (fun x => g x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C) (hg.mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun x => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- Multiplication by a bounded measurable scalar function as a continuous linear map. -/
def boundedMulLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (hC : ∀ x, ‖g x‖ ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_bounded_mul hg C hC f).toLp _
      map_add' := fun f h => by
        apply Lp.ext
        filter_upwards [(memLp_bounded_mul hg C hC (f + h)).coeFn_toLp,
          (memLp_bounded_mul hg C hC f).coeFn_toLp,
          (memLp_bounded_mul hg C hC h).coeFn_toLp,
          Lp.coeFn_add f h, Lp.coeFn_add
            ((memLp_bounded_mul hg C hC f).toLp _)
            ((memLp_bounded_mul hg C hC h).toLp _)] with x h₁ h₂ h₃ h₄ h₅
        simp only [h₁, h₅, Pi.add_apply, h₂, h₃, h₄]
        exact mul_add _ _ _
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_bounded_mul hg C hC (c • f)).coeFn_toLp,
          (memLp_bounded_mul hg C hC f).coeFn_toLp,
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_bounded_mul hg C hC f).toLp _)]
          with x h₁ h₂ h₃ h₄
        change _ = (c • (memLp_bounded_mul hg C hC f).toLp _) x
        simp only [h₁, h₄, Pi.smul_apply, h₂, h₃, smul_eq_mul]
        ring } C (by
    intro f
    change ‖(memLp_bounded_mul hg C hC f).toLp _‖ ≤ C * ‖f‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(memLp_bounded_mul hg C hC f).coeFn_toLp] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- The multiplication map has its prescribed pointwise action almost everywhere. -/
theorem boundedMulLp_apply {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (C : ℝ)
    (hC : ∀ x, ‖g x‖ ≤ C) (f : Lp ℝ 2 μ) :
    boundedMulLp μ g hg C hC f =ᵐ[μ] fun x => g x * f x :=
  (memLp_bounded_mul hg C hC f).coeFn_toLp

/-- A nonnegative pointwise multiplier bound bounds the operator norm. -/
theorem norm_boundedMulLp_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (C : ℝ) (hpos : 0 ≤ C)
    (hC : ∀ x, ‖g x‖ ≤ C) : ‖boundedMulLp μ g hg C hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hpos _

/-- Continuum multiplication by a bounded continuous real function. -/
def mulLp (U : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) →ᵇ ℝ) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  boundedMulLp _ φ φ.continuous.aestronglyMeasurable ‖φ‖ φ.norm_coe_le_norm

/-- Continuum multiplication is bounded by the uniform norm. -/
theorem norm_mulLp_le (U : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) →ᵇ ℝ) :
    ‖mulLp U φ‖ ≤ ‖φ‖ :=
  norm_boundedMulLp_le _ _ _ _ (norm_nonneg _) _

/-- Discrete multiplication samples the multiplier at the physical point `εq`. -/
def mulDiscrete (ε : ℝ) (U : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) →ᵇ ℝ) :
    discreteL2 ε U →L[ℝ] discreteL2 ε U :=
  boundedMulLp _ (fun q => φ (physical ε q))
    (measurable_of_countable _).aestronglyMeasurable ‖φ‖
    (fun q => φ.norm_coe_le_norm (physical ε q))

/-- Discrete multiplication is bounded by the same uniform norm at every scale. -/
theorem norm_mulDiscrete_le (ε : ℝ) (U : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →ᵇ ℝ) : ‖mulDiscrete ε U φ‖ ≤ ‖φ‖ :=
  norm_boundedMulLp_le _ _ _ _ (norm_nonneg _) _


/-- Continuum multiplication has the specified pointwise action almost everywhere. -/
theorem mulLp_apply (U : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) →ᵇ ℝ)
    (f : Lp ℝ 2 (volume.restrict U)) :
    mulLp U φ f =ᵐ[volume.restrict U] fun y => φ y * f y :=
  boundedMulLp_apply _ _ _ _ _ f

/-- Discrete multiplication evaluates the multiplier at the physical lattice point. -/
theorem mulDiscrete_apply (ε : ℝ) (U : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) →ᵇ ℝ) (f : discreteL2 ε U) :
    mulDiscrete ε U φ f =ᵐ[latticeMeasure ε U] fun q => φ (physical ε q) * f q :=
  boundedMulLp_apply _ _ _ _ _ f

/-- A cell oscillation bound controls the multiplication error by averaging `|f|`. -/
theorem abs_mul_cellAverage_sub_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U)
    (φ : (Fin d → ℝ) →ᵇ ℝ) (f : Lp ℝ 2 (volume.restrict U))
    (q : Site d) {a : ℝ}
    (hosc : ∀ y ∈ cellCube ε q, y ∈ U → |φ (physical ε q) - φ y| ≤ a) :
    |φ (physical ε q) * cellAverage ε U f q -
      cellAverage ε U (fun y => φ y * f y) q| ≤
      a * cellAverage ε U (fun y => |f y|) q := by
  classical
  have he := (memLp_indicator_iff_restrict hU).mpr (Lp.memLp f)
  have hv : volume (cellCube ε q) ≠ ⊤ := by
    rw [volume_cellCube hε]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict (cellCube ε q)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hv.lt_top⟩
  have hi := (he.restrict (cellCube ε q)).integrable (by norm_num)
  have hp := memLp_bounded_mul φ.continuous.aestronglyMeasurable
    ‖φ‖ φ.norm_coe_le_norm f
  have hj := (((memLp_indicator_iff_restrict hU).mpr hp).restrict
    (cellCube ε q)).integrable (by norm_num)
  have hid : φ (physical ε q) * cellAverage ε U f q -
      cellAverage ε U (fun y => φ y * f y) q =
      (ε ^ d)⁻¹ * ∫ y in cellCube ε q,
        U.indicator (fun y => (φ (physical ε q) - φ y) * f y) y := by
    have heq : U.indicator (fun y => (φ (physical ε q) - φ y) * f y) =
        (fun y => φ (physical ε q) * U.indicator (fun y => f y) y -
          U.indicator (fun y => φ y * f y) y) := by
      funext y
      by_cases hy : y ∈ U <;> simp [hy, sub_mul]
    rw [heq, integral_sub (hi.const_mul _) hj, integral_const_mul]
    simp only [cellAverage]
    ring
  have hnorm : |∫ y in cellCube ε q,
      U.indicator (fun y => (φ (physical ε q) - φ y) * f y) y| ≤
      ∫ y in cellCube ε q, a * U.indicator (fun y => |f y|) y := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae
    · have heq : U.indicator (fun y => (φ (physical ε q) - φ y) * f y) =
          (fun y => φ (physical ε q) * U.indicator (fun y => f y) y -
            U.indicator (fun y => φ y * f y) y) := by
        funext y
        by_cases hy : y ∈ U <;> simp [hy, sub_mul]
      rw [heq]
      exact ((hi.const_mul _).sub hj).norm
    · have heq : U.indicator (fun y => |f y|) =
          (fun y => ‖U.indicator (fun y => f y) y‖) := by
        funext y
        by_cases hy : y ∈ U <;> simp [hy, Real.norm_eq_abs]
      rw [heq]
      exact hi.norm.const_mul a
    · filter_upwards [ae_restrict_mem (measurableSet_cellCube ε q)] with y hy
      by_cases hyU : y ∈ U
      · simp only [Set.indicator_of_mem hyU, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hosc y hy hyU) (abs_nonneg _)
      · simp only [Set.indicator_of_notMem hyU, norm_zero, mul_zero, le_refl]
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hε d))]
  calc
    _ ≤ (ε ^ d)⁻¹ * ∫ y in cellCube ε q, a * U.indicator (fun y => |f y|) y :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (pow_nonneg hε.le d))
    _ = a * cellAverage ε U (fun y => |f y|) q := by
      rw [integral_const_mul, cellAverage]
      ring


/-- The averaging map agrees almost everywhere with the full-cell integral formula. -/
theorem cellAverageLp_coe {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (f : Lp ℝ 2 (volume.restrict U)) :
    cellAverageLp hε hU hb f =ᵐ[latticeMeasure ε U] cellAverage ε U f :=
  (memLp_latticeMeasure hε hb (cellAverage ε U f)).coeFn_toLp

/-- Oscillation on the domain portions of cells bounds the L² commutator. -/
theorem norm_mul_cellAverage_commutator_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (φ : (Fin d → ℝ) →ᵇ ℝ) (f : Lp ℝ 2 (volume.restrict U))
    {a : ℝ} (ha : 0 ≤ a)
    (hosc : ∀ q ∈ latticeSet ε U, ∀ y ∈ cellCube ε q,
      y ∈ U → |φ (physical ε q) - φ y| ≤ a) :
    ‖mulDiscrete ε U φ (cellAverageLp hε hU hb f) -
      cellAverageLp hε hU hb (mulLp U φ f)‖ ≤ a * ‖f‖ := by
  have hfabs : MemLp (fun y => |f y|) 2 (volume.restrict U) := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp f).norm
  let F := hfabs.toLp (fun y => |f y|)
  have hFnorm : ‖F‖ ≤ ‖f‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hfabs.coeFn_toLp] with y hy
    simp only [F, hy, Real.norm_eq_abs, abs_abs, le_refl]
  have hc : ∀ q, cellAverage ε U (mulLp U φ f) q =
      cellAverage ε U (fun y => φ y * f y) q :=
    cellAverage_congr_ae hU (mulLp_apply U φ f)
  have hF : ∀ q, cellAverage ε U F q = cellAverage ε U (fun y => |f y|) q :=
    cellAverage_congr_ae hU hfabs.coeFn_toLp
  have hsites : ∀ᵐ q ∂latticeMeasure ε U, q ∈ latticeSet ε U := by
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (latticeSet_finite hε hb).measurableSet
  have hbound : ‖mulDiscrete ε U φ (cellAverageLp hε hU hb f) -
      cellAverageLp hε hU hb (mulLp U φ f)‖ ≤
      a * ‖cellAverageLp hε hU hb F‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hsites,
      Lp.coeFn_sub (mulDiscrete ε U φ (cellAverageLp hε hU hb f))
        (cellAverageLp hε hU hb (mulLp U φ f)),
      mulDiscrete_apply ε U φ (cellAverageLp hε hU hb f),
      cellAverageLp_coe hε hU hb f,
      cellAverageLp_coe hε hU hb (mulLp U φ f),
      cellAverageLp_coe hε hU hb F] with q hq hsub hmul havg hprod habs
    simp only [hsub, Pi.sub_apply]
    rw [hmul, havg, hprod, habs, hc, hF]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (abs_mul_cellAverage_sub_le hε hU φ f q (hosc q hq)).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) ha)
  exact hbound.trans (mul_le_mul_of_nonneg_left
    ((norm_cellAverageLinearMap_le hε hU hb F).trans hFnorm) ha)

/-- The multiplier commutator vanishes as the positive scale tends to zero.
The scale is indexed by `I = {ε : ℝ // 0 < ε}` with the filter pulled back from
`𝓝[>] 0`; this makes the positivity proof needed by `cellAverageLp` explicit. -/
theorem tendsto_mul_cellAverage_commutator
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (φ : (Fin d → ℝ) →ᵇ ℝ) (f : Lp ℝ 2 (volume.restrict U)) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      ‖mulDiscrete ε U φ (cellAverageLp ε.property hU hb f) -
        cellAverageLp ε.property hU hb (mulLp U φ f)‖)
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) (nhds 0) := by
  have hcont := hb.isCompact_closure.uniformContinuousOn_of_continuous
    φ.continuous.continuousOn
  have hr : Tendsto (fun ε : {ε : ℝ // 0 < ε} => Real.sqrt d * (ε : ℝ) / 2)
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) (nhds 0) := by
    have hi : Tendsto (fun ε : {ε : ℝ // 0 < ε} => (ε : ℝ))
        (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) (nhds 0) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).comp tendsto_comap
    simpa only [mul_zero, zero_div] using
      (tendsto_const_nhds.mul hi).div_const (2 : ℝ)
  apply tendsto_order.mpr
  constructor
  · intro b hbneg
    exact Eventually.of_forall (fun ε => hbneg.trans_le (norm_nonneg _))
  · intro b hbpos
    let a := b / (‖f‖ + 1)
    have ha : 0 < a := div_pos hbpos (by positivity)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hcont a ha
    filter_upwards [hr.eventually (eventually_lt_nhds hδ)] with ε hε
    have hosc : ∀ q ∈ latticeSet (ε : ℝ) U, ∀ y ∈ cellCube (ε : ℝ) q,
        y ∈ U → |φ (physical (ε : ℝ) q) - φ y| ≤ a := by
      intro q hq y hy hyU
      apply le_of_lt
      rw [← Real.dist_eq]
      apply hmod _ (subset_closure hq) _ (subset_closure hyU)
      rw [dist_comm, dist_eq_norm]
      exact (TaylorHolder.norm_le_radius _).trans_lt
        ((radius_sub_physical_le ε.property q hy).trans_lt hε)
    apply (norm_mul_cellAverage_commutator_le ε.property hU hb φ f ha.le hosc).trans_lt
    have hden : 0 < ‖f‖ + 1 := by positivity
    have heq : a * (‖f‖ + 1) = b := by
      dsimp [a]
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith only [heq, ha]

end

end LongRange
