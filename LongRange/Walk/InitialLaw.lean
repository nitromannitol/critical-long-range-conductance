import LongRange.Walk.CellAverage
import LongRange.Walk.Increments
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Initial laws from full-cell averages

The half-open cells partition coordinate space. Integrating a probability density on
these cells gives the initial lattice probability measure.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- Full half-open cells cover coordinate space, including their boundary points. -/
theorem iUnion_cellCube_eq_univ {ε : ℝ} (hε : 0 < ε) :
    ⋃ z : Site d, cellCube ε z = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  refine Set.mem_iUnion.mpr ⟨fun i => ⌊y i / ε + 1 / 2⌋, ?_⟩
  intro i
  have hlo := Int.floor_le (y i / ε + 1 / 2)
  have hhi := Int.lt_floor_add_one (y i / ε + 1 / 2)
  have hdiv : y i / ε * ε = y i := div_mul_cancel₀ _ hε.ne'
  have hl := mul_le_mul_of_nonneg_right hlo hε.le
  have hh := mul_lt_mul_of_pos_right hhi hε
  dsimp [physical]
  constructor <;> nlinarith

/-- Compact support turns a square-integrable density into an integrable function. -/
theorem integrable_initial_density {g : (Fin d → ℝ) → ℝ}
    (hg : MemLp g 2 volume) (hgc : HasCompactSupport g) : Integrable g volume := by
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport g)).mp
  exact (hg.locallyIntegrable (by norm_num)).integrableOn_isCompact hgc

/-- The scaled cell average is exactly the integral of the density on the cell. -/
theorem cellMass_eq_integral {ε : ℝ} (hε : 0 < ε)
    (g : (Fin d → ℝ) → ℝ) (z : Site d) :
    ε ^ d * cellAverage ε Set.univ g z = ∫ y in cellCube ε z, g y := by
  rw [cellAverage, Set.indicator_univ, ← mul_assoc,
    mul_inv_cancel₀ (pow_pos hε d).ne', one_mul]

/-- Almost-everywhere nonnegative densities have nonnegative cell masses. -/
theorem cellMass_nonneg {ε : ℝ} (hε : 0 < ε)
    {g : (Fin d → ℝ) → ℝ} (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (z : Site d) :
    0 ≤ ε ^ d * cellAverage ε Set.univ g z := by
  rw [cellMass_eq_integral hε]
  exact integral_nonneg_of_ae (hg0.filter_mono (ae_mono Measure.restrict_le_self))

/-- The extended nonnegative cell mass is the density's Lebesgue integral on that cell. -/
theorem ofReal_cellMass_eq_lintegral {ε : ℝ} (hε : 0 < ε)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (z : Site d) :
    ENNReal.ofReal (ε ^ d * cellAverage ε Set.univ g z) =
      ∫⁻ y in cellCube ε z, ENNReal.ofReal (g y) := by
  rw [cellMass_eq_integral hε]
  exact ofReal_integral_eq_lintegral_ofReal hg.integrableOn
    (hg0.filter_mono (ae_mono Measure.restrict_le_self))

/-- Cell masses sum to one for an integrable probability density. -/
theorem tsum_cellMass_eq_one {ε : ℝ} (hε : 0 < ε)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1) :
    ∑' z : Site d, ENNReal.ofReal (ε ^ d * cellAverage ε Set.univ g z) = 1 := by
  simp_rw [ofReal_cellMass_eq_lintegral hε hg hg0]
  rw [← lintegral_iUnion (measurableSet_cellCube ε) (fun _ _ h => cellCube_disjoint hε h),
    iUnion_cellCube_eq_univ hε, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hg hg0, hg1, ENNReal.ofReal_one]

/-- The initial lattice law is the sum of Dirac masses weighted by full-cell integrals. -/
def initialLaw (ε : ℝ) (g : (Fin d → ℝ) → ℝ) (hε : 0 < ε)
    (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) : ProbabilityMeasure (Site d) :=
  ⟨Measure.sum (fun z => ENNReal.ofReal (ε ^ d * cellAverage ε Set.univ g z) •
    Measure.dirac z),
    (show HasSum (fun z : Site d =>
        ENNReal.ofReal (ε ^ d * cellAverage ε Set.univ g z)) 1 from
      (tsum_cellMass_eq_one hε hg hg0 hg1) ▸
        ENNReal.summable.hasSum).isProbabilityMeasure_sum_dirac_ennreal⟩

/-- Each lattice singleton has the prescribed scaled cell-average mass. -/
theorem initialLaw_singleton (ε : ℝ) (g : (Fin d → ℝ) → ℝ) (hε : 0 < ε)
    (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) (z : Site d) :
    (initialLaw ε g hε hg hg0 hg1 : Measure (Site d)) {z} =
      ENNReal.ofReal (ε ^ d * cellAverage ε Set.univ g z) :=
  Measure.sum_smul_dirac_singleton

/-- Each coordinate point belongs to exactly one full half-open cell. -/
theorem existsUnique_mem_cellCube (ε : ℝ) (hε : 0 < ε) (y : Fin d → ℝ) :
    ∃! z : Site d, y ∈ cellCube ε z := by
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp
    (show y ∈ ⋃ z : Site d, cellCube ε z by rw [iUnion_cellCube_eq_univ hε]; trivial)
  refine ⟨z, hz, ?_⟩
  intro w hw
  by_contra hne
  exact Set.disjoint_left.mp (cellCube_disjoint hε hne) hw hz

/-- The unique site whose half-open cell contains a given coordinate point. -/
def cellIndex (ε : ℝ) (hε : 0 < ε) (y : Fin d → ℝ) : Site d :=
  Classical.choose (Set.mem_iUnion.mp
    (show y ∈ ⋃ z : Site d, cellCube ε z by rw [iUnion_cellCube_eq_univ hε]; trivial))

/-- The selected site contains the original point in its cell. -/
theorem mem_cellCube_cellIndex (ε : ℝ) (hε : 0 < ε) (y : Fin d → ℝ) :
    y ∈ cellCube ε (cellIndex ε hε y) :=
  Classical.choose_spec (Set.mem_iUnion.mp
    (show y ∈ ⋃ z : Site d, cellCube ε z by rw [iUnion_cellCube_eq_univ hε]; trivial))

/-- Fibers of the cell-index map are exactly the full half-open cells. -/
theorem cellIndex_preimage_singleton (ε : ℝ) (hε : 0 < ε) (z : Site d) :
    cellIndex ε hε ⁻¹' {z} = cellCube ε z := by
  ext y
  change cellIndex ε hε y = z ↔ y ∈ cellCube ε z
  constructor
  · intro h
    simpa only [h] using mem_cellCube_cellIndex ε hε y
  · intro hy
    by_contra hne
    exact Set.disjoint_left.mp (cellCube_disjoint hε hne)
      (mem_cellCube_cellIndex ε hε y) hy

/-- The cell-index map is measurable because all its countably many fibers are cells. -/
theorem measurable_cellIndex (ε : ℝ) (hε : 0 < ε) : Measurable (cellIndex (d := d) ε hε) :=
  measurable_to_countable' (fun z => by
    rw [cellIndex_preimage_singleton]
    exact measurableSet_cellCube ε z)

/-- The coordinate density defines a probability measure before Euclidean transport. -/
def initialDensity (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1) :
    ProbabilityMeasure (Fin d → ℝ) :=
  ⟨volume.withDensity (fun y => ENNReal.ofReal (g y)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg hg0, hg1, ENNReal.ofReal_one]⟩⟩

/-- Pushing the density through cell selection produces precisely the atomic initial law. -/
theorem initialLaw_eq_map_cellIndex (ε : ℝ) (g : (Fin d → ℝ) → ℝ) (hε : 0 < ε)
    (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) :
    (initialLaw ε g hε hg hg0 hg1 : Measure (Site d)) =
      Measure.map (cellIndex ε hε) (initialDensity g hg hg0 hg1) := by
  apply Measure.ext_of_singleton
  intro z
  rw [initialLaw_singleton, Measure.map_apply (measurable_cellIndex ε hε)
    (measurableSet_singleton z), cellIndex_preimage_singleton]
  exact (ofReal_cellMass_eq_lintegral hε hg hg0 z).trans
    (withDensity_apply _ (measurableSet_cellCube ε z)).symm

/-- Euclidean transport of the coordinate probability density. -/
def initialDensityEuclidean (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
  (initialDensity g hg hg0 hg1).map
    (PiLp.continuous_toLp (p := (2 : ENNReal)) (fun _ : Fin d => ℝ)).measurable.aemeasurable

/-- Selecting cell centers converges pointwise in the Euclidean metric. -/
theorem tendsto_walkEmbed_cellIndex (y : Fin d → ℝ) :
    Tendsto (fun ε : {ε : ℝ // ε ∈ Set.Ioo (0 : ℝ) 1} =>
      walkEmbed ε.val (cellIndex ε.val ε.property.1 y))
      (Filter.comap Subtype.val (𝓝[Set.Ioo (0 : ℝ) 1] 0))
      (𝓝 (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hi : Tendsto (fun ε : {ε : ℝ // ε ∈ Set.Ioo (0 : ℝ) 1} => ε.val)
      (Filter.comap Subtype.val (𝓝[Set.Ioo (0 : ℝ) 1] 0)) (𝓝 (0 : ℝ)) :=
    (tendsto_comap : Tendsto Subtype.val _ _).mono_right nhdsWithin_le_nhds
  have hb := (tendsto_const_nhds (x := Real.sqrt (d : ℝ))).mul hi |>.div_const 2
  apply squeeze_zero (fun _ => dist_nonneg) _ (by simpa using hb)
  intro ε
  rw [dist_comm, dist_eq_norm, walkEmbed, ← WithLp.toLp_sub, ← radius_norm]
  exact radius_sub_physical_le ε.property.1 _
    (mem_cellCube_cellIndex ε.val ε.property.1 y)

/-- The embedded initial lattice laws converge weakly to the transported density law. -/
theorem tendsto_initialLaw (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1) :
    Tendsto
      (fun ε : {ε : ℝ // ε ∈ Set.Ioo (0 : ℝ) 1} =>
        (initialLaw ε.val g ε.property.1 hg hg0 hg1).map
          (measurable_of_countable (walkEmbed ε.val)).aemeasurable)
      (Filter.comap Subtype.val (𝓝[Set.Ioo (0 : ℝ) 1] 0))
      (𝓝 (initialDensityEuclidean g hg hg0 hg1)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let μ := initialDensity g hg hg0 hg1
  have hm (ε : {ε : ℝ // ε ∈ Set.Ioo (0 : ℝ) 1}) :
      Measurable (fun y : Fin d → ℝ => walkEmbed ε.val (cellIndex ε.val ε.property.1 y)) :=
    (measurable_of_countable (walkEmbed ε.val)).comp
      (measurable_cellIndex ε.val ε.property.1)
  have hc := tendsto_integral_filter_of_dominated_convergence
    (μ := (μ : Measure (Fin d → ℝ))) (fun _ => ‖f‖)
    (Filter.Eventually.of_forall (fun ε =>
      (f.continuous.measurable.comp (hm ε)).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε =>
      Filter.Eventually.of_forall (fun y =>
        f.norm_coe_le_norm (walkEmbed ε.val (cellIndex ε.val ε.property.1 y)))))
    (integrable_const ‖f‖)
    (Filter.Eventually.of_forall (fun y =>
      f.continuous.continuousAt.tendsto.comp (tendsto_walkEmbed_cellIndex y)))
  have he (ε : {ε : ℝ // ε ∈ Set.Ioo (0 : ℝ) 1}) :
      (Measure.map (walkEmbed ε.val)
        (initialLaw ε.val g ε.property.1 hg hg0 hg1)) =
      Measure.map (fun y : Fin d → ℝ =>
        walkEmbed ε.val (cellIndex ε.val ε.property.1 y)) (μ : Measure (Fin d → ℝ)) := by
    rw [initialLaw_eq_map_cellIndex]
    exact Measure.map_map (measurable_of_countable _) (measurable_cellIndex _ _)
  have htest (ε : {ε : ℝ // ε ∈ Set.Ioo (0 : ℝ) 1}) :
      (∫ x, f x ∂((initialLaw ε.val g ε.property.1 hg hg0 hg1).map
        (measurable_of_countable (walkEmbed ε.val)).aemeasurable :
          Measure (EuclideanSpace ℝ (Fin d)))) =
      ∫ y, f (walkEmbed ε.val (cellIndex ε.val ε.property.1 y)) ∂μ := by
    change (∫ x, f x ∂Measure.map (walkEmbed ε.val)
      (initialLaw ε.val g ε.property.1 hg hg0 hg1)) = _
    rw [he ε]
    exact integral_map (hm ε).aemeasurable f.continuous.aestronglyMeasurable
  have hlimit : (∫ x, f x ∂(initialDensityEuclidean g hg hg0 hg1 :
      Measure (EuclideanSpace ℝ (Fin d)))) = ∫ y, f (WithLp.toLp 2 y) ∂μ :=
    integral_map (PiLp.continuous_toLp (p := (2 : ENNReal))
      (fun _ : Fin d => ℝ)).measurable.aemeasurable f.continuous.aestronglyMeasurable
  simpa only [htest, hlimit, Function.comp_apply] using hc

/-- A cell center above a supported point stays inside a fixed Euclidean enlargement. -/
theorem norm_walkEmbed_cellIndex_le {ε R₀ : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    {y : Fin d → ℝ} (hy : radius y < R₀) :
    ‖walkEmbed ε (cellIndex ε hε.1 y)‖ ≤ R₀ + Real.sqrt d := by
  have hc := radius_sub_physical_le hε.1 _ (mem_cellCube_cellIndex ε hε.1 y)
  have ht := (abs_le.mp (radius_difference y
    (physical ε (cellIndex ε hε.1 y)))).1
  have hs := Real.sqrt_nonneg (d : ℝ)
  have hb : Real.sqrt d * ε / 2 ≤ Real.sqrt d := by nlinarith [hε.2]
  change ‖WithLp.toLp 2 (physical ε (cellIndex ε hε.1 y))‖ ≤ _
  rw [← radius_norm]
  linarith

/-- All initial mass lies within the fixed Euclidean enlargement of the density support. -/
theorem initialLaw_ae_norm_le {ε R₀ : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1)
    (hsupp : ∀ y ∈ Function.support g, radius y < R₀) :
    ∀ᵐ z ∂(initialLaw ε g hε.1 hg hg0 hg1 : Measure (Site d)),
      ‖walkEmbed ε z‖ ≤ R₀ + Real.sqrt d := by
  rw [initialLaw_eq_map_cellIndex]
  apply (ae_map_iff (measurable_cellIndex ε hε.1).aemeasurable
    ((Set.to_countable _).measurableSet)).mpr
  change ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (g y)), _
  apply (ae_withDensity_iff' hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mpr
  apply Filter.Eventually.of_forall
  intro y hy
  apply norm_walkEmbed_cellIndex_le hε
  apply hsupp y
  exact fun hzero => hy (by rw [hzero, ENNReal.ofReal_zero])

/-- Compact support gives the physical initial-tail bound used by marginal tightness. -/
theorem initialLaw_tight (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1)
    (hgc : HasCompactSupport g) :
    ∀ η : ℝ, 0 < η → ∃ R : ℝ,
      ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
        (initialLaw ε g hε.1 hg hg0 hg1 : Measure (Site d))
          {z | R < radius (physical ε z)} ≤ ENNReal.ofReal η := by
  obtain ⟨R₀, hR₀⟩ :=
    (hgc.image (PiLp.continuous_toLp (p := (2 : ENNReal))
      (fun _ : Fin d => ℝ))).isBounded.subset_ball
      (0 : EuclideanSpace ℝ (Fin d))
  have hsupp : ∀ y ∈ Function.support g, radius y < R₀ := by
    intro y hy
    have h := hR₀ (Set.mem_image_of_mem (WithLp.toLp 2) (subset_tsupport g hy))
    simpa only [Metric.mem_ball, dist_zero_right, ← radius_norm] using h
  intro η _
  refine ⟨R₀ + Real.sqrt d, ?_⟩
  intro ε hε
  have h := initialLaw_ae_norm_le hε g hg hg0 hg1 hsupp
  have hz : (initialLaw ε g hε.1 hg hg0 hg1 : Measure (Site d))
      {z | R₀ + Real.sqrt d < radius (physical ε z)} = 0 := by
    simpa only [ae_iff, not_le, walkEmbed, ← radius_norm] using h
  rw [hz]
  exact bot_le

/-- Prescribed singleton masses uniquely determine the initial law on the countable lattice. -/
theorem initialLaw_unique (ε : ℝ) (g : (Fin d → ℝ) → ℝ) (hε : 0 < ε)
    (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) (μ : Measure (Site d))
    (hμ : ∀ z, μ {z} = ENNReal.ofReal (ε ^ d * cellAverage ε Set.univ g z)) :
    μ = (initialLaw ε g hε hg hg0 hg1 : Measure (Site d)) := by
  apply Measure.ext_of_singleton
  intro z
  exact (hμ z).trans (initialLaw_singleton ε g hε hg hg0 hg1 z).symm

end

end LongRange
