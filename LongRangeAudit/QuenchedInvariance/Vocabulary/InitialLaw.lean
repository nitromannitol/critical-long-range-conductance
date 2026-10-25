import LongRangeAudit.QuenchedInvariance.Vocabulary.CellAverage

/-! # Independent InitialLaw vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LongRange
open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped ENNReal
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

end LongRange
end

end LongRangeAudit.QuenchedInvariance
