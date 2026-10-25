import LongRange.Walk.CellAverageLp
import LongRange.Walk.Rates
import LatticeProb.Prob.JumpChain.KilledGenerator
import LatticeProb.Analysis.ContractionSemigroupResolvent

/-!
# The discrete killed resolvent

The full-rate killed generator agrees with the discrete Dirichlet operator on
zero extensions. The Laplace resolvent is exactly the unique discrete Dirichlet solution.
-/

namespace LongRange

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.JumpChain.BoundedRates LatticeProb.ContractionSemigroup

noncomputable section

variable {d : ℕ}

/-- The killed walk semigroup on the physical-volume weighted discrete space. -/
def discreteKilledSemigroup (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) :
    StronglyContinuousContractionSemigroup (discreteL2 ε U) :=
  (walkRates hd hε hlam a ha).killedSemigroup (walkRate_symm ε a)
    (latticeSet ε U) (latticeSet_finite hε hb) (pow_pos hε d)

/-- Zero extension leaves a supported function unchanged. -/
theorem indicator_eq_of_supportedIn {ε : ℝ} {U : Set (Fin d → ℝ)}
    {u : Site d → ℝ} (hu : SupportedIn ε U u) : (latticeSet ε U).indicator u = u := by
  classical
  funext q
  by_cases hq : q ∈ latticeSet ε U
  · exact Set.indicator_of_mem hq u
  · rw [Set.indicator_of_notMem hq, hu q hq]

/-- The full outgoing killing rate gives exactly the discrete Dirichlet generator. -/
theorem killedGen_eq_generator (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    {u : Site d → ℝ} (hu : SupportedIn ε U u) (q : Site d) :
    (walkRates hd hε hlam a ha).killedGen (latticeSet ε U) u q =
      generator ε a u q := by
  classical
  have hs : Summable (fun y => walkRate ε a q y * u y) := by
    apply summable_of_ne_finset_zero (s := (latticeSet_finite hε hb).toFinset)
    intro y hy
    rw [hu y (fun h => hy ((latticeSet_finite hε hb).mem_toFinset.mpr h)), mul_zero]
  rw [generator_eq_walkRate_tsum]
  simp only [mul_sub]
  have hr : Summable (walkRate ε a q) :=
    (walkRates hd hε hlam a ha).summable q
  rw [hs.tsum_sub (hr.mul_right (u q))]
  rw [tsum_mul_right]
  simp only [killedGen, indicator_eq_of_supportedIn hu, walkRates]

/-- Passing to the discrete equivalence class preserves values at interior atoms. -/
theorem toLp_latticeMeasure_apply {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (f : Site d → ℝ)
    (q : Site d) (hq : q ∈ latticeSet ε U) :
    (memLp_latticeMeasure hε hb f).toLp f q = f q :=
  eq_of_ae_killedMeasure (latticeSet ε U) (pow_pos hε d)
    (memLp_latticeMeasure hε hb f).coeFn_toLp q hq

/-- The killed generator depends only on values inside the killing set. -/
theorem killedGen_congr_on (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} {u v : Site d → ℝ}
    (huv : ∀ q ∈ latticeSet ε U, u q = v q) {q : Site d}
    (hq : q ∈ latticeSet ε U) :
    (walkRates hd hε hlam a ha).killedGen (latticeSet ε U) u q =
      (walkRates hd hε hlam a ha).killedGen (latticeSet ε U) v q := by
  classical
  unfold killedGen
  rw [huv q hq]
  congr 1
  apply tsum_congr
  intro y
  by_cases hy : y ∈ latticeSet ε U
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, huv y hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-- The zero-extended resolvent representative solves the discrete Dirichlet equation. -/
theorem killedResolvent_eq_solution (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) {μ : ℝ} (hμ : 0 < μ)
    (f : Site d → ℝ) :
    let v := resolvent (discreteKilledSemigroup hd hε hlam a ha hb) μ hμ
      ((memLp_latticeMeasure hε hb f).toLp f)
    let u := (latticeSet ε U).indicator (fun q => v q)
    SupportedIn ε U u ∧
      (memLp_latticeMeasure hε hb u).toLp u = v ∧
      ∀ q ∈ latticeSet ε U, μ * u q - generator ε a u q = f q := by
  classical
  dsimp only
  let T : StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (ENNReal.ofReal (ε ^ d) •
        Measure.count.restrict (latticeSet ε U))) :=
    discreteKilledSemigroup hd hε hlam a ha hb
  let F : Lp ℝ 2 (ENNReal.ofReal (ε ^ d) •
      Measure.count.restrict (latticeSet ε U)) :=
    (memLp_latticeMeasure hε hb f).toLp f
  let v := resolvent T μ hμ F
  let u := (latticeSet ε U).indicator (fun q => v q)
  have hu : SupportedIn ε U u := fun q hq => Set.indicator_of_notMem hq _
  have huv : ∀ q ∈ latticeSet ε U, u q = v q :=
    fun q hq => Set.indicator_of_mem hq _
  refine ⟨hu, ?_, ?_⟩
  · apply killedLp_ext (latticeSet ε U) (ε ^ d)
    intro q hq
    exact (toLp_latticeMeasure_apply hε hb u q hq).trans (huv q hq)
  · intro q hq
    have hg := generatorGraph_unique T (resolvent_mem_generatorGraph T hμ F)
      ((walkRates hd hε hlam a ha).mem_generatorGraph_killedSemigroup
        (walkRate_symm ε a) (latticeSet ε U) (latticeSet_finite hε hb)
        (pow_pos hε d) v)
    have he := congrArg (fun w : discreteL2 ε U => w q) hg
    have hsub := eq_of_ae_killedMeasure (latticeSet ε U) (pow_pos hε d)
      (Lp.coeFn_sub (μ • v) F) q hq
    change (μ • v - F) q =
      (walkRates hd hε hlam a ha).killedGenLp
        (latticeSet ε U) (latticeSet_finite hε hb) (ε ^ d) v q at he
    rw [hsub] at he
    change (μ • v) q - F q = _ at he
    have hsmul := eq_of_ae_killedMeasure (latticeSet ε U) (pow_pos hε d)
      (Lp.coeFn_smul μ v) q hq
    rw [hsmul, killedGenLp_apply _ _ _ (pow_pos hε d) v q hq] at he
    change μ * u q - generator ε a u q = f q
    rw [← killedGen_eq_generator hd hε hlam a ha hb hu q,
      killedGen_congr_on hd hε hlam a ha huv hq, huv q hq]
    rw [← he]
    change μ * v q - (μ * v q - F q) = f q
    rw [sub_sub_cancel]
    exact toLp_latticeMeasure_apply hε hb f q hq

/-- Every discrete Dirichlet solution represents the Laplace resolvent. -/
theorem toLp_eq_killedResolvent (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) {μ : ℝ} (hμ : 0 < μ)
    (f u : Site d → ℝ) (hu : SupportedIn ε U u)
    (heq : ∀ q ∈ latticeSet ε U, μ * u q - generator ε a u q = f q) :
    (memLp_latticeMeasure hε hb u).toLp u =
      resolvent (discreteKilledSemigroup hd hε hlam a ha hb) μ hμ
        ((memLp_latticeMeasure hε hb f).toLp f) := by
  let v : Lp ℝ 2 (ENNReal.ofReal (ε ^ d) •
      Measure.count.restrict (latticeSet ε U)) :=
    (memLp_latticeMeasure hε hb u).toLp u
  have hg := (walkRates hd hε hlam a ha).mem_generatorGraph_killedSemigroup
    (walkRate_symm ε a) (latticeSet ε U) (latticeSet_finite hε hb) (pow_pos hε d) v
  let F : Lp ℝ 2 (ENNReal.ofReal (ε ^ d) •
      Measure.count.restrict (latticeSet ε U)) :=
    (memLp_latticeMeasure hε hb f).toLp f
  have hvu : ∀ x ∈ latticeSet ε U, v x = u x :=
    fun x hx => toLp_latticeMeasure_apply hε hb u x hx
  have hfq : ∀ x ∈ latticeSet ε U, F x = f x :=
    fun x hx => toLp_latticeMeasure_apply hε hb f x hx
  have he : μ • v - (walkRates hd hε hlam a ha).killedGenLp
      (latticeSet ε U) (latticeSet_finite hε hb) (ε ^ d) v =
      F := by
    apply killedLp_ext (latticeSet ε U) (ε ^ d)
    intro q hq
    rw [eq_of_ae_killedMeasure (latticeSet ε U) (pow_pos hε d)
      (Lp.coeFn_sub _ _) q hq]
    change (μ • v) q - _ = _
    rw [eq_of_ae_killedMeasure (latticeSet ε U) (pow_pos hε d)
        (Lp.coeFn_smul μ v) q hq,
      killedGenLp_apply _ _ _ (pow_pos hε d) v q hq,
      killedGen_congr_on hd hε hlam a ha
        hvu hq,
      killedGen_eq_generator hd hε hlam a ha hb hu q,
      hfq q hq]
    change μ * v q - generator ε a u q = f q
    rw [hvu q hq]
    exact heq q hq
  exact (he ▸ resolvent_of_mem_generatorGraph
    (discreteKilledSemigroup hd hε hlam a ha hb) hμ hg).symm

/-- The discrete killed resolvent has the sharp inverse-discount norm bound. -/
theorem norm_killedResolvent_le (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) {μ : ℝ} (hμ : 0 < μ) :
    ‖resolvent (discreteKilledSemigroup hd hε hlam a ha hb) μ hμ‖ ≤ μ⁻¹ :=
  norm_resolvent_le _ hμ

end

end LongRange
