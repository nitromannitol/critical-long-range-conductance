import LongRange.Corrector.EnergyLowerBound.Weighted
import LongRange.Corrector.Measurable
import LongRange.Corrector.EnergyLowerBound.Counting
import LongRange.Dirichlet.CoefficientBounds
import LongRange.Dirichlet.Hoeffding
import Mathlib.Probability.Moments.Variance

/-!
# The matching corrector energy lower bound

Positive source-edge variance yields a lower bound of order the squared Euclidean slope
radius divided by the critical normalization. The corrector equation, weighted
Cauchy--Schwarz, the exact centered drift second moment, and a lower lattice count prove
the bound for every bounded nonempty open domain, with constants preceding all slopes.
-/

namespace LongRange

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The actual negative-infimum energy has a deterministic upper bound under ellipticity. -/
theorem exists_correctorEnergy_uniform_bound {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (p : Fin d → ℝ) :
    ∃ C : ℝ, ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      0 ≤ correctorEnergy ε U a p ∧ correctorEnergy ε U a p ≤ C := by
  obtain ⟨C, hC⟩ := exists_correctorFunctional_lower_bound hd hε hlam hU p
  refine ⟨C, ?_⟩
  intro a ha
  obtain ⟨φ, ⟨hφ, hmin⟩, _⟩ := existsUnique_correctorMinimizer hd hε hU hlam ha p
  refine ⟨correctorEnergy_nonneg p hφ hmin, ?_⟩
  rw [correctorEnergy_eq_neg_functional p hφ hmin]
  exact neg_le.mpr (hC a ha φ hφ)

/-- Assumption (U) makes the actual corrector energy integrable on every bounded domain. -/
theorem AssumptionU.integrable_correctorEnergy {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (p : Fin d → ℝ) :
    Integrable (fun ω => correctorEnergy ε U (a ω) p) P := by
  haveI := hA.isProbabilityMeasure
  obtain ⟨C, hC⟩ := exists_correctorEnergy_uniform_bound hA.one_le_dim hε hA.lam_pos hU p
  apply Integrable.of_bound
    (measurable_correctorEnergy hA.one_le_dim hε.1 hA.lam_pos hU p
      hA.measurable hA.bounds).aestronglyMeasurable C
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hC (a ω) (hA.bounds ω)).1]
    exact (hC (a ω) (hA.bounds ω)).2

/-- The centered second moment at the source edge is precisely its variance. -/
theorem AssumptionU.variance_baseEdge_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a) :
    Var[fun ω => a ω (baseEdge hA.one_le_dim); P] =
      ∫ ω, (a ω (baseEdge hA.one_le_dim) - meanConductance P hA.one_le_dim a) ^ 2 ∂P := by
  exact variance_eq_integral (hA.measurable _).aemeasurable

namespace Corrector.EnergyLowerBound

variable {d : ℕ}

open Classical

/-- The deterministic physical coefficient of one centered incident conductance. -/
def affineCoeff (ε : ℝ) (p : Fin d → ℝ) (z : Site d) : ℝ :=
  jumpKernel (physical ε z) * linearFn ε p z

/-- The affine coefficients are absolutely summable. -/
theorem summable_affineCoeff (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ) :
    Summable (affineCoeff ε p) := by
  apply ((summable_jumpKernel_firstMoment hd hε).mul_left (∑ i, |p i|)).of_norm_bounded
  intro z
  rw [Real.norm_eq_abs, affineCoeff, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
  calc
    _ ≤ jumpKernel (physical ε z) * ((∑ i, |p i|) * radius (physical ε z)) :=
      mul_le_mul_of_nonneg_left (abs_linearFn_le ε p z) (jumpKernel_nonneg _)
    _ = _ := by ring

/-- Reflection cancels the deterministic affine drift exactly. -/
theorem tsum_affineCoeff_eq_zero (ε : ℝ) (p : Fin d → ℝ) :
    ∑' z, affineCoeff ε p z = 0 := by
  have hneg (z : Site d) : affineCoeff ε p (-z) = -affineCoeff ε p z := by
    have hlinear : linearFn ε p (-z) = -linearFn ε p z := by
      simp only [linearFn, physical, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]
    rw [affineCoeff, physical_neg, jumpKernel_neg, hlinear, mul_neg]
    rfl
  have he := (Equiv.neg (Site d)).tsum_eq (affineCoeff ε p)
  simp only [Equiv.neg_apply, hneg, tsum_neg] at he
  linarith

/-- The centered incident conductance, with a genuine zero diagonal. -/
def centeredIncident (m : ℝ) (a : Edge d → ℝ) (q z : Site d) : ℝ :=
  if hz : z = 0 then 0 else a (edgeAdd q z hz) - m

/-- Subtracting any constant mean leaves the physical affine drift unchanged. -/
theorem affineDrift_eq_centered (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (m : ℝ) (p : Fin d → ℝ) (q : Site d) :
    affineDrift ε a p q = ∑' z, affineCoeff ε p z * centeredIncident m a q z := by
  have heq (z : Site d) : affineCoeff ε p z * centeredIncident m a q z =
      rowWeight ε a q z * linearFn ε p z - m * affineCoeff ε p z := by
    by_cases hz : z = 0
    · simp only [hz, centeredIncident, rowWeight, ↓reduceDIte, affineCoeff,
        (physical_eq_zero_iff hε 0).mpr rfl, jumpKernel_zero, zero_mul, mul_zero, sub_zero]
    · simp only [hz, centeredIncident, rowWeight, ↓reduceDIte, affineCoeff]
      ring
  simp_rw [heq]
  rw [(summable_affineDrift hd hε hlam ha p q).tsum_sub
    ((summable_affineCoeff hd hε p).mul_left m), tsum_mul_left,
    tsum_affineCoeff_eq_zero, mul_zero, sub_zero]
  rfl

/-- Distinct nonzero increments at one site index distinct unordered edges. -/
theorem edgeAdd_injective_at (q : Site d) {z w : Site d} (hz : z ≠ 0) (hw : w ≠ 0)
    (he : edgeAdd q z hz = edgeAdd q w hw) : z = w := by
  have he' : s(q, q + z) = s(q, q + w) := congrArg Subtype.val he
  rcases Sym2.eq_iff.mp he' with ⟨_, h⟩ | ⟨h, _⟩
  · exact add_left_cancel h
  · exact (hw (by simpa using h.symm)).elim

/-- The physical drift has the exact diagonal second moment under Assumption (U). -/
theorem integral_affineDrift_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ) (q : Site d) :
    ∫ ω, affineDrift ε (a ω) p q ^ 2 ∂P =
      Var[fun ω => a ω (baseEdge hA.one_le_dim); P] * ∑' z, affineCoeff ε p z ^ 2 := by
  haveI := hA.isProbabilityMeasure
  have hlam := hA.lam_pos
  let m := meanConductance P hA.one_le_dim a
  let X : Site d → Ω → ℝ := fun z ω => centeredIncident m (a ω) q z
  have hm (z : Site d) : Measurable (X z) := by
    dsimp only [X, centeredIncident]
    split
    · exact measurable_const
    · exact (hA.measurable _).sub measurable_const
  have hb (z : Site d) (ω : Ω) : |X z ω| ≤ 2 * lam⁻¹ := by
    dsimp only [X, centeredIncident]
    split
    · simp only [abs_zero]
      positivity
    · have ha := hA.bounds ω (edgeAdd q z ‹z ≠ 0›)
      have hmean : lam ≤ m ∧ m ≤ lam⁻¹ := hA.mean_mem_Icc
      rw [abs_le]
      constructor <;> linarith [inv_pos.mpr hA.lam_pos]
  have hc (z : Site d) : ∫ ω, X z ω ∂P = 0 := by
    dsimp only [X, centeredIncident]
    split
    · exact integral_zero _ _
    · rw [integral_sub (hA.integrable _) (integrable_const m), hA.integral_eq_mean]
      simp only [integral_const, probReal_univ, one_smul, m, sub_self]
  have horth (z w : Site d) (hzw : z ≠ w) : ∫ ω, X z ω * X w ω ∂P = 0 := by
    by_cases hz : z = 0
    · simp only [hz, X, centeredIncident, ↓reduceDIte, zero_mul, integral_zero]
    by_cases hw : w = 0
    · simp only [hw, X, centeredIncident, ↓reduceDIte, mul_zero, integral_zero]
    have he : edgeAdd q z hz ≠ edgeAdd q w hw :=
      fun h => hzw (edgeAdd_injective_at q hz hw h)
    have hi := (hA.iIndep.indepFun he).comp
      (show Measurable (fun x : ℝ => x - m) from measurable_id.sub_const _)
      (show Measurable (fun x : ℝ => x - m) from measurable_id.sub_const _)
    have hi' : IndepFun (X z) (X w) P := by
      simpa only [X, centeredIncident, hz, hw, ↓reduceDIte, Function.comp_def] using hi
    rw [hi'.integral_fun_mul_eq_mul_integral (hm z).aestronglyMeasurable
      (hm w).aestronglyMeasurable, hc z, zero_mul]
  simp_rw [affineDrift_eq_centered hA.one_le_dim hε hA.lam_pos (hA.bounds _) m p q]
  rw [LatticeProb.integral_sq_tsum (summable_affineCoeff hA.one_le_dim hε p) hm
    (by positivity : 0 ≤ 2 * lam⁻¹) hb horth, ← tsum_mul_left]
  apply tsum_congr
  intro z
  by_cases hz : z = 0
  · simp only [hz, affineCoeff, (physical_eq_zero_iff hε 0).mpr rfl, jumpKernel_zero,
      zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · have hv : ∫ ω, X z ω ^ 2 ∂P =
        Var[fun ω => a ω (baseEdge hA.one_le_dim); P] := by
      rw [hA.variance_baseEdge_eq]
      dsimp only [X, centeredIncident]
      simp only [hz, ↓reduceDIte]
      exact ((hA.identDistrib (edgeAdd q z hz) (baseEdge hA.one_le_dim)).comp
        (show Measurable (fun x : ℝ => (x - m) ^ 2) by fun_prop)).integral_eq
    rw [hv, mul_comm]

/-- The physical affine drift has an integrable square under Assumption (U). -/
theorem integrable_affineDrift_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ) (q : Site d) :
    Integrable (fun ω => affineDrift ε (a ω) p q ^ 2) P := by
  haveI := hA.isProbabilityMeasure
  have hm : Measurable (fun ω => affineDrift ε (a ω) p q) := by
    apply Measurable.tsum
    intro z
    unfold rowWeight
    split
    · exact measurable_const
    · exact ((hA.measurable _).mul_const _).mul_const _
  let M := lam⁻¹ * ∑' z, |affineCoeff ε p z|
  have hM : 0 ≤ M := mul_nonneg (inv_nonneg.mpr hA.lam_pos.le)
    (tsum_nonneg (fun z => abs_nonneg _))
  apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (M ^ 2)
  apply ae_of_all
  intro ω
  have hb : |affineDrift ε (a ω) p q| ≤ M := by
    have hs := summable_affineDrift hA.one_le_dim hε hA.lam_pos (hA.bounds ω) p q
    calc
      _ ≤ ∑' z, |rowWeight ε (a ω) q z * linearFn ε p z| := norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' z, lam⁻¹ * |affineCoeff ε p z| := by
        apply hs.abs.tsum_le_tsum _ ((summable_affineCoeff hA.one_le_dim hε p).abs.mul_left _)
        intro z
        unfold rowWeight
        split
        · simp only [zero_mul, abs_zero]
          exact mul_nonneg (inv_nonneg.mpr hA.lam_pos.le) (abs_nonneg _)
        · rw [abs_mul, abs_mul,
            abs_of_nonneg (hA.lam_pos.le.trans (hA.bounds ω _).1),
            abs_of_nonneg (jumpKernel_nonneg _)]
          simpa only [affineCoeff, abs_mul, abs_of_nonneg (jumpKernel_nonneg _), mul_assoc]
            using mul_le_mul_of_nonneg_right (hA.bounds ω _).2
              (mul_nonneg (jumpKernel_nonneg _) (abs_nonneg (linearFn ε p z)))
      _ = M := tsum_mul_left
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) hM).mpr hb

/-- A positive coordinate step has the exact physical affine coefficient. -/
theorem affineCoeff_unit {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ) (i : Fin d) :
    affineCoeff ε p (unit i) = p i / ε ^ (d + 1) := by
  have hn := (physical_eq_zero_iff hε (unit i)).not.mpr (unit_ne_zero i)
  have hr := Dirichlet.radius_physical_unit_orientation hε.le (unit i) i (Or.inl rfl)
  have hl : linearFn ε p (unit i) = ε * p i := by
    simp [linearFn, physical, unit, Pi.single_apply, mul_comm]
  rw [affineCoeff, jumpKernel_of_ne_zero hn, hr, hl,
    show d + 2 = (d + 1) + 1 by omega, pow_succ]
  field_simp

/-- Retaining positive nearest-neighbour increments gives a Euclidean slope lower bound. -/
theorem affineCoeff_sq_tsum_ge (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ) :
    radius p ^ 2 / ε ^ (2 * d + 2) ≤ ∑' z, affineCoeff ε p z ^ 2 := by
  classical
  have hu : Function.Injective (unit : Fin d → Site d) := by
    intro i j hij
    by_contra hn
    have hi := congrFun hij i
    simp only [unit, Pi.single_eq_same, Pi.single_eq_of_ne hn] at hi
    norm_num at hi
  have hs := summable_sq_of_summable_real (summable_affineCoeff hd hε p)
  have hb := hs.sum_le_tsum (Finset.univ.image unit) (fun z _ => sq_nonneg _)
  rw [Finset.sum_image (fun i _ j _ h => hu h)] at hb
  simp_rw [affineCoeff_unit hε p, div_pow] at hb
  rw [← Finset.sum_div, ← radius_sq] at hb
  have he : (ε ^ (d + 1)) ^ 2 = ε ^ (2 * d + 2) := by
    rw [← pow_mul]
    congr 1
    omega
  rwa [he] at hb

/-- Physical scaling gives the total jump-kernel mass exactly. -/
theorem tsum_jumpKernel_physical {ε : ℝ} (hε : 0 < ε) :
    ∑' z : Site d, jumpKernel (physical ε z) =
      (ε ^ (d + 2))⁻¹ * ∑' z : Site d, jumpKernel (physical 1 z) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  by_cases hz : z = 0
  · simp only [hz, (physical_eq_zero_iff hε 0).mpr rfl,
      (physical_eq_zero_iff zero_lt_one 0).mpr rfl, jumpKernel_zero, mul_zero]
  · rw [jumpKernel_physical hε hz,
      jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one z).not.mpr hz)]

/-- Averaging the deterministic drift estimate gives the explicit lower bound per lattice site. -/
theorem integral_correctorEnergy_ge_card {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (p : Fin d → ℝ) :
    ε ^ d * ((latticeSet ε U).ncard : ℝ) *
        Var[fun ω => a ω (baseEdge hA.one_le_dim); P] * radius p ^ 2 /
        (2 * kappa d ε * (lam⁻¹ * ∑' z : Site d, jumpKernel (physical 1 z))) ≤
      ∫ ω, correctorEnergy ε U (a ω) p ∂P := by
  haveI := hA.isProbabilityMeasure
  let K := lam⁻¹ * ∑' z : Site d, jumpKernel (physical 1 z)
  have hK : 0 < K := mul_pos (inv_pos.mpr hA.lam_pos) (unitKernel_tsum_pos hA.one_le_dim)
  let R := K / ε ^ (d + 2)
  have hR : 0 < R := div_pos hK (pow_pos hε.1 _)
  let N := ε ^ (2 * d) / (2 * kappa d ε * R)
  have hkap := kappa_pos hA.one_le_dim hε
  have hN : 0 ≤ N := div_nonneg (pow_nonneg hε.1.le _)
    (mul_nonneg (mul_nonneg (by norm_num) hkap.le) hR.le)
  let s := (latticeSet_finite hε.1 hU).toFinset
  have hs (q : Site d) : q ∈ s ↔ q ∈ latticeSet ε U := Set.Finite.mem_toFinset _
  have hsCard : (s.card : ℝ) = ((latticeSet ε U).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ (latticeSet_finite hε.1 hU)]
  have hrow (ω : Ω) (q : Site d) : ∑' z, rowWeight ε (a ω) q z ≤ R := by
    have hb := (rowWeight_summable_bound hA.one_le_dim hε.1 hA.lam_pos (hA.bounds ω) q).2
    rw [tsum_jumpKernel_physical hε.1] at hb
    exact hb.trans_eq (by dsimp only [R, K]; ring)
  have hpoint (ω : Ω) : N * ∑ q ∈ s, affineDrift ε (a ω) p q ^ 2 ≤
      correctorEnergy ε U (a ω) p :=
    correctorEnergy_ge_affineDrift hA.one_le_dim hε hA.lam_pos hU (hA.bounds ω) p s
      (fun q hq => (hs q).mp hq) hR (hrow ω)
  have hint : Integrable (fun ω => ∑ q ∈ s, affineDrift ε (a ω) p q ^ 2) P :=
    integrable_finsetSum s (fun q _ => integrable_affineDrift_sq hA hε.1 p q)
  have hb := integral_mono (hint.const_mul N) (hA.integrable_correctorEnergy hε hU p) hpoint
  rw [integral_const_mul, integral_finsetSum s
    (fun q _ => integrable_affineDrift_sq hA hε.1 p q)] at hb
  have hvariance := variance_nonneg (fun ω => a ω (baseEdge hA.one_le_dim)) P
  have hsum : (s.card : ℝ) *
      (Var[fun ω => a ω (baseEdge hA.one_le_dim); P] *
        (radius p ^ 2 / ε ^ (2 * d + 2))) ≤
      ∑ q ∈ s, ∫ ω, affineDrift ε (a ω) p q ^ 2 ∂P := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro q _
    rw [integral_affineDrift_sq hA hε.1 p q]
    exact mul_le_mul_of_nonneg_left (affineCoeff_sq_tsum_ge hA.one_le_dim hε.1 p) hvariance
  have hbound := (mul_le_mul_of_nonneg_left hsum hN).trans hb
  have heq : N * ((s.card : ℝ) *
      (Var[fun ω => a ω (baseEdge hA.one_le_dim); P] *
        (radius p ^ 2 / ε ^ (2 * d + 2)))) =
      ε ^ d * ((latticeSet ε U).ncard : ℝ) *
        Var[fun ω => a ω (baseEdge hA.one_le_dim); P] * radius p ^ 2 /
          (2 * kappa d ε * K) := by
    rw [hsCard]
    dsimp only [N, R]
    rw [pow_add, pow_add]
    field_simp [hε.1.ne', hK.ne', hkap.ne']
  rw [heq] at hbound
  exact hbound

end Corrector.EnergyLowerBound

/-- The matching lower bound of Remark `rem:nu-lower-bound`, for the actual corrector
energy and Euclidean slope radius. The constants are chosen before every slope and scale. -/
theorem AssumptionU.exists_correctorEnergy_lower_bound {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ}
    (hA : AssumptionU P lam a) {U : Set (Fin d → ℝ)} (hUo : IsOpen U)
    (hUne : U.Nonempty) (hU : Bornology.IsBounded U)
    (hvar : 0 < Var[fun ω => a ω (baseEdge hA.one_le_dim); P]) :
    ∃ c > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ p : Fin d → ℝ, ∀ ε : ℝ,
      0 < ε → ε < min 1 ε₀ →
        c * radius p ^ 2 / kappa d ε ≤ ∫ ω, correctorEnergy ε U (a ω) p ∂P := by
  obtain ⟨b, hb, ε₀, hε₀, hcount⟩ :=
    Corrector.EnergyLowerBound.exists_lattice_count_lower hUo hUne hU
  let K := lam⁻¹ * ∑' z : Site d, jumpKernel (physical 1 z)
  have hK : 0 < K := mul_pos (inv_pos.mpr hA.lam_pos) (unitKernel_tsum_pos hA.one_le_dim)
  let v := Var[fun ω => a ω (baseEdge hA.one_le_dim); P]
  refine ⟨b * v / (2 * K), div_pos (mul_pos hb hvar) (mul_pos (by norm_num) hK),
    ε₀, hε₀, ?_⟩
  intro p ε hε hsmall
  have hε' : ε ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε, lt_of_lt_of_le hsmall (min_le_left _ _)⟩
  have hc := hcount ε hε (lt_of_lt_of_le hsmall (min_le_right _ _))
  have hkap := kappa_pos hA.one_le_dim hε'
  have hf : 0 ≤ v * radius p ^ 2 / (2 * kappa d ε * K) :=
    div_nonneg (mul_nonneg hvar.le (sq_nonneg _)) (by positivity)
  have hm := mul_le_mul_of_nonneg_right hc hf
  calc
    _ = b * (v * radius p ^ 2 / (2 * kappa d ε * K)) := by ring
    _ ≤ _ := hm
    _ = ε ^ d * ((latticeSet ε U).ncard : ℝ) * v * radius p ^ 2 /
        (2 * kappa d ε * K) := by ring
    _ ≤ _ := Corrector.EnergyLowerBound.integral_correctorEnergy_ge_card hA hε' hU p


end

end LongRange
