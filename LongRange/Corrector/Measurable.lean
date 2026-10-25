import LongRange.Calculus.BilinForm
import LongRange.Appendix.LatticeCount
import LongRange.Appendix.Kappa
import LongRange.Model.CorrectorEnergy
import LongRange.Corrector.Support
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Measurability of the corrector functional and energy

The series defining the corrector functional converges absolutely on finite supports.
Pointwise measurable conductances and test functions give measurable energies, with the
physical affine increment and the Euclidean jump kernel of the model. A countable dense
set in the finite coordinate space computes the energy infimum. Uniform ellipticity also
gives a lower bound independent of the conductance configuration.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

open Classical

variable {d : ℕ}

/-- The unrestricted square difference splits into quadratic and affine bilinear terms. -/
private theorem square_difference (A x y b : ℝ) :
    b * ((A + x - y) ^ 2 - A ^ 2) =
      b * (x - y) * (x - y) + 2 * (b * A * (x - y)) := by
  ring

/-- Absolute convergence of the corrector functional at every finitely supported field,
even when its support is not contained in the domain. -/
theorem summable_correctorFunctional_of_hasFiniteSupport (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {U : Set (Fin d → ℝ)}
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (p : Fin d → ℝ) {w : Site d → ℝ} (hw : Function.HasFiniteSupport w) :
    Summable (fun q : Site d × Site d =>
      if hz : q.2 = 0 then 0
      else if q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U then
        a (edgeAdd q.1 q.2 hz) * jumpKernel (physical ε q.2) *
          ((linearFn ε p q.2 + w (q.1 + q.2) - w q.1) ^ 2 -
            linearFn ε p q.2 ^ 2)
      else 0) := by
  classical
  have hquad := summable_bilinForm hd hε hlam ha hw hw
  have hlin := summable_bilinForm_affine hd hε hlam ha p
    (φ := 0) ⟨0, le_rfl, fun _ => by simp only [Pi.zero_apply, abs_zero, le_refl]⟩ hw
  simp only [Pi.zero_apply, add_zero, linearFn_add, add_sub_cancel_left] at hlin
  have hs := hquad.add (hlin.mul_left 2)
  refine hs.norm.of_norm_bounded (fun q => ?_)
  by_cases hz : q.2 = 0
  · simp only [hz, ↓reduceDIte, mul_zero, add_zero, norm_zero, le_refl]
  · simp only [hz, ↓reduceDIte]
    split_ifs
    · exact le_of_eq (congrArg norm (square_difference _ _ _ _))
    · simp only [norm_zero]
      exact norm_nonneg _

/-- A measurable random conductance and pointwise measurable random test field give a
measurable corrector functional. Absolute convergence on finite supports is proved separately
in `summable_correctorFunctional_of_hasFiniteSupport`. -/
theorem measurable_correctorFunctional {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (U : Set (Fin d → ℝ)) (p : Fin d → ℝ)
    {a : Ω → Edge d → ℝ} (ha : ∀ e, Measurable (fun ω => a ω e))
    {w : Ω → Site d → ℝ} (hw : ∀ q, Measurable (fun ω => w ω q)) :
    Measurable (fun ω => correctorFunctional ε U (a ω) p (w ω)) := by
  classical
  apply Measurable.const_mul
  apply Measurable.tsum
  intro q
  by_cases hz : q.2 = 0
  · simp only [hz, ↓reduceDIte]
    exact measurable_const
  · simp only [hz, ↓reduceDIte]
    split_ifs
    · exact ((ha _).mul_const _).mul
        (((measurable_const.add (hw _)).sub (hw _)).pow_const 2 |>.sub measurable_const)
    · exact measurable_const

/-- Pointwise measurable fields have a measurable critical seminorm. -/
theorem measurable_h1CritSq {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    {φ : Ω → Site d → ℝ} (hφ : ∀ q, Measurable (fun ω => φ ω q)) :
    Measurable (fun ω => h1CritSq ε (φ ω)) := by
  unfold h1CritSq
  apply Measurable.const_mul
  exact Measurable.tsum (fun q => (((hφ _).sub (hφ _)).pow_const 2).const_mul _)

/-- Pointwise measurable conductances and fields give a measurable bilinear energy. -/
theorem measurable_bilinForm {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    {a : Ω → Edge d → ℝ} (ha : ∀ e, Measurable (fun ω => a ω e))
    {φ ψ : Ω → Site d → ℝ}
    (hφ : ∀ q, Measurable (fun ω => φ ω q))
    (hψ : ∀ q, Measurable (fun ω => ψ ω q)) :
    Measurable (fun ω => bilinForm ε (a ω) (φ ω) (ψ ω)) := by
  unfold bilinForm
  apply Measurable.const_mul
  apply Measurable.tsum
  intro q
  by_cases hz : q.2 = 0
  · simp only [hz, ↓reduceDIte]
    exact measurable_const
  · simp only [hz, ↓reduceDIte]
    exact (((ha _).mul_const _).mul ((hφ _).sub (hφ _))).mul ((hψ _).sub (hψ _))

/-- On admissible fields the domain restriction drops out, and expansion of the square
identifies the functional with its quadratic and physical affine parts. -/
theorem correctorFunctional_eq_bilinForm (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {U : Set (Fin d → ℝ)}
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (p : Fin d → ℝ) {w : Site d → ℝ} (hw : Function.HasFiniteSupport w)
    (hU : SupportedIn ε U w) :
    correctorFunctional ε U a p w = bilinForm ε a w w +
      2 * bilinForm ε a (linearFn ε p) w := by
  classical
  have hquad := summable_bilinForm hd hε hlam ha hw hw
  have hlin := summable_bilinForm_affine hd hε hlam ha p
    (φ := 0) ⟨0, le_rfl, fun _ => by simp only [Pi.zero_apply, abs_zero, le_refl]⟩ hw
  simp only [Pi.zero_apply, add_zero, linearFn_add, add_sub_cancel_left] at hlin
  unfold correctorFunctional bilinForm
  have heq : (fun q : Site d × Site d =>
      if hz : q.2 = 0 then 0
      else if q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U then
        a (edgeAdd q.1 q.2 hz) * jumpKernel (physical ε q.2) *
          ((linearFn ε p q.2 + w (q.1 + q.2) - w q.1) ^ 2 -
            linearFn ε p q.2 ^ 2)
      else 0) = (fun q =>
        (if hz : q.2 = 0 then 0 else a (edgeAdd q.1 q.2 hz) *
          jumpKernel (physical ε q.2) * (w (q.1 + q.2) - w q.1) *
            (w (q.1 + q.2) - w q.1)) +
        2 * (if hz : q.2 = 0 then 0 else a (edgeAdd q.1 q.2 hz) *
          jumpKernel (physical ε q.2) * linearFn ε p q.2 *
            (w (q.1 + q.2) - w q.1))) := by
    funext q
    by_cases hz : q.2 = 0
    · simp only [hz, ↓reduceDIte, mul_zero, add_zero]
    · simp only [hz, ↓reduceDIte]
      split_ifs with hmem
      · exact square_difference _ _ _ _
      · have hx := hU q.1 (fun h => hmem (Or.inl h))
        have hy := hU (q.1 + q.2) (fun h => hmem (Or.inr h))
        simp only [hx, hy, sub_self, mul_zero, add_zero]
  rw [heq, Summable.tsum_add hquad (hlin.mul_left 2), tsum_mul_left]
  simp_rw [linearFn_add, add_sub_cancel_left]
  ring

/-- Extension by zero from a finite set, as a linear map. -/
private def finiteField (s : Finset (Site d)) : (s → ℝ) →ₗ[ℝ] (Site d → ℝ) where
  toFun v q := if h : q ∈ s then v ⟨q, h⟩ else 0
  map_add' v w := by
    funext q
    by_cases h : q ∈ s <;> simp [h]
  map_smul' c v := by
    funext q
    by_cases h : q ∈ s <;> simp [h]

/-- An extended field vanishes outside its finite index set. -/
private theorem finiteField_finite (s : Finset (Site d)) (v : s → ℝ) :
    Function.HasFiniteSupport (finiteField s v) := by
  apply s.finite_toSet.subset
  intro q hq
  by_contra h
  have hqs : q ∉ s := h
  exact hq (by simp only [finiteField, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hqs])

/-- The bilinear energy on the finite coordinate space. -/
private def finiteBilin (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (s : Finset (Site d)) : (s → ℝ) →ₗ[ℝ] (s → ℝ) →ₗ[ℝ] ℝ where
  toFun v :=
    { toFun := fun w => bilinForm ε a (finiteField s v) (finiteField s w)
      map_add' := fun w z => by
        rw [map_add]
        exact bilinForm_add_right hd hε hlam ha (finiteField_finite s v)
          (finiteField_finite s w) (finiteField_finite s z)
      map_smul' := fun c w => by
        rw [map_smul]
        exact bilinForm_smul_right ε a c _ _ }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    change bilinForm ε a (finiteField s (v + w)) (finiteField s z) = _
    rw [map_add]
    exact bilinForm_add_left hd hε hlam ha (finiteField_finite s v)
      (finiteField_finite s w) (finiteField_finite s z)
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    change bilinForm ε a (finiteField s (c • v)) (finiteField s w) = _
    rw [map_smul]
    exact bilinForm_smul_left ε a c _ _

/-- A physical affine factor paired with finitely many coordinates is a linear functional. -/
private def finiteLinear (ε : ℝ) (a : Edge d → ℝ)
    (p : Fin d → ℝ) (s : Finset (Site d)) : (s → ℝ) →ₗ[ℝ] ℝ where
  toFun v := -(ε ^ d * ∑ q ∈ s, finiteField s v q * generator ε a (linearFn ε p) q)
  map_add' v w := by
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add, neg_add_rev]
    ring
  map_smul' c v := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      ← Finset.mul_sum]
    ring

/-- Green's identity expresses the affine term as a finite linear functional. -/
private theorem finiteLinear_eq (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    (s : Finset (Site d)) (v : s → ℝ) :
    finiteLinear ε a p s v =
      bilinForm ε a (linearFn ε p) (finiteField s v) := by
  have hg := bilinForm_eq_neg_generator_affine hd hε hlam ha p
    (φ := 0) ⟨0, le_rfl, fun _ => by simp only [Pi.zero_apply, abs_zero, le_refl]⟩
    (finiteField_finite s v)
  simp only [Pi.zero_apply, add_zero] at hg
  change -(ε ^ d * ∑ q ∈ s, finiteField s v q * generator ε a (linearFn ε p) q) = _
  rw [hg]
  congr 2
  exact (tsum_eq_sum (s := s) (fun q hq => by
    simp only [finiteField, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hq, zero_mul])).symm

/-- Continuity of the corrector functional on its finite coordinate space. -/
private theorem continuous_finiteFunctional (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {U : Set (Fin d → ℝ)}
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (p : Fin d → ℝ) (s : Finset (Site d)) (hs : (s : Set (Site d)) = latticeSet ε U) :
    Continuous (fun v : s → ℝ => correctorFunctional ε U a p (finiteField s v)) := by
  have heq (v : s → ℝ) := correctorFunctional_eq_bilinForm hd hε hlam ha p
    (finiteField_finite s v) (show SupportedIn ε U (finiteField s v) from by
      intro q hq
      have hqs : q ∉ s := by simpa only [← hs, Finset.mem_coe] using hq
      simp only [finiteField, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hqs])
  simp_rw [heq, ← finiteLinear_eq hd hε hlam ha p s]
  exact ((IsModuleTopology.continuous_bilinear_of_finite_left
    (finiteBilin hd hε hlam ha s)).comp (continuous_id.prodMk continuous_id)).add
    ((finiteLinear ε a p s).continuous_of_finiteDimensional.const_mul 2)

/-- The corrector energy is measurable for pointwise measurable, uniformly elliptic
conductances on a bounded domain. -/
theorem measurable_correctorEnergy {Ω : Type*} [MeasurableSpace Ω]
    (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (p : Fin d → ℝ)
    {a : Ω → Edge d → ℝ} (ha : ∀ e, Measurable (fun ω => a ω e))
    (hb : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹) :
    Measurable (fun ω => correctorEnergy ε U (a ω) p) := by
  classical
  let s := (latticeSet_finite hε hU).toFinset
  have hs : (s : Set (Site d)) = latticeSet ε U := Set.Finite.coe_toFinset _
  clear_value s
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense (s → ℝ)
  have hrange (ω : Ω) :
      Set.range (fun w : {w : Site d → ℝ // SupportedIn ε U w} =>
        correctorFunctional ε U (a ω) p w) =
      Set.range (fun v : s → ℝ => correctorFunctional ε U (a ω) p (finiteField s v)) := by
    ext r
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨fun q => w.val q, ?_⟩
      have hw_eq : finiteField s (fun q => w.val q) = w.val := by
        funext q
        by_cases hq : q ∈ s
        · simp only [finiteField, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hq]
        · have hqU : q ∉ latticeSet ε U := by
            simpa only [← hs, Finset.mem_coe] using hq
          simp only [finiteField, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hq,
            w.property q hqU]
      exact congrArg (correctorFunctional ε U (a ω) p) hw_eq
    · rintro ⟨v, rfl⟩
      refine ⟨⟨finiteField s v, ?_⟩, rfl⟩
      intro q hq
      have hqs : q ∉ s := by simpa only [← hs, Finset.mem_coe] using hq
      simp only [finiteField, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hqs]
  have heq (ω : Ω) : correctorEnergy ε U (a ω) p =
      -(⨅ v : D, correctorFunctional ε U (a ω) p (finiteField s v.val)) := by
    unfold correctorEnergy
    rw [hrange, sInf_range]
    exact congrArg Neg.neg (hdense.ciInf'
      (continuous_finiteFunctional hd hε hlam (hb ω) p s hs)).symm
  simp_rw [heq]
  letI : Countable D := hD.to_subtype
  apply Measurable.neg
  apply Measurable.iInf
  intro v
  exact measurable_correctorFunctional ε U p ha (fun _ => measurable_const)

/-- The affine generator is bounded uniformly in the site and the elliptic environment. -/
private theorem abs_generator_linear_le (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) (q : Site d) :
    |generator ε a (linearFn ε p) q| ≤
      |ε ^ d / kappa d ε| * (lam⁻¹ * (∑ i, |p i|) *
        ∑' z : Site d, jumpKernel (physical ε z) * (1 + radius (physical ε z))) := by
  have hC : 0 ≤ ∑ i, |p i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs := summable_generator_affine hd hε hlam ha p
    (φ := 0) ⟨0, le_rfl, fun _ => by simp only [Pi.zero_apply, abs_zero, le_refl]⟩ q
  simp only [Pi.zero_apply, add_zero, linearFn_add, add_sub_cancel_left] at hs
  have ht := (summable_jumpKernel_weight hd hε).mul_left (lam⁻¹ * ∑ i, |p i|)
  unfold generator
  simp only [linearFn_add, add_sub_cancel_left, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ∑' z : Site d, |if hz : z = 0 then 0 else
        a (edgeAdd q z hz) * linearFn ε p z * jumpKernel (physical ε z)| :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' z : Site d, (lam⁻¹ * ∑ i, |p i|) *
        (jumpKernel (physical ε z) * (1 + radius (physical ε z))) := by
      apply hs.norm.tsum_le_tsum _ ht
      intro z
      simp only [Real.norm_eq_abs]
      by_cases hz : z = 0
      · simp only [hz, ↓reduceDIte, abs_zero]
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le) hC)
          (mul_nonneg (jumpKernel_nonneg _)
            (add_nonneg zero_le_one (radius_nonneg _)))
      · simp only [hz, ↓reduceDIte, abs_mul,
          abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg (jumpKernel_nonneg _)]
        calc
          _ ≤ (lam⁻¹ * ((∑ i, |p i|) * radius (physical ε z))) *
              jumpKernel (physical ε z) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (ha _).2 (abs_linearFn_le ε p z) (abs_nonneg _)
                (inv_nonneg.mpr hlam.le)) (jumpKernel_nonneg _)
          _ ≤ _ := by
            have hn := mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le) hC)
              (jumpKernel_nonneg (physical ε z))
            nlinarith only [hn]
    _ = _ := tsum_mul_left

/-- Completing the square bounds a quadratic polynomial with a positive leading coefficient. -/
private theorem quadratic_lower_bound {c A M F : ℝ} (hc : 0 < c)
    (hF : c * M ^ 2 - 2 * A * M ≤ F) : -(A ^ 2 / c) ≤ F := by
  have hsq := sq_nonneg (c * M - A)
  have hmul := mul_le_mul_of_nonneg_left hF hc.le
  rw [← neg_div]
  apply (div_le_iff₀ hc).mpr
  nlinarith only [hsq, hmul]

/-- Uniform ellipticity bounds the functional below, with a constant independent of the
conductance configuration. The bound may depend on the domain, scale, slope and ellipticity. -/
theorem exists_correctorFunctional_lower_bound (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (p : Fin d → ℝ) :
    ∃ C : ℝ, ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ w : Site d → ℝ, SupportedIn ε U w → -C ≤ correctorFunctional ε U a p w := by
  classical
  let s := (latticeSet_finite hε.1 hU).toFinset
  have hs : (s : Set (Site d)) = latticeSet ε U := Set.Finite.coe_toFinset _
  clear_value s
  by_cases hne : s.Nonempty
  · letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨r, hr⟩ := s.exists_notMem
    have hjump (q : Site d) (hq : q ∈ s) : 0 < jumpKernel (physical ε (r - q)) := by
      have hz : r - q ≠ 0 := sub_ne_zero.mpr (fun h => hr (h.symm ▸ hq))
      have hz' : physical ε (r - q) ≠ 0 :=
        fun h => hz ((physical_eq_zero_iff hε.1 _).mp h)
      rw [jumpKernel_of_ne_zero hz']
      exact inv_pos.mpr (pow_pos (radius_pos hz') _)
    obtain ⟨q₀, hq₀, hmin⟩ := s.exists_min_image
      (fun q => jumpKernel (physical ε (r - q))) hne
    let N := ε ^ (2 * d) / (2 * kappa d ε)
    have hN : 0 < N := div_pos (pow_pos hε.1 _)
      (mul_pos (by norm_num) (kappa_pos hd hε))
    let c := N * (lam * jumpKernel (physical ε (r - q₀)))
    have hc : 0 < c := mul_pos hN (mul_pos hlam (hjump q₀ hq₀))
    let G := |ε ^ d / kappa d ε| * (lam⁻¹ * (∑ i, |p i|) *
      ∑' z : Site d, jumpKernel (physical ε z) * (1 + radius (physical ε z)))
    let A := ε ^ d * ((s.card : ℝ) * G)
    refine ⟨A ^ 2 / c, ?_⟩
    intro a ha w hw
    have hwf : Function.HasFiniteSupport w := s.finite_toSet.subset (by
      intro q hq
      by_contra hqs
      exact hq (hw q (by simpa only [← hs, Finset.mem_coe] using hqs)))
    obtain ⟨q, hq, hmax⟩ := s.exists_max_image (fun q => |w q|) hne
    let M := |w q|
    have hquad : c * M ^ 2 ≤ bilinForm ε a w w := by
      have hz : r - q ≠ 0 := sub_ne_zero.mpr (fun h => hr (h.symm ▸ hq))
      have hwr : w r = 0 := hw r (by simpa only [← hs, Finset.mem_coe] using hr)
      have ht := (summable_bilinForm hd hε.1 hlam ha hwf hwf).le_tsum
        (q, r - q) (fun t _ => by
          by_cases ht : t.2 = 0
          · simp only [ht, ↓reduceDIte, le_refl]
          · simp only [ht, ↓reduceDIte]
            have hn := mul_nonneg
              (mul_nonneg (hlam.le.trans (ha (edgeAdd t.1 t.2 ht)).1)
                (jumpKernel_nonneg (physical ε t.2)))
              (sq_nonneg (w (t.1 + t.2) - w t.1))
            simpa only [pow_two, mul_assoc] using hn)
      have hqr : q + (r - q) = r := by abel
      simp only [hz, ↓reduceDIte, hqr, hwr, zero_sub] at ht
      have hcoef : lam * jumpKernel (physical ε (r - q₀)) ≤
          a (edgeAdd q (r - q) hz) * jumpKernel (physical ε (r - q)) :=
        mul_le_mul (ha _).1 (hmin q hq) (jumpKernel_nonneg _)
          (hlam.le.trans (ha _).1)
      calc
        c * M ^ 2 = N * (lam * jumpKernel (physical ε (r - q₀)) * w q ^ 2) := by
          dsimp only [c, M]
          rw [sq_abs]
          ring
        _ ≤ N * (a (edgeAdd q (r - q) hz) *
            jumpKernel (physical ε (r - q)) * w q ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)) hN.le
        _ ≤ bilinForm ε a w w := by
          calc
            _ = N * (a (edgeAdd q (r - q) hz) *
                jumpKernel (physical ε (r - q)) * (-w q) * (-w q)) := by ring
            _ ≤ bilinForm ε a w w := mul_le_mul_of_nonneg_left ht hN.le
    have hlin : |bilinForm ε a (linearFn ε p) w| ≤ A * M := by
      have hg := bilinForm_eq_neg_generator_affine hd hε.1 hlam ha p
        (φ := 0) ⟨0, le_rfl, fun _ => by simp only [Pi.zero_apply, abs_zero, le_refl]⟩ hwf
      simp only [Pi.zero_apply, add_zero] at hg
      rw [hg, abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hε.1.le _)]
      rw [tsum_eq_sum (s := s) (fun z hz => by
        rw [hw z (by simpa only [← hs, Finset.mem_coe] using hz), zero_mul])]
      calc
        _ ≤ ε ^ d * ∑ z ∈ s, |w z * generator ε a (linearFn ε p) z| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (pow_nonneg hε.1.le _)
        _ ≤ ε ^ d * ∑ _z ∈ s, M * G := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε.1.le _)
          apply Finset.sum_le_sum
          intro z hz
          rw [abs_mul]
          exact mul_le_mul (hmax z hz)
            (abs_generator_linear_le hd hε.1 hlam ha p z) (abs_nonneg _) (abs_nonneg _)
        _ = A * M := by simp only [Finset.sum_const, nsmul_eq_mul, A]; ring
    apply quadratic_lower_bound (A := A) (M := M) hc
    rw [correctorFunctional_eq_bilinForm hd hε.1 hlam ha p hwf hw]
    linarith [(abs_le.mp hlin).1]
  · refine ⟨0, ?_⟩
    intro a _ w hw
    have hw0 : w = 0 := by
      funext q
      exact hw q (by
        rw [← hs]
        exact fun h => hne ⟨q, h⟩)
    rw [hw0]
    simp [correctorFunctional]

/-- The range whose infimum defines the corrector energy is bounded below. -/
theorem correctorFunctional_range_bddBelow (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (p : Fin d → ℝ)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    BddBelow (Set.range fun w : {w : Site d → ℝ // SupportedIn ε U w} =>
      correctorFunctional ε U a p w) := by
  obtain ⟨C, hC⟩ := exists_correctorFunctional_lower_bound hd hε hlam hU p
  refine ⟨-C, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact hC a ha w.val w.property

/-- The admissible class in the corrector energy contains the zero field. -/
theorem correctorFunctional_range_nonempty (ε : ℝ) (U : Set (Fin d → ℝ))
    (a : Edge d → ℝ) (p : Fin d → ℝ) :
    (Set.range fun w : {w : Site d → ℝ // SupportedIn ε U w} =>
      correctorFunctional ε U a p w).Nonempty := by
  exact ⟨correctorFunctional ε U a p 0, ⟨⟨0, fun _ _ => rfl⟩, rfl⟩⟩

end

end LongRange
