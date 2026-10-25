import LongRange.Corrector.Definition

/-!
# Linear dependence of the source corrector on its slope

The affine forcing is linear in the physical slope. Inverting the nondegenerate energy
form on supported variations gives a linear map whose values are precisely the unique
minimizers, equivalently the unique solutions of the source corrector equation.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The corrector equation has exactly one solution under the standing assumptions. -/
theorem existsUnique_correctorSolution (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) :
    ∃! φ : Site d → ℝ, IsCorrectorSolution ε U a p φ := by
  obtain ⟨⟨φ, hφ, huniq⟩, hiff⟩ := corrector_wellDefined hd hε hU hlam ha p
  exact ⟨φ, (hiff φ).mp hφ, fun ψ hψ => huniq ψ ((hiff ψ).mpr hψ)⟩

/-- Addition of slopes adds their physical affine functions. -/
theorem linearFn_slope_add (ε : ℝ) (p r : Fin d → ℝ) :
    linearFn ε (p + r) = linearFn ε p + linearFn ε r := by
  funext q
  simp only [linearFn, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Scaling a slope scales its physical affine function. -/
theorem linearFn_slope_smul (ε t : ℝ) (p : Fin d → ℝ) :
    linearFn ε (t • p) = t • linearFn ε p := by
  funext q
  simp only [linearFn, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The affine cross energy is additive in slopes, with convergence supplied by the
finite support of the test function. -/
theorem bilinForm_slope_add (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p r : Fin d → ℝ)
    {v : Site d → ℝ} (hv : v.HasFiniteSupport) :
    bilinForm ε a (linearFn ε (p + r)) v =
      bilinForm ε a (linearFn ε p) v + bilinForm ε a (linearFn ε r) v := by
  classical
  have hs := summable_bilinForm_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ hv
  have ht := summable_bilinForm_affine hd hε hlam ha r
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ hv
  simp only [add_zero] at hs ht
  rw [linearFn_slope_add]
  unfold bilinForm
  rw [← mul_add, ← Summable.tsum_add hs ht]
  congr 1
  apply tsum_congr
  intro q
  by_cases hz : q.2 = 0 <;> simp only [hz, ↓reduceDIte, Pi.add_apply] <;> ring

/-- Physical affine forcing, bundled as a linear map from slopes to the dual variation
space. Bilinearity is used only with finitely supported test functions. -/
def correctorSlopeForm (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ}
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    (Fin d → ℝ) →ₗ[ℝ] Module.Dual ℝ (correctorVariationSpace ε U) where
  toFun := correctorAffineForm hd hε hU hlam ha
  map_add' p r := by
    ext v
    change -bilinForm ε a (linearFn ε (p + r)) v.val =
      -bilinForm ε a (linearFn ε p) v.val + -bilinForm ε a (linearFn ε r) v.val
    rw [bilinForm_slope_add hd hε hlam ha p r (v.property.hasFiniteSupport hε hU),
      neg_add]
  map_smul' t p := by
    ext v
    change -bilinForm ε a (linearFn ε (t • p)) v.val =
      t * -bilinForm ε a (linearFn ε p) v.val
    rw [linearFn_slope_smul, bilinForm_smul_left, mul_neg]

/-- There is exactly one linear map taking every slope to its source corrector. The
characterization is a literal equality of lattice functions and includes both the
minimizing property and the complete supported corrector equation. -/
theorem existsUnique_correctorLinearMap (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃! T : (Fin d → ℝ) →ₗ[ℝ] correctorVariationSpace ε U,
      ∀ (p : Fin d → ℝ) (φ : Site d → ℝ),
        ((T p).val = φ ↔ IsCorrectorSolution ε U a p φ) ∧
        ((T p).val = φ ↔ IsCorrectorMinimizer ε U a p φ) := by
  letI := correctorVariationSpace_finite hε.1 hU
  let B := correctorVariationForm hd hε.1 hU hlam ha
  have hB : B.Nondegenerate := correctorVariationForm_nondegenerate hd hε hU hlam ha
  let T := (B.toDual hB).symm.toLinearMap.comp
    (correctorSlopeForm hd hε.1 hU hlam ha)
  have hmin (p : Fin d → ℝ) : IsCorrectorMinimizer ε U a p (T p).val := by
    refine ⟨(T p).property, ?_⟩
    apply (correctorMinimizer_iff_variations hd hε.1 hU hlam ha p (T p).property).mpr
    intro η hη
    have heq : bilinForm ε a (T p).val η = -bilinForm ε a (linearFn ε p) η :=
      LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB)
        (correctorAffineForm hd hε.1 hU hlam ha p) ⟨η, hη⟩
    rw [bilinForm_affine_add hd hε.1 hlam ha p
      ((T p).property.hasFiniteSupport hε.1 hU) (hη.hasFiniteSupport hε.1 hU), heq]
    exact add_neg_cancel _
  have hchar (p : Fin d → ℝ) (φ : Site d → ℝ) :
      (T p).val = φ ↔ IsCorrectorMinimizer ε U a p φ := by
    constructor
    · intro heq
      exact heq ▸ hmin p
    · intro hφ
      obtain ⟨ψ, _, huniq⟩ := (corrector_wellDefined hd hε hU hlam ha p).1
      exact (huniq _ (hmin p)).trans (huniq _ hφ).symm
  refine ⟨T, ?_, ?_⟩
  · intro p φ
    exact ⟨(hchar p φ).trans ((corrector_wellDefined hd hε hU hlam ha p).2 φ),
      hchar p φ⟩
  · intro S hS
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact ((hS p (T p).val).2).mpr (hmin p)

end

end LongRange
