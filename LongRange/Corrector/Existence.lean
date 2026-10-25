import LongRange.Corrector.EulerLagrange
import LongRange.Appendix.Kappa
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Unique attainment of the corrector variational problem

The diagonal energy is positive definite on finitely supported variations. The finite
space of supported functions is therefore identified with its dual by its bilinear energy.
Solving against the affine cross term gives the unique minimizer.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A finitely supported function of zero energy vanishes, since the Euclidean kernel is
strictly positive between every pair of distinct sites. -/
theorem eq_zero_of_bilinForm_self_eq_zero (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {u : Site d → ℝ} (hu : u.HasFiniteSupport) (hz : bilinForm ε a u u = 0) :
    u = 0 := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hlo := (bilinForm_self_bounds hd hε.1 hlam ha hu).1
  rw [hz] at hlo
  have hn : 0 ≤ h1CritSq ε u := by
    exact mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le)
      (tsum_nonneg fun q => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _))
  have hh : h1CritSq ε u = 0 := by
    have hp : 0 < lam / 2 := div_pos hlam (by norm_num)
    exact le_antisymm (nonpos_of_mul_nonpos_right hlo hp) hn
  have hc : 0 < ε ^ (2 * d) / kappa d ε :=
    div_pos (pow_pos hε.1 _) (kappa_pos hd hε)
  have hsum : (∑' q : Site d × Site d,
      jumpKernel (physical ε q.2) * (u (q.1 + q.2) - u q.1) ^ 2) = 0 :=
    (mul_eq_zero.mp hh).resolve_left hc.ne'
  have hs := summable_h1CritSq hd hε.1 hu
  obtain ⟨y, hy⟩ := hu.exists_notMem
  have huy : u y = 0 := by simpa only [Function.mem_support, not_not] using hy
  ext x
  by_cases hxy : y = x
  · simpa only [Pi.zero_apply, ← hxy] using huy
  · have hw : y - x ≠ 0 := sub_ne_zero.mpr hxy
    have hj : 0 < jumpKernel (physical ε (y - x)) := by
      rw [jumpKernel_of_ne_zero ((physical_eq_zero_iff hε.1 _).not.mpr hw)]
      exact inv_pos.mpr (pow_pos (radius_pos
        ((physical_eq_zero_iff hε.1 _).not.mpr hw)) _)
    have ht := hs.le_tsum (x, y - x) (fun q _ =>
      mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _))
    rw [hsum] at ht
    have hcancel : x + (y - x) = y := by abel
    rw [hcancel, huy] at ht
    simp only [zero_sub, neg_sq] at ht
    have hsq : u x ^ 2 = 0 :=
      (mul_eq_zero.mp (le_antisymm ht (mul_nonneg hj.le (sq_nonneg _)))).resolve_left
        hj.ne'
    simpa only [Pi.zero_apply] using (sq_eq_zero_iff.mp hsq)

/-- The real vector space of functions vanishing outside the physical lattice domain. -/
def correctorVariationSpace (ε : ℝ) (U : Set (Fin d → ℝ)) :
    Submodule ℝ (Site d → ℝ) where
  carrier := {u | SupportedIn ε U u}
  zero_mem' := by intro _ _; rfl
  add_mem' := fun hu hv => hu.add hv
  smul_mem' := fun t _ hu => hu.smul t

/-- Restriction to the finite lattice domain proves finite dimensionality of variations. -/
theorem correctorVariationSpace_finite {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) :
    FiniteDimensional ℝ (correctorVariationSpace ε U) := by
  classical
  letI : Fintype (latticeSet ε U) := (latticeSet_finite hε hU).fintype
  let R : correctorVariationSpace ε U →ₗ[ℝ] (latticeSet ε U → ℝ) :=
    { toFun := fun u q => u.val q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective R
  intro u v huv
  apply Subtype.ext
  funext q
  by_cases hq : q ∈ latticeSet ε U
  · exact congrFun huv ⟨q, hq⟩
  · rw [u.property q hq, v.property q hq]

/-- The convergent bilinear energy restricted to supported variations. -/
def correctorVariationForm (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ}
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    LinearMap.BilinForm ℝ (correctorVariationSpace ε U) where
  toFun u :=
    { toFun := fun v => bilinForm ε a u.val v.val
      map_add' := fun v w => bilinForm_add_right hd hε hlam ha
        (u.property.hasFiniteSupport hε hU) (v.property.hasFiniteSupport hε hU)
        (w.property.hasFiniteSupport hε hU)
      map_smul' := fun t v => bilinForm_smul_right ε a t u.val v.val }
  map_add' u v := by
    ext w
    exact bilinForm_add_left hd hε hlam ha (u.property.hasFiniteSupport hε hU)
      (v.property.hasFiniteSupport hε hU) (w.property.hasFiniteSupport hε hU)
  map_smul' t u := by
    ext v
    exact bilinForm_smul_left ε a t u.val v.val

/-- The affine cross term is a genuine linear functional on supported variations. -/
def correctorAffineForm (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ}
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) :
    Module.Dual ℝ (correctorVariationSpace ε U) where
  toFun u := -bilinForm ε a (linearFn ε p) u.val
  map_add' u v := by
    rw [show (u + v).val = u.val + v.val from rfl,
      bilinForm_linear_add_right hd hε hlam ha p
        (u.property.hasFiniteSupport hε hU) (v.property.hasFiniteSupport hε hU)]
    exact neg_add _ _
  map_smul' t u := by
    change -bilinForm ε a (linearFn ε p) (t • u.val) =
      t * -bilinForm ε a (linearFn ε p) u.val
    rw [bilinForm_smul_right, mul_neg]

/-- Positive definiteness makes the supported energy form nondegenerate. -/
theorem correctorVariationForm_nondegenerate (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    (correctorVariationForm hd hε.1 hU hlam ha).Nondegenerate := by
  constructor
  · intro u hu
    apply Subtype.ext
    exact eq_zero_of_bilinForm_self_eq_zero hd hε hlam ha
      (u.property.hasFiniteSupport hε.1 hU) (hu u)
  · intro u hu
    apply Subtype.ext
    exact eq_zero_of_bilinForm_self_eq_zero hd hε hlam ha
      (u.property.hasFiniteSupport hε.1 hU) (hu u)

/-- The strictly convex corrector functional has exactly one supported minimizer. -/
theorem existsUnique_correctorMinimizer {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) :
    ∃! φ : Site d → ℝ, SupportedIn ε U φ ∧
      ∀ w, SupportedIn ε U w →
        correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w := by
  letI := correctorVariationSpace_finite hε.1 hU
  let B := correctorVariationForm hd hε.1 hU hlam ha
  have hB : B.Nondegenerate := correctorVariationForm_nondegenerate hd hε hU hlam ha
  let L := correctorAffineForm hd hε.1 hU hlam ha p
  let u := (B.toDual hB).symm L
  have hu (v : correctorVariationSpace ε U) : bilinForm ε a u.val v.val =
      -bilinForm ε a (linearFn ε p) v.val :=
    LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB) L v
  have hmin : ∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p u.val ≤ correctorFunctional ε U a p w := by
    apply (correctorMinimizer_iff_variations hd hε.1 hU hlam ha p u.property).mpr
    intro η hη
    rw [bilinForm_affine_add hd hε.1 hlam ha p
      (u.property.hasFiniteSupport hε.1 hU) (hη.hasFiniteSupport hε.1 hU), hu ⟨η, hη⟩]
    exact add_neg_cancel _
  refine ⟨u.val, ⟨u.property, hmin⟩, ?_⟩
  rintro φ ⟨hφ, hφmin⟩
  have hv := (correctorMinimizer_iff_variations hd hε.1 hU hlam ha p hφ).mp hφmin
  have heq : B ⟨φ, hφ⟩ = B u := by
    ext v
    have hvv := hv v.val v.property
    rw [bilinForm_affine_add hd hε.1 hlam ha p
      (hφ.hasFiniteSupport hε.1 hU) (v.property.hasFiniteSupport hε.1 hU)] at hvv
    change bilinForm ε a φ v.val = bilinForm ε a u.val v.val
    rw [hu v]
    linarith only [hvv]
  have hinj : Function.Injective B := LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  exact congrArg Subtype.val (hinj heq)

end

end LongRange
