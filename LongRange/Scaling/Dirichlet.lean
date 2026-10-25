import LongRange.Scaling.Generator
import LatticeProb.Analysis.Elliptic.Dirichlet

/-!
# Dirichlet solutions under halving of the domain

Zero exterior values and the actual pointwise generator equation characterize the discrete
solution uniquely. The generator scaling therefore identifies the two solutions, at the same
integer indices, without assuming a solution-scaling bridge.
-/

namespace LongRange.Scaling

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The half-domain is the inverse image of `U` under multiplication by two. -/
def halfDomain (U : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {x | (2 : ℝ) • x ∈ U}

/-- Halving physical coordinates leaves the integer index unchanged. -/
theorem twice_physical_half (ε : ℝ) (q : Site d) :
    (2 : ℝ) • physical (ε / 2) q = physical ε q := by
  ext i
  change 2 * (ε / 2 * (q i : ℝ)) = ε * (q i : ℝ)
  ring

/-- The two domains have exactly the same integer lattice sites. -/
theorem latticeSet_halfDomain (ε : ℝ) (U : Set (Fin d → ℝ)) :
    latticeSet (ε / 2) (halfDomain U) = latticeSet ε U := by
  ext q
  change (2 : ℝ) • physical (ε / 2) q ∈ U ↔ physical ε q ∈ U
  rw [twice_physical_half]

/-- The physical half-domain of a bounded domain is bounded. -/
theorem halfDomain_isBounded {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) :
    Bornology.IsBounded (halfDomain U) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hU
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R / 2, ?_⟩
  intro x hx
  have h := hR ((2 : ℝ) • x) hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- A bounded-domain, zero-exterior harmonic function is zero, by positive definite energy. -/
theorem eq_zero_of_generator_eq_zero (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {u : Site d → ℝ}
    (hu : SupportedIn ε U u)
    (heq : ∀ q ∈ latticeSet ε U, generator ε a u q = 0) : u = 0 := by
  have hfin := hu.hasFiniteSupport hε.1 hU
  apply eq_zero_of_bilinForm_self_eq_zero hd hε hlam ha hfin
  rw [bilinForm_eq_neg_generator_bounded hd hε.1 hlam ha
    (exists_bound_of_finite_support hfin) hfin]
  have hz : ∀ q : Site d, u q * generator ε a u q = 0 := by
    intro q
    by_cases hq : q ∈ latticeSet ε U
    · rw [heq q hq, mul_zero]
    · rw [hu q hq, zero_mul]
  simp only [hz, tsum_zero, mul_zero, neg_zero]

/-- The actual zero-exterior Dirichlet equation has at most one solution. -/
theorem dirichlet_unique (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f u v : Site d → ℝ}
    (hu : SupportedIn ε U u) (hv : SupportedIn ε U v)
    (heu : ∀ q ∈ latticeSet ε U, -generator ε a u q = f q)
    (hev : ∀ q ∈ latticeSet ε U, -generator ε a v q = f q) : u = v := by
  have hs : SupportedIn ε U (fun q => u q - v q) := by
    intro q hq
    change u q - v q = 0
    rw [hu q hq, hv q hq, sub_self]
  have heq : ∀ q ∈ latticeSet ε U,
      generator ε a (fun z => u z - v z) q = 0 := by
    intro q hq
    rw [generator_sub ε a q
      (summable_generator_bounded hd hε.1 hlam ha
        (exists_bound_of_finite_support (hu.hasFiniteSupport hε.1 hU)) q)
      (summable_generator_bounded hd hε.1 hlam ha
        (exists_bound_of_finite_support (hv.hasFiniteSupport hε.1 hU)) q)]
    linarith [heu q hq, hev q hq]
  have hz := eq_zero_of_generator_eq_zero hd hε hU hlam ha hs heq
  funext q
  have h := congrFun hz q
  exact sub_eq_zero.mp h

/-- Every forcing on a bounded lattice domain has a unique actual zero-mass Dirichlet
solution, obtained by inverting the positive definite finite-dimensional energy form. -/
theorem existsUnique_dirichlet (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (f : Site d → ℝ) :
    ∃! u : Site d → ℝ, SupportedIn ε U u ∧
      ∀ q ∈ latticeSet ε U, -generator ε a u q = f q := by
  classical
  letI := (latticeSet_finite hε.1 hU).fintype
  letI := correctorVariationSpace_finite hε.1 hU
  let B := correctorVariationForm hd hε.1 hU hlam ha
  have hB : B.Nondegenerate := correctorVariationForm_nondegenerate hd hε hU hlam ha
  let L : Module.Dual ℝ (correctorVariationSpace ε U) :=
    { toFun := fun v => ε ^ d * ∑ q : latticeSet ε U, v.val q * f q
      map_add' := fun v w => by
        simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
          mul_add]
      map_smul' := fun t v => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          mul_assoc, ← Finset.mul_sum]
        ring }
  let u := (B.toDual hB).symm L
  have hu (v : correctorVariationSpace ε U) : bilinForm ε a u.val v.val =
      ε ^ d * ∑ q : latticeSet ε U, v.val q * f q :=
    LinearMap.BilinForm.apply_toDual_symm_apply (B := B) (hB := hB) L v
  have heq : ∀ q ∈ latticeSet ε U, -generator ε a u.val q = f q := by
    intro q hq
    let η : Site d → ℝ := fun x => if x = q then 1 else 0
    have hη : SupportedIn ε U η := by
      intro x hx
      change (if x = q then (1 : ℝ) else 0) = 0
      exact if_neg (fun he : x = q => hx (he.symm ▸ hq))
    have hv := hu ⟨η, hη⟩
    rw [bilinForm_eq_neg_generator_bounded hd hε.1 hlam ha
      (exists_bound_of_finite_support (u.property.hasFiniteSupport hε.1 hU))
      (hη.hasFiniteSupport hε.1 hU)] at hv
    have ht : (∑' x : Site d, η x * generator ε a u.val x) =
        generator ε a u.val q := by
      simp only [η, ite_mul, one_mul, zero_mul, tsum_ite_eq]
    have hf : (∑ x : latticeSet ε U, η x * f x) = f q := by
      have hi : (fun x : latticeSet ε U => η x * f x) =
          fun x => if x = ⟨q, hq⟩ then f q else 0 := by
        funext x
        simp only [η, ite_mul, one_mul, zero_mul, Subtype.ext_iff]
        split_ifs with hx
        · rw [hx]
        · rfl
      rw [hi, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    change -(ε ^ d * ∑' x : Site d, η x * generator ε a u.val x) =
      ε ^ d * ∑ x : latticeSet ε U, η x * f x at hv
    rw [ht, hf, ← mul_neg] at hv
    exact mul_left_cancel₀ (pow_ne_zero _ hε.1.ne') hv
  refine ⟨u.val, ⟨u.property, heq⟩, ?_⟩
  intro v hv
  exact dirichlet_unique hd hε hU hlam ha hv.1 u.property hv.2 heq

/-- The source's two actual solutions satisfy its discrete scaling identity.
The forcing in the half-domain is `4 f(2x)`, with the same conductance field. -/
theorem dirichlet_half_scaling (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (f : (Fin d → ℝ) → ℝ) {u v : Site d → ℝ}
    (hu : SupportedIn ε U u) (hv : SupportedIn (ε / 2) (halfDomain U) v)
    (heu : ∀ q ∈ latticeSet ε U, -generator ε a u q = f (physical ε q))
    (hev : ∀ q ∈ latticeSet (ε / 2) (halfDomain U),
      -generator (ε / 2) a v q = 4 * f ((2 : ℝ) • physical (ε / 2) q)) :
    v = fun q => kappa d (ε / 2) / kappa d ε * u q := by
  have hh : ε / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  apply dirichlet_unique hd hh (halfDomain_isBounded hU) hlam ha hv
  · intro q hq
    rw [latticeSet_halfDomain] at hq
    change kappa d (ε / 2) / kappa d ε * u q = 0
    rw [hu q hq, mul_zero]
  · exact hev
  · intro q hq
    rw [latticeSet_halfDomain] at hq
    rw [generator_half_normalized hd hε, twice_physical_half]
    linarith [heu q hq]

/-- The source lattice measure changes by exactly `2⁻ᵈ` on the shared integer carrier. -/
theorem l2NormSq_halfDomain (ε : ℝ) (U : Set (Fin d → ℝ)) (g : Site d → ℝ) :
    l2NormSq (ε / 2) (halfDomain U) g = (2 : ℝ)⁻¹ ^ d * l2NormSq ε U g := by
  unfold l2NormSq
  rw [latticeSet_halfDomain, div_eq_mul_inv, mul_pow]
  ring

/-- Dilation by two on the continuum coordinate carrier. -/
def doubleEquiv : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin d → ℝ)
    (Units.mk0 (2 : ℝ) (by norm_num))

/-- The continuum dilation acts by ordinary scalar multiplication. -/
theorem doubleEquiv_apply (x : Fin d → ℝ) : doubleEquiv x = (2 : ℝ) • x := rfl

/-- The continuum Laplacian acquires the factor four under dilation by two. -/
theorem laplacian_double (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Elliptic.laplacian (fun y => u ((2 : ℝ) • y)) x =
      4 * Elliptic.laplacian u ((2 : ℝ) • x) := by
  have h := (doubleEquiv (d := d)).iteratedFDerivWithin_comp_right u uniqueDiffOn_univ
    (Set.mem_univ (doubleEquiv x)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  unfold Elliptic.laplacian Elliptic.secondPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ 2 (u ∘ doubleEquiv) x ![Pi.single i 1, Pi.single i 1] = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun j : Fin 2 => doubleEquiv (![Pi.single i 1, Pi.single i 1] j)) =
      fun j => (2 : ℝ) • (![Pi.single i 1, Pi.single i 1] j) := rfl
  change (iteratedFDeriv ℝ 2 u (doubleEquiv x))
    (fun j => doubleEquiv (![Pi.single i 1, Pi.single i 1] j)) = _
  rw [hv, ContinuousMultilinearMap.map_smul_univ]
  norm_num
  rfl

/-- The classical continuum solution produces the actual rescaled classical solution.
Thus its scaling identity is definitional and its equation is proved, rather than assumed. -/
theorem classical_dirichlet_half {U : Set (Fin d → ℝ)} {a₀ : ℝ}
    {f u : (Fin d → ℝ) → ℝ}
    (hu : Elliptic.IsClassicalDirichletSolution U 0 a₀ f u) :
    Elliptic.IsClassicalDirichletSolution (halfDomain U) 0 a₀
      (fun x => 4 * f ((2 : ℝ) • x)) (fun x => u ((2 : ℝ) • x)) := by
  refine ⟨hu.1.comp (by fun_prop) (fun x hx => hx), ?_, ?_, ?_⟩
  · apply hu.2.1.comp (by fun_prop)
    intro x hx
    have he := (doubleEquiv (d := d)).toHomeomorph.preimage_closure U
    have hm : x ∈ (doubleEquiv (d := d)).toHomeomorph ⁻¹' closure U := by
      rw [he]
      exact hx
    exact hm
  · intro x hx
    apply hu.2.2.1
    have he := (doubleEquiv (d := d)).toHomeomorph.preimage_frontier U
    have hm : x ∈ (doubleEquiv (d := d)).toHomeomorph ⁻¹' frontier U := by
      rw [he]
      exact hx
    exact hm
  · intro x hx
    rw [laplacian_double]
    have he := hu.2.2.2 ((2 : ℝ) • x) hx
    linarith

/-- The produced classical half-domain solution satisfies the printed continuum identity. -/
theorem classical_half_identity (u : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (fun y => u ((2 : ℝ) • y)) ((2 : ℝ)⁻¹ • x) = u x := by
  change u ((2 : ℝ) • ((2 : ℝ)⁻¹ • x)) = u x
  rw [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]

end

end LongRange.Scaling
