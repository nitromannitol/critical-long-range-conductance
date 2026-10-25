import LongRange.Corrector.Energy

/-!
# Monotonicity of the corrector energy

A corrector on a larger domain minimizes over every variation supported in the smaller
one. The quadratic identity removes the touching-edge gate before comparing minima.
Ellipticity then gives the norm estimate for a nonnegative Poincaré constant.
-/

namespace LongRange

open LatticeProb

noncomputable section

/-- Enlarging the physical domain preserves the support condition. -/
theorem SupportedIn.mono {d : ℕ} {ε : ℝ} {U V : Set (Fin d → ℝ)}
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ) (hUV : U ⊆ V) :
    SupportedIn ε V φ := by
  intro q hq
  exact hφ q (fun h => hq (hUV h))

/-- On a variation supported in both domains, the touching-edge functionals agree. -/
theorem correctorFunctional_eq_of_supportedIn {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) {U V : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hV : Bornology.IsBounded V)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφU : SupportedIn ε U φ) (hφV : SupportedIn ε V φ) :
    correctorFunctional ε U a p φ = correctorFunctional ε V a p φ := by
  rw [correctorFunctional_eq_quadratic hd hε hU hlam ha p hφU,
    correctorFunctional_eq_quadratic hd hε hV hlam ha p hφV]

/-- The energy of a supported harmonic corrector increases when its domain increases. -/
theorem corrector_bilinForm_mono {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U V : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hV : Bornology.IsBounded V) (hUV : U ⊆ V)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φU φV : Site d → ℝ}
    (hφU : SupportedIn ε U φU)
    (hgU : ∀ q ∈ latticeSet ε U,
      generator ε a (fun x => linearFn ε p x + φU x) q = 0)
    (hφV : SupportedIn ε V φV)
    (hgV : ∀ q ∈ latticeSet ε V,
      generator ε a (fun x => linearFn ε p x + φV x) q = 0) :
    bilinForm ε a φU φU ≤ bilinForm ε a φV φV := by
  have hmU := (isCorrectorMinimizer_iff hd hε hU hlam ha p hφU).mpr hgU
  have hmV := (isCorrectorMinimizer_iff hd hε hV hlam ha p hφV).mpr hgV
  have htest := hmV φU (hφU.mono hUV)
  rw [← correctorFunctional_eq_of_supportedIn hd hε.1 hU hV hlam ha p
    hφU (hφU.mono hUV)] at htest
  have heU := correctorEnergy_eq_neg_functional p hφU hmU
  have heV := correctorEnergy_eq_neg_functional p hφV hmV
  rw [correctorEnergy_eq_bilinForm hd hε hU hlam ha p hφU hmU] at heU
  rw [correctorEnergy_eq_bilinForm hd hε hV hlam ha p hφV hmV] at heV
  linarith only [htest, heU, heV]

/-- With a nonnegative Poincaré constant, energy monotonicity controls both squared norms.
The Poincaré estimate is an explicit premise, independent of the harmonic equations. -/
theorem corrector_norm_mono_of_poincare {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U V : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hV : Bornology.IsBounded V) (hUV : U ⊆ V)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {Cp : ℝ} (hCp : 0 ≤ Cp)
    (hP : ∀ ψ, SupportedIn ε U ψ → l2NormSq ε U ψ ≤ Cp * h1CritSq ε ψ)
    {φU φV : Site d → ℝ}
    (hφU : SupportedIn ε U φU)
    (hgU : ∀ q ∈ latticeSet ε U,
      generator ε a (fun x => linearFn ε p x + φU x) q = 0)
    (hφV : SupportedIn ε V φV)
    (hgV : ∀ q ∈ latticeSet ε V,
      generator ε a (fun x => linearFn ε p x + φV x) q = 0) :
    h1CritSq ε φU + l2NormSq ε U φU ≤
      (1 + Cp) * lam⁻¹ ^ 2 * (h1CritSq ε φV + l2NormSq ε V φV) := by
  have hm := corrector_bilinForm_mono hd hε hU hV hUV hlam ha p hφU hgU hφV hgV
  have hbU := (bilinForm_self_bounds hd hε.1 hlam ha
    (hφU.hasFiniteSupport hε.1 hU)).1
  have hbV := (bilinForm_self_bounds hd hε.1 hlam ha
    (hφV.hasFiniteSupport hε.1 hV)).2
  have hscale : h1CritSq ε φU ≤ lam⁻¹ ^ 2 * h1CritSq ε φV := by
    have hb : lam * h1CritSq ε φU ≤ lam⁻¹ * h1CritSq ε φV := by
      linarith only [hbU, hm, hbV]
    have ht := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hlam.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul, pow_two] using ht
  have hl2 : 0 ≤ l2NormSq ε V φV := by
    exact mul_nonneg (pow_nonneg hε.1.le _) (tsum_nonneg (fun _ => sq_nonneg _))
  calc
    h1CritSq ε φU + l2NormSq ε U φU ≤ (1 + Cp) * h1CritSq ε φU := by
      linarith only [hP φU hφU]
    _ ≤ (1 + Cp) * (lam⁻¹ ^ 2 * h1CritSq ε φV) :=
      mul_le_mul_of_nonneg_left hscale (by linarith only [hCp])
    _ ≤ (1 + Cp) * lam⁻¹ ^ 2 * (h1CritSq ε φV + l2NormSq ε V φV) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hl2)
        (mul_nonneg (by linarith only [hCp]) (sq_nonneg _))

end

end LongRange
