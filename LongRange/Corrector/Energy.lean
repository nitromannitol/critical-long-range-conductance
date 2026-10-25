import LongRange.Corrector.Existence

/-!
# The value of the corrector variational problem at an attained minimum

An actual minimizer supplies both a lower bound and a member of the admissible functional
range. Consequently its functional value is the genuine infimum. Testing the minimizer
against zero also proves that the corrector energy is nonnegative.
-/

namespace LongRange

open LatticeProb

noncomputable section

/-- The zero function is admissible for the corrector variational problem. -/
theorem supportedIn_zero {d : ℕ} (ε : ℝ) (U : Set (Fin d → ℝ)) :
    SupportedIn ε U (fun _ => 0) := by
  intro _ _
  rfl

/-- The subtracted affine square makes the functional vanish on the zero test function. -/
theorem correctorFunctional_zero {d : ℕ} (ε : ℝ) (U : Set (Fin d → ℝ))
    (a : Edge d → ℝ) (p : Fin d → ℝ) :
    correctorFunctional ε U a p (fun _ => 0) = 0 := by
  simp only [correctorFunctional, add_zero, sub_zero, sub_self, mul_zero, dite_eq_ite,
    ite_self, tsum_zero]

/-- A supported minimizer realizes the true infimum defining the corrector energy. -/
theorem correctorEnergy_eq_neg_functional {d : ℕ} {ε : ℝ}
    {U : Set (Fin d → ℝ)} {a : Edge d → ℝ} (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ)
    (hmin : ∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w) :
    correctorEnergy ε U a p = -correctorFunctional ε U a p φ := by
  let S := Set.range fun w : {w : Site d → ℝ // SupportedIn ε U w} =>
    correctorFunctional ε U a p w
  have hmem : correctorFunctional ε U a p φ ∈ S := ⟨⟨φ, hφ⟩, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hbound : BddBelow S := by
    refine ⟨correctorFunctional ε U a p φ, ?_⟩
    rintro b ⟨w, rfl⟩
    exact hmin w w.property
  have hinf : sInf S = correctorFunctional ε U a p φ := by
    apply le_antisymm (csInf_le hbound hmem)
    apply le_csInf hne
    rintro b ⟨w, rfl⟩
    exact hmin w w.property
  exact congrArg Neg.neg hinf

/-- Comparing an attained minimum with the zero test function gives nonnegative energy. -/
theorem correctorEnergy_nonneg {d : ℕ} {ε : ℝ}
    {U : Set (Fin d → ℝ)} {a : Edge d → ℝ} (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ)
    (hmin : ∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w) :
    0 ≤ correctorEnergy ε U a p := by
  rw [correctorEnergy_eq_neg_functional p hφ hmin]
  have htest := hmin (fun _ => 0) (supportedIn_zero ε U)
  rw [correctorFunctional_zero] at htest
  exact neg_nonneg.mpr htest

/-- At a supported minimizer, the first variation against itself cancels the affine cross
term and identifies the variational energy with the diagonal bilinear energy. -/
theorem correctorEnergy_eq_bilinForm {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ)
    (hmin : ∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w) :
    correctorEnergy ε U a p = bilinForm ε a φ φ := by
  have hv := (correctorMinimizer_iff_variations hd hε.1 hU hlam ha p hφ).mp hmin φ hφ
  have hf := hφ.hasFiniteSupport hε.1 hU
  rw [bilinForm_affine_add hd hε.1 hlam ha p hf hf] at hv
  rw [correctorEnergy_eq_neg_functional p hφ hmin,
    correctorFunctional_eq_quadratic hd hε.1 hU hlam ha p hφ]
  linarith only [hv]

/-- Ellipticity compares the attained corrector energy with half the critical seminorm,
with precisely the two constants appearing in the paper. -/
theorem correctorEnergy_comparison {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : SupportedIn ε U φ)
    (hmin : ∀ w, SupportedIn ε U w →
      correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w) :
    lam / 2 * h1CritSq ε φ ≤ correctorEnergy ε U a p ∧
      correctorEnergy ε U a p ≤ lam⁻¹ / 2 * h1CritSq ε φ := by
  rw [correctorEnergy_eq_bilinForm hd hε hU hlam ha p hφ hmin]
  exact bilinForm_self_bounds hd hε.1 hlam ha (hφ.hasFiniteSupport hε.1 hU)

end

end LongRange
