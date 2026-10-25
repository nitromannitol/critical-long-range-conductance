import LongRange.Corrector.CorrectorLinearMap
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic dependence of the true corrector energy on its slope

The supported corrector linear map pulls back the convergent variation energy form.
Its diagonal is a Mathlib quadratic map and agrees with the negative true infimum
in the source definition, with the original normalization and Euclidean kernel.
-/

namespace LongRange

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The source energy, defined as a negative infimum, is represented by exactly one
Mathlib quadratic map on slopes under the standing assumptions. -/
theorem existsUnique_correctorEnergyQuadraticMap (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃! Q : QuadraticMap ℝ (Fin d → ℝ) ℝ,
      ∀ p, Q p = correctorEnergy ε U a p := by
  obtain ⟨T, hT, _⟩ := existsUnique_correctorLinearMap hd hε hU hlam ha
  let B := correctorVariationForm hd hε.1 hU hlam ha
  let Q := B.toQuadraticMap.comp T
  have hQ (p : Fin d → ℝ) : Q p = correctorEnergy ε U a p := by
    have hmin := ((hT p (T p).val).2).mp rfl
    exact (correctorEnergy_eq_bilinForm hd hε hU hlam ha p hmin.1 hmin.2).symm
  refine ⟨Q, hQ, ?_⟩
  intro R hR
  apply DFunLike.ext
  intro p
  exact (hR p).trans (hQ p).symm

/-- The source corrector equation and the true variational energy are simultaneously
represented by a linear map and a quadratic map. Nonnegativity and both precise
ellipticity constants hold for every slope without an additional solver premise. -/
theorem exists_corrector_linear_quadratic (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ (T : (Fin d → ℝ) →ₗ[ℝ] correctorVariationSpace ε U)
      (Q : QuadraticMap ℝ (Fin d → ℝ) ℝ),
      (∀ (p : Fin d → ℝ) (φ : Site d → ℝ),
        ((T p).val = φ ↔ IsCorrectorSolution ε U a p φ) ∧
        ((T p).val = φ ↔ IsCorrectorMinimizer ε U a p φ)) ∧
      ∀ p, Q p = correctorEnergy ε U a p ∧
        Q p = bilinForm ε a (T p).val (T p).val ∧
        0 ≤ Q p ∧
        lam / 2 * h1CritSq ε (T p).val ≤ Q p ∧
        Q p ≤ lam⁻¹ / 2 * h1CritSq ε (T p).val := by
  obtain ⟨T, hT, _⟩ := existsUnique_correctorLinearMap hd hε hU hlam ha
  let B := correctorVariationForm hd hε.1 hU hlam ha
  let Q := B.toQuadraticMap.comp T
  refine ⟨T, Q, hT, ?_⟩
  intro p
  have hmin := ((hT p (T p).val).2).mp rfl
  have heq : Q p = correctorEnergy ε U a p :=
    (correctorEnergy_eq_bilinForm hd hε hU hlam ha p hmin.1 hmin.2).symm
  refine ⟨heq, rfl, ?_⟩
  rw [heq]
  exact ⟨correctorEnergy_nonneg p hmin.1 hmin.2,
    correctorEnergy_comparison hd hε hU hlam ha p hmin.1 hmin.2⟩

end

end LongRange
