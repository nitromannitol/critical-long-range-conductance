import LongRange.Corrector.EnergyQuadraticMap

/-!
# The supported corrector and its negative-infimum energy share linear and quadratic maps.

-/

namespace LongRange.Statements

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The supported corrector and its negative-infimum energy share linear and quadratic maps. -/

theorem corrector_linear_quadratic (hd : 1 ≤ d) {ε : ℝ}
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
        Q p ≤ lam⁻¹ / 2 * h1CritSq ε (T p).val :=

by exact LongRange.exists_corrector_linear_quadratic hd hε hU hlam ha

end

end LongRange.Statements
