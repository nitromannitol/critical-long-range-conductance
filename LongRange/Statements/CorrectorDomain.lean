import LongRange.Dirichlet.Proposition

/-!
# corrector bound on bounded domains

A statement-preserving wrapper for Proposition 5.1 (`p.corrector.domain`).
-/

open MeasureTheory LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- Proposition 5.1 (`p.corrector.domain`): the corrector of slope `e_i` on a bounded open domain
satisfies `‖φ_i‖²_{H¹_crit} + ‖φ_i‖²_{L²} ≤ C/κ_ε + O₁(Cε^d/κ_ε) + O₂(Cε^{d/2})`, with
`C = C(d, λ, U)`. -/

theorem LongRange.Statements.corrector_domain_bound (d : ℕ) (lam : ℝ) (U : Set (Fin d → ℝ))
    (hUo : IsOpen U) (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ i : Fin d,
      ∀ φ : Ω → Site d → ℝ,
      (∀ ω, IsCorrectorSolution ε U (a ω) (Pi.single i 1) (φ ω)) →
      ∃ X₁ X₂ : Ω → ℝ, Measurable X₁ ∧ Measurable X₂ ∧
        OsBound P 1 (C * ε ^ d / kappa d ε) X₁ ∧
        OsBound P 2 (C * ε ^ ((d : ℝ) / 2)) X₂ ∧
        ∀ ω, h1CritSq ε (φ ω) + l2NormSq ε U (φ ω) ≤
          C / kappa d ε + X₁ ω + X₂ ω :=

by exact LongRange.corrector_domain_bound d lam U hUo hU
