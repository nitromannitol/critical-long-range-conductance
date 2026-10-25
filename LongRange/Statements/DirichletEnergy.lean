import LongRange.Dirichlet.Proposition

/-!
# convergence of the corrector energy

A statement-preserving wrapper for Proposition 3.3 (`p.dirichlet`).
-/

open MeasureTheory LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- Proposition 3.3 (`p.dirichlet`): `ν(U^ε, p) + ‖φ_p^ε‖²_{H¹_crit} ≤ C|p|²/|ln ε| +
O₁(C|p|²ε^d/|ln ε|) + O₂(C|p|²ε^{d/2})`, with `C = C(d, U, λ)`, for every `ε ∈ (0,1)` and every `p`;
the corrector is any minimizer of (e.nu) (unique by `corrector_wellDefined`). -/

theorem LongRange.Statements.corrector_energy_bound (d : ℕ) (lam : ℝ) (U : Set (Fin d → ℝ))
    (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ p : Fin d → ℝ,
      ∀ φ : Ω → Site d → ℝ, (∀ ω, IsCorrectorMinimizer ε U (a ω) p (φ ω)) →
      ∃ X₁ X₂ : Ω → ℝ, Measurable X₁ ∧ Measurable X₂ ∧
        OsBound P 1 (C * radius p ^ 2 * ε ^ d / |Real.log ε|) X₁ ∧
        OsBound P 2 (C * radius p ^ 2 * ε ^ ((d : ℝ) / 2)) X₂ ∧
        ∀ ω, correctorEnergy ε U (a ω) p + h1CritSq ε (φ ω) ≤
          C * radius p ^ 2 / |Real.log ε| + X₁ ω + X₂ ω :=

by exact LongRange.corrector_energy_bound d lam U hU
