import LongRange.Corrector.MonotonicityLemma

/-!
# monotonicity of the corrector energy

A statement-preserving wrapper for Lemma 5.2 (`l.corrector.monotonicity`), with the constant
depending only on the dimension, the ellipticity constant and a bound on `diam U`.
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- Lemma 5.2 (`l.corrector.monotonicity`): for nested bounded domains `U ⊆ V` with `U` open,
the correctors satisfy `D_a(φ_U) ≤ D_a(φ_V)` and the norm comparison
(e.corrector.monotonicity.norms). -/

theorem LongRange.Statements.corrector_monotonicity (d : ℕ) (hd : 1 ≤ d) (lam R : ℝ)
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ U V : Set (Fin d → ℝ), IsOpen U → Bornology.IsBounded U →
      Bornology.IsBounded V → U ⊆ V → euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (p : Fin d → ℝ) (φU φV : Site d → ℝ),
      IsCorrectorSolution ε U a p φU → IsCorrectorSolution ε V a p φV →
        bilinForm ε a φU φU ≤ bilinForm ε a φV φV ∧
        h1CritSq ε φU + l2NormSq ε U φU ≤ C * (h1CritSq ε φV + l2NormSq ε V φV) :=

by exact LongRange.corrector_monotonicity d hd lam R hlam
