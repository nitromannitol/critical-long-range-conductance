import LongRange.Poincare.Inequality

/-!
# Poincaré inequality

A statement-preserving wrapper for Proposition 4.1 (`p.poincare`), with the constant uniform
over domains of bounded diameter.
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- Proposition 4.1 (`p.poincare`): the critical seminorm controls the discrete `L²` norm of a
function vanishing outside a bounded open domain, with `C = C(d, diam U)`. -/

theorem LongRange.Statements.poincare (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Fin d → ℝ), IsOpen U → Bornology.IsBounded U →
      euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ h : Site d → ℝ, SupportedIn ε U h → l2NormSq ε U h ≤ C * h1CritSq ε h :=

by exact LongRange.poincare d hd R
