import LongRange.Poincare.SingleScale

/-!
# single-scale estimate

A statement-preserving wrapper for Lemma 4.2 (`l.single.scale`).
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- Lemma 4.2 (`l.single.scale`): one triadic sup-norm shell of the critical kernel controls
the discrete `L²` norm of a function vanishing outside the domain. -/

theorem LongRange.Statements.single_scale_estimate (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Fin d → ℝ), IsOpen U → Bornology.IsBounded U →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ k : ℕ, ε * 3 ^ k ≤ euclideanDiam U →
      ∀ h : Site d → ℝ, SupportedIn ε U h →
        l2NormSq ε U h ≤ C * euclideanDiam U ^ 2 * ε ^ (2 * d) *
          ∑' x : Site d × Site d,
            if ε * 3 ^ k ≤ ‖physical ε x.2‖ ∧ ‖physical ε x.2‖ < ε * 3 ^ (k + 1) then
              jumpKernel (physical ε x.2) * (h (x.1 + x.2) - h x.1) ^ 2
            else 0 :=

by exact LongRange.single_scale_estimate d
