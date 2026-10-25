import LongRange.Dirichlet.SolenoidalEquivalence

/-!
# Solenoidality and supported tests

Absolute local nonzero-row convergence makes the source divergence condition equivalent
to vanishing of the unnormalized pairing against every supported real test.
-/

namespace LongRange.Statements

open LatticeProb LatticeProb.Euclidean.Lattice

/-- On a bounded physical domain, the nonzero-displacement divergence vanishes exactly
when every supported source test has zero pairing. -/

theorem solenoidal_equivalence {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (g : Site d → Site d → ℝ) (hanti : ∀ x y, g x y = -g y x)
    (hrow : ∀ x ∈ latticeSet ε U,
      Summable (fun z : {z : Site d // z ≠ 0} => g (x + z) x)) :
    (∀ x ∈ latticeSet ε U,
      (∑' z : {z : Site d // z ≠ 0}, g (x + z) x) = 0) ↔
      (∀ w : Site d → ℝ, SupportedIn ε U w →
        (∑' q : Site d × Site d,
          g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) = 0) :=

by
  exact LongRange.solenoidal_nonzero_iff_pairing_eq_zero hε hU g hanti hrow

end LongRange.Statements
