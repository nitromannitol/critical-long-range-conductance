import LongRange.Appendix.LatticeCount

/-!
# Finite support of admissible corrector variations

A bounded physical domain contains finitely many positively scaled lattice sites.
Every admissible variation therefore has finite support.
-/

namespace LongRange

open LatticeProb

/-- Every function supported in a bounded physical domain has finite lattice support. -/
theorem SupportedIn.hasFiniteSupport {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {φ : Site d → ℝ}
    (hφ : SupportedIn ε U φ) : φ.HasFiniteSupport := by
  apply (latticeSet_finite hε hU).subset
  intro q hq
  by_contra hnot
  exact hq (hφ q hnot)

end LongRange
