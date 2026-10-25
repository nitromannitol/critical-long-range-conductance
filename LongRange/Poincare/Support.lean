import LongRange.Corrector.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Finite support on a bounded physical domain

A bounded domain contains finitely many points of a lattice with positive spacing.
Consequently, every supported function has a summable square, including the subtype sum
used in the discrete `L²` norm.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The full lattice square sum is summable for a bounded-domain supported function. -/
theorem SupportedIn.summable_sq {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {h : Site d → ℝ}
    (hh : SupportedIn ε U h) : Summable (fun q => h q ^ 2) := by
  apply summable_of_hasFiniteSupport
  apply (hh.hasFiniteSupport hε hU).subset
  intro q hq hz
  apply hq
  change h q ^ 2 = 0
  rw [hz, zero_pow (by decide : 2 ≠ 0)]

/-- The subtype sum defining the discrete `L²` norm is summable. -/
theorem summable_l2NormSq {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (h : Site d → ℝ) :
    Summable (fun q : latticeSet ε U => h q ^ 2) := by
  letI := (latticeSet_finite hε hU).fintype
  exact Summable.of_finite

end

end LongRange
