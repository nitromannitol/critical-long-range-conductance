import Mathlib

/-! # Independent Site vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LatticeProb

variable {d : ℕ}

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- A coordinate unit vector of the integer lattice is nonzero. -/
theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

end LatticeProb
end

end LongRangeAudit.QuenchedInvariance
