import LongRangeHeat.Defs

/-!
# Initial value of the lattice heat series

The exponential series has the prescribed initial value at time zero.
-/

namespace LongRangeHeat

open LatticeProb.Euclidean.Lattice

/-- The lattice heat series starts from the restriction of the initial data. -/
theorem latticeHeat_zero {d : ℕ} (ε : ℝ) (a : LongRange.Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) : latticeHeat ε a f 0 = restrict ε f := by
  funext q
  unfold latticeHeat
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

end LongRangeHeat
