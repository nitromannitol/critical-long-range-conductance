import LongRange.HeatKernel.RescaledKilled

/-!
# The initially killed physical-volume density of the actual rescaled walk
-/

namespace LongRange.Statements

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

/-- The actual density killed outside `U`, including restriction of the initial point.
The exported survival characterization covers all starting sites and includes time zero. -/

def rescaled_killed_density {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (U : Set (Fin d → ℝ))
    (t : ℝ≥0) (x y : Site d) : ℝ :=
  LongRange.rescaledKilledDensity hd hε hlam a ha U t x y


end

end LongRange.Statements
