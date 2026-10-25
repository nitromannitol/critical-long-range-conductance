import LongRange.HeatKernel.RescaledKilled

/-!
# The full physical-volume density of the actual rescaled walk
-/

namespace LongRange.Statements

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

/-- The actual full transition density with physical atom volume `ε ^ d`.
Its complete actual-position characterization is exported with the common kernel bound. -/

def rescaled_density {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (t : ℝ≥0) (x y : Site d) : ℝ :=
  LongRange.rescaledDensity hd hε hlam a ha t x y


end

end LongRange.Statements
