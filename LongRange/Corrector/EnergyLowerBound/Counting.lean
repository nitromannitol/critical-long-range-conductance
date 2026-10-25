import LongRange.Appendix.LatticeCount
import LatticeProb.Euclidean.LatticeCountLower

/-!
# A lower lattice count in a nonempty open set

An open set contains a fixed coordinate box. Counting integer intervals in that box gives
a lower bound of order the inverse lattice cell volume. The coordinate box is used only
for topology and counting; the jump kernel and the slope radius remain Euclidean.
-/

namespace LongRange.Corrector.EnergyLowerBound

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- A nonempty bounded open set contains at least a fixed multiple of `ε⁻ᵈ` lattice sites. -/
theorem exists_lattice_count_lower {d : ℕ} {U : Set (Fin d → ℝ)}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hU : Bornology.IsBounded U) :
    ∃ c > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      c ≤ ε ^ d * ((latticeSet ε U).ncard : ℝ) := by
  exact exists_physical_lattice_count_lower hUo hUne hU

end

end LongRange.Corrector.EnergyLowerBound
