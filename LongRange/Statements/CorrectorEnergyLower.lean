import LongRange.Corrector.EnergyLowerBound

/-!
# Positive source-edge variance gives the matching expected corrector energy lower bound.

-/

namespace LongRange.Statements

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section


/-- Positive source-edge variance gives the matching expected corrector energy lower bound. -/

theorem corrector_energy_lower_bound {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ}
    (hA : AssumptionU P lam a) {U : Set (Fin d → ℝ)} (hUo : IsOpen U)
    (hUne : U.Nonempty) (hU : Bornology.IsBounded U)
    (hvar : 0 < Var[fun ω => a ω (baseEdge hA.one_le_dim); P]) :
    ∃ c > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ p : Fin d → ℝ, ∀ ε : ℝ,
      0 < ε → ε < min 1 ε₀ →
        c * radius p ^ 2 / kappa d ε ≤ ∫ ω, correctorEnergy ε U (a ω) p ∂P :=

by exact LongRange.AssumptionU.exists_correctorEnergy_lower_bound hA hUo hUne hU hvar

end

end LongRange.Statements
