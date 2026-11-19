import LongRange.HeatKernel.CriticalBinomialConcentration
import LongRange.HeatKernel.CriticalGaussianLower

/-!
# Gaussian lower bound for the averaged lattice walk

The central mass of the binomial mixture yields the Gaussian lower bound for
the averaged nearest-neighbour walk.
-/

open scoped ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The averaged lattice walk satisfies a Gaussian lower bound at reachable distances. -/
theorem weightedLattice_averaged_gaussian_lower {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      (8⁻¹ * δ) * ENNReal.ofReal
        (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        densityPower (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) n x y := by
  obtain ⟨c, hc, hbound⟩ := weightedLattice_averaged_gaussian_lower_of_central_mass hd
  obtain ⟨δ, hδ, hmass⟩ := central_binomial_mass_uniform
  refine ⟨c, hc, δ, hδ, ?_⟩
  intro x y n hn hdist
  apply hbound x y n hn hdist (Finset.Icc (n / 4) (3 * n / 4)) δ
  · intro k hk
    exact Finset.mem_Icc.mp hk
  · exact hmass n

end LatticeProb.Graph.LongRangeKernel
