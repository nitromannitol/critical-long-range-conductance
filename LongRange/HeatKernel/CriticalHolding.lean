import LongRange.Support.Graph.LongRangeKernel.Lattice
import LongRange.Support.Graph.LongRangeKernel.CriticalScale

/-!
# Holding and two-step kernel bounds

The diagonal part of the critical jump comparison provides the uniform holding
bound used in the proof of Murugan and Saloff-Coste, Theorem 3.2.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

/-- The critical comparison at zero gives a uniform diagonal lower bound. -/
theorem lattice_critical_holding {d : ℕ} (C : ℝ) (k : Site d → Site d → ℝ≥0∞)
    (h : ∀ x y,
      ENNReal.ofReal (C⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
        quadraticScale ((lattice d).dist x y))) ≤ k x y ∧
      k x y ≤ ENNReal.ofReal (C / (latticeVolumeProfile d ((lattice d).dist x y) *
        quadraticScale ((lattice d).dist x y)))) :
    ∀ x, ENNReal.ofReal C⁻¹ ≤ k x x := by
  intro x
  simpa [SimpleGraph.dist_self, latticeVolumeProfile, quadraticScale] using (h x x).1

/-- The two-step density dominates the path that holds at its destination. -/
theorem lattice_densityPower_two_ge {d : ℕ} (hd : 0 < d)
    (k : Site d → Site d → ℝ≥0∞) (x y : Site d) :
    k x y * k y y ≤ densityPower (weightedLattice d hd).mass k 2 x y := by
  classical
  have h : densityPower (weightedLattice d hd).mass k 1 y y = k y y := by
    simp [densityPower, identityDensity, weightedLattice_mass]
  calc
    k x y * k y y = k x y * densityPower (weightedLattice d hd).mass k 1 y y *
        ((weightedLattice d hd).mass y : ℝ≥0∞) := by simp [h, weightedLattice_mass]
    _ ≤ densityPower (weightedLattice d hd).mass k 2 x y :=
      ENNReal.le_tsum (f := fun z => k x z *
        densityPower (weightedLattice d hd).mass k 1 z y *
        ((weightedLattice d hd).mass z : ℝ≥0∞)) y

/-- A uniform holding probability transfers the kernel to its two-step density. -/
theorem lattice_densityPower_two_ge_of_holding {d : ℕ} (hd : 0 < d)
    (k : Site d → Site d → ℝ≥0∞) (α : ℝ≥0∞)
    (hα : ∀ x, α ≤ k x x) (x y : Site d) :
    α * k x y ≤ densityPower (weightedLattice d hd).mass k 2 x y := by
  calc
    α * k x y ≤ k y y * k x y := by gcongr; exact hα y
    _ = k x y * k y y := mul_comm _ _
    _ ≤ densityPower (weightedLattice d hd).mass k 2 x y :=
      lattice_densityPower_two_ge hd k x y

/-- Holding bounds the one-step energy by the two-step energy. -/
theorem lattice_energy_le_two_step {d : ℕ} (hd : 0 < d)
    (k : Site d → Site d → ℝ≥0∞) (α : ℝ≥0∞)
    (hα : ∀ x, α ≤ k x x) (f : Site d → ℝ) :
    α * (∑' x, ∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) ≤
      ∑' x, ∑' y, densityPower (weightedLattice d hd).mass k 2 x y *
        ENNReal.ofReal ((f x - f y) ^ 2) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro y
  rw [← mul_assoc]
  gcongr
  exact lattice_densityPower_two_ge_of_holding hd k α hα x y

end LatticeProb.Graph.LongRangeKernel
