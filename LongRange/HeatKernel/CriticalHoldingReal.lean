import LongRange.HeatKernel.CriticalEnergyReal
import LongRange.HeatKernel.CriticalHolding

/-!
# Holding comparison for real energies

A diagonal lower bound compares the real Dirichlet energies of a symmetric
Markov kernel and its two-step density on the lattice.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

/-- A holding probability compares the real one-step and two-step energies. -/
theorem lattice_real_energy_le_two_step {d : ℕ} (hd : 0 < d)
    (k : Site d → Site d → ℝ≥0∞) (hk : ∀ x, ∑' y, k x y = 1)
    (hsym : ∀ x y, k x y = k y x) (α : ℝ) (hα : 0 ≤ α)
    (hhold : ∀ x, ENNReal.ofReal α ≤ k x x) (f : Site d → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    α * realKernelEnergy k f ≤
      realKernelEnergy (densityPower (weightedLattice d hd).mass k 2) f := by
  let m := (weightedLattice d hd).mass
  have hm (x : Site d) : m x ≠ 0 := by simp [m, weightedLattice_mass]
  have hk' : IsMarkovDensity m k := by
    intro x
    simpa only [m, weightedLattice_mass, ENNReal.coe_one, mul_one] using hk x
  have hp : ∀ x, ∑' y, densityPower m k 2 x y = 1 := by
    intro x
    simpa only [m, weightedLattice_mass, ENNReal.coe_one, mul_one] using
      densityPower_isMarkov m hm k hk' 2 x
  have hs : ∀ x y, densityPower m k 2 x y = densityPower m k 2 y x :=
    densityPower_symmetric m hm k hsym 2
  have hfin := symmetric_markov_energy_lt_top (densityPower m k 2) hp hs f hf
  have hcomp := lattice_energy_le_two_step hd k (ENNReal.ofReal α) hhold f
  have hreal := (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt hcomp hfin)) hfin.ne).2 hcomp
  rw [realKernelEnergy_eq_toReal k hk hsym f hf,
    realKernelEnergy_eq_toReal (densityPower m k 2) hp hs f hf]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα] at hreal
  nlinarith

end LatticeProb.Graph.LongRangeKernel
