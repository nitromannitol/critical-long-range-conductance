import LongRange.HeatKernel.CriticalDiagonal
import LongRange.Support.Graph.LongRangeKernel.CriticalVolume

/-!
# Critical diagonal bound in volume form

The logarithmic bound gives the even-kernel supremum estimate at the critical inverse scale.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The lattice even-kernel supremum is bounded by inverse critical volume. -/
theorem weightedLattice_evenKernelSup_le {d : ℕ} (hd : 0 < d)
    (Cφ : ℝ) (hCφ : 0 < Cφ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Site d → Site d → ℝ≥0∞,
      IsMarkovDensity (weightedLattice d hd).mass k → (∀ x y, k x y = k y x) →
      (∀ x y,
        ENNReal.ofReal (Cφ⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
          quadraticScale ((lattice d).dist x y))) ≤ k x y ∧
        k x y ≤ ENNReal.ofReal (Cφ / (latticeVolumeProfile d ((lattice d).dist x y) *
          quadraticScale ((lattice d).dist x y)))) →
      ∀ n : ℕ, evenKernelSup (weightedLattice d hd).mass k n ≤
        ENNReal.ofReal (C / latticeVolumeProfile d (criticalInverse n)) := by
  obtain ⟨K, hK, hk⟩ := weightedLattice_critical_diagonal hd Cφ hCφ
  obtain ⟨c, C, hc, hC, hv⟩ := latticeVolume_criticalInverse_comparison d
  refine ⟨K * C, mul_pos hK hC, ?_⟩
  intro k hmark hsym hprofile n
  have hmass : (weightedLattice d hd).mass = fun _ => 1 := funext (weightedLattice_mass hd)
  have hrow : ∀ x, ∑' y, k x y = 1 := by
    simpa only [hmass, IsMarkovDensity, ENNReal.coe_one, mul_one] using hmark
  have hlower : ∀ x y, ENNReal.ofReal (Cφ⁻¹ /
      (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
        quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y := by
    intro x y
    exact (hprofile x y).1
  have hp : ∀ x, ∑' y, densityPower (fun _ => 1) k (2 * n) x y = 1 := by
    have h := densityPower_isMarkov (fun _ : Site d => 1) (by simp) k
      (by simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using hrow) (2 * n)
    simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using h
  have hlog : 0 ≤ Real.log (2 + (n : ℝ)) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hbase : 0 < 1 + (n : ℝ) * Real.log (2 + n) := by positivity
  have hpow : 0 < (1 + (n : ℝ) * Real.log (2 + n)) ^ ((d : ℝ) / 2) :=
    Real.rpow_pos_of_pos hbase _
  have hV := hv n (Nat.cast_nonneg n)
  have hVpos : 0 < latticeVolumeProfile d (criticalInverse n) :=
    (mul_pos hc hpow).trans_le hV.1
  rw [evenKernelSup, hmass]
  apply iSup_le
  intro x
  have hfinite : densityPower (fun _ => 1) k (2 * n) x x ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt ((ENNReal.le_tsum x).trans_eq (hp x)) ENNReal.one_lt_top)
  rw [← ENNReal.ofReal_toReal hfinite]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ K * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) :=
      hk k hrow hsym hlower n x
    _ = K / (1 + (n : ℝ) * Real.log (2 + n)) ^ ((d : ℝ) / 2) := by
      simp only [Real.rpow_neg hbase.le, div_eq_mul_inv]
    _ ≤ K * C / latticeVolumeProfile d (criticalInverse n) := by
      apply (div_le_div_iff₀ hpow hVpos).2
      nlinarith [mul_le_mul_of_nonneg_left hV.2 hK.le]

end LatticeProb.Graph.LongRangeKernel
