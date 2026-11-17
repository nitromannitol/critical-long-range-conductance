import LongRange.HeatKernel.CriticalSubordinateUpper
import LongRange.HeatKernel.CriticalEnergyComparison

/-!
# Comparison with the subordinated lattice kernel

A lower critical jump bound dominates the subordinated reference kernel.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The subordinate lattice kernel is dominated by any kernel with a critical lower bound. -/
theorem weightedLattice_subordinate_le_of_lower {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) (k : Site d → Site d → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1)
    (hlower : ∀ x y, ENNReal.ofReal (C⁻¹ /
      (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
        quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) :
    ∃ D : ℝ, 0 < D ∧ ∀ x y,
      (criticalSubordinateDensity (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) x y).toReal ≤ D * (k x y).toReal := by
  obtain ⟨B, hB, hupper⟩ := weightedLattice_criticalSubordinate_volume_profile_upper hd
  let D : ℝ := (B.toReal + 1) * C
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro x y
  let r : ℝ := ((weightedLattice d hd).graph.dist x y : ℝ)
  let v : ℝ := latticeVolumeProfile d r * quadraticScale r
  have hv : 0 < v := by dsimp [v, latticeVolumeProfile, quadraticScale, r]; positivity
  have hfin : k x y < ∞ := by
    have h := ENNReal.le_tsum (f := k x) y
    rw [hk x] at h
    exact lt_of_le_of_lt h ENNReal.one_lt_top
  have hlow := ENNReal.toReal_mono hfin.ne (hlower x y)
  have hlow' : C⁻¹ / v ≤ (k x y).toReal := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ C⁻¹ / v), v, r] using hlow
  have htop : B * ENNReal.ofReal (1 / (quadraticScale r * latticeVolumeProfile d r)) ≠ ∞ :=
    (ENNReal.mul_lt_top hB ENNReal.ofReal_lt_top).ne
  have hscale : 0 < quadraticScale r := by dsimp [quadraticScale, r]; positivity
  have hvolume : 0 < latticeVolumeProfile d r := by
    dsimp [latticeVolumeProfile, r]
    positivity
  have hu := ENNReal.toReal_mono htop (hupper x y)
  have hu' : (criticalSubordinateDensity (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) x y).toReal ≤ B.toReal / v := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 1 / (quadraticScale r * latticeVolumeProfile d r))] at hu
    simpa only [v, mul_comm, div_eq_mul_inv, one_mul] using hu
  have hc : 1 / v ≤ C * (k x y).toReal := by
    have h := mul_le_mul_of_nonneg_left hlow' hC.le
    convert h using 1
    field_simp
  calc
    _ ≤ B.toReal / v := hu'
    _ ≤ (B.toReal + 1) * (1 / v) := by
      have hi : 0 ≤ v⁻¹ := by positivity
      rw [div_eq_mul_inv, one_div]
      nlinarith
    _ ≤ D * (k x y).toReal := by
      have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ B.toReal + 1 by positivity)
      simpa only [D, mul_assoc] using h

end LatticeProb.Graph.LongRangeKernel
