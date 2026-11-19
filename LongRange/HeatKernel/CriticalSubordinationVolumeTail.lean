import LongRange.HeatKernel.CriticalSubordinationTail
import LongRange.Support.Graph.LongRangeKernel.LatticeVolume

/-!
# Volume-weighted tail of quadratic subordination

Monotonicity of lattice volume combines with the coefficient tail bound.
-/

namespace LatticeProb.Graph.LongRangeKernel

/-- The large-scale sum in the subordinate kernel has the critical volume decay. -/
theorem criticalSubordinationCoefficient_volume_tail_le (d : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (∑' j : ℕ, criticalSubordinationCoefficient (j + r) /
      latticeVolumeProfile d ((j + r + 1 : ℕ) : ℝ)) ≤
      (1 / (2 * (r : ℝ) ^ 2)) / latticeVolumeProfile d r := by
  let a : ℕ → ℝ := fun j => criticalSubordinationCoefficient (j + r)
  let v : ℝ := latticeVolumeProfile d r
  have ha : Summable a :=
    summable_criticalSubordinationCoefficient.comp_injective (fun _ _ h => by omega)
  have ha0 (j : ℕ) : 0 ≤ a j := by
    dsimp [a, criticalSubordinationCoefficient, quadraticScale]
    positivity
  have hv : 0 < v := by dsimp [v, latticeVolumeProfile]; positivity
  have hvj (j : ℕ) : v ≤ latticeVolumeProfile d ((j + r + 1 : ℕ) : ℝ) := by
    dsimp [v, latticeVolumeProfile]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hbound (j : ℕ) : a j / latticeVolumeProfile d ((j + r + 1 : ℕ) : ℝ) ≤ a j / v :=
    div_le_div_of_nonneg_left (ha0 j) hv (hvj j)
  have hsum : Summable (fun j : ℕ => a j / latticeVolumeProfile d ((j + r + 1 : ℕ) : ℝ)) := by
    apply Summable.of_nonneg_of_le _ hbound (ha.div_const v)
    intro j
    apply div_nonneg (ha0 j)
    exact (hv.trans_le (hvj j)).le
  calc
    _ ≤ ∑' j, a j / v := hsum.tsum_le_tsum hbound (ha.div_const v)
    _ = (∑' j, a j) / v := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right (criticalSubordinationCoefficient_tail_le hr) hv.le

end LatticeProb.Graph.LongRangeKernel
