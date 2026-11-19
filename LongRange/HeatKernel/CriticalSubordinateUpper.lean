import LongRange.HeatKernel.CriticalQuadraticGaussianUpper
import LongRange.HeatKernel.CriticalSubordinationGaussianSum

/-!
# Upper bound for the quadratic subordinate kernel

A Gaussian estimate at quadratic times and the coefficient sum bound yield
critical-profile decay away from the diagonal.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The quadratic subordinate lattice kernel has critical-profile decay at positive distance. -/
theorem weightedLattice_criticalSubordinate_upper_of_dist_pos {d : ℕ} (hd : 0 < d) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x y,
      1 ≤ (weightedLattice d hd).graph.dist x y →
      criticalSubordinateDensity (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) x y ≤
        B * ENNReal.ofReal (1 / (quadraticScale
          ((weightedLattice d hd).graph.dist x y : ℝ) * latticeVolumeProfile d
          ((weightedLattice d hd).graph.dist x y : ℝ))) := by
  obtain ⟨A, c, hA, hc, hgauss⟩ := weightedLattice_averaged_quadratic_gaussian_upper hd
  let a : ℝ≥0∞ := (∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j))⁻¹
  let K : ℝ := ((d + 3).factorial : ℝ) * (c ^ 2) ^ (d + 3) + 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ha : a < ∞ := by
    apply ENNReal.inv_lt_top.mpr
    have := criticalSubordinationCoefficient_tsum_pos
    have h := ENNReal.ofReal_pos.mpr this
    rw [ENNReal.ofReal_tsum_of_nonneg _ summable_criticalSubordinationCoefficient] at h
    · exact h
    · intro j
      unfold criticalSubordinationCoefficient quadraticScale
      positivity
  refine ⟨a * ENNReal.ofReal (A * K), ENNReal.mul_lt_top ha ENNReal.ofReal_lt_top, ?_⟩
  intro x y hr
  let r := (weightedLattice d hd).graph.dist x y
  let f : ℕ → ℝ := fun j =>
    criticalSubordinationCoefficient j / latticeVolumeProfile d ((j : ℝ) + 1) *
      Real.exp (-((r : ℝ) / ((j : ℝ) + 1) / c) ^ 2)
  have hf0 (j : ℕ) : 0 ≤ f j := by
    dsimp [f, criticalSubordinationCoefficient, quadraticScale, latticeVolumeProfile]
    positivity
  obtain ⟨hfs, hsum⟩ := criticalSubordination_gaussian_sum_le d r hr hc
  change Summable f at hfs
  change (∑' j, f j) ≤ K / ((1 + (r : ℝ)) ^ 2 * latticeVolumeProfile d r) at hsum
  have hterm (j : ℕ) : criticalSubordinationWeight j *
      densityPower (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) (2 * (j + 1) ^ 2) x y ≤
      a * (ENNReal.ofReal A * ENNReal.ofReal (f j)) := by
    have hcoeff : 0 ≤ criticalSubordinationCoefficient j := by
      unfold criticalSubordinationCoefficient quadraticScale
      positivity
    have hv : 0 < latticeVolumeProfile d ((j : ℝ) + 1) := by
      unfold latticeVolumeProfile
      positivity
    calc
      _ ≤ a * (ENNReal.ofReal (criticalSubordinationCoefficient j) * ENNReal.ofReal
          (A / latticeVolumeProfile d ((j : ℝ) + 1) *
            Real.exp (-((r : ℝ) / ((j : ℝ) + 1) / c) ^ 2))) := by
        dsimp [criticalSubordinationWeight, a, r]
        rw [mul_assoc]
        gcongr
        exact hgauss x y j
      _ = _ := by
        rw [← ENNReal.ofReal_mul hcoeff, ← ENNReal.ofReal_mul hA.le]
        congr 1
        apply congrArg ENNReal.ofReal
        dsimp [f]
        field_simp
  calc
    _ ≤ ∑' j, a * (ENNReal.ofReal A * ENNReal.ofReal (f j)) := by
      exact ENNReal.tsum_le_tsum hterm
    _ = a * (ENNReal.ofReal A * ENNReal.ofReal (∑' j, f j)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
    _ ≤ a * (ENNReal.ofReal A * ENNReal.ofReal
        (K / ((1 + (r : ℝ)) ^ 2 * latticeVolumeProfile d r))) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA.le, mul_assoc,
        ← ENNReal.ofReal_mul (mul_nonneg hA.le hK)]
      congr 1
      apply congrArg ENNReal.ofReal
      dsimp [quadraticScale, r]
      ring

/-- The quadratic subordinate lattice kernel has critical-profile decay. -/
theorem weightedLattice_criticalSubordinate_volume_profile_upper {d : ℕ} (hd : 0 < d) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x y,
      criticalSubordinateDensity (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) x y ≤
        B * ENNReal.ofReal (1 / (quadraticScale
          ((weightedLattice d hd).graph.dist x y : ℝ) * latticeVolumeProfile d
          ((weightedLattice d hd).graph.dist x y : ℝ))) := by
  obtain ⟨B, hB, hupper⟩ := weightedLattice_criticalSubordinate_upper_of_dist_pos hd
  have hm : ∀ z, (weightedLattice d hd).mass z ≠ 0 := by
    intro z
    rw [weightedLattice_mass]
    exact one_ne_zero
  have hmarkov := criticalSubordinateDensity_isMarkov (weightedLattice d hd).mass hm _
    (averagedDensity_isMarkov (weightedLattice d hd).mass hm _ (weightedLattice_isMarkovDensity hd))
  have hle (x y : Site d) : criticalSubordinateDensity (weightedLattice d hd).mass
      (averagedDensity (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity) x y ≤ 1 := by
    have h := ENNReal.le_tsum (f := fun z => criticalSubordinateDensity
      (weightedLattice d hd).mass (averagedDensity (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity) x z * ((weightedLattice d hd).mass z : ℝ≥0∞)) y
    rw [hmarkov x] at h
    simpa [weightedLattice_mass] using h
  refine ⟨B + 1, ENNReal.add_lt_top.mpr ⟨hB, ENNReal.one_lt_top⟩, ?_⟩
  intro x y
  by_cases hdist : (weightedLattice d hd).graph.dist x y = 0
  · simpa [hdist, quadraticScale, latticeVolumeProfile] using
      (hle x y).trans (show (1 : ℝ≥0∞) ≤ B + 1 by simp)
  · have hp : 1 ≤ (weightedLattice d hd).graph.dist x y := by omega
    exact (hupper x y hp).trans (by gcongr; exact le_add_right le_rfl)

end LatticeProb.Graph.LongRangeKernel
