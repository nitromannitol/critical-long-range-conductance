import LongRange.HeatKernel.CriticalSubordinateLower

/-!
# Polynomial profile for quadratic subordination

The lower bound from a quadratic block has inverse-polynomial decay.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The explicit Gaussian block bound dominates the inverse polynomial profile. -/
theorem quadratic_block_profile_le (d : ℕ) {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 1 ≤ r) :
    (c * Real.exp (-(1 / (2 * c))) / (18 * (4 : ℝ) ^ d)) *
        (1 / r ^ (d + 2)) ≤
      (1 / (18 * r ^ 2)) *
        (c / latticeVolumeProfile d (3 * r) * Real.exp (-(1 / (2 * c)))) := by
  have hrp : 0 < r := by linarith
  have hvp : 0 < latticeVolumeProfile d (3 * r) := by
    unfold latticeVolumeProfile
    positivity
  have hv : latticeVolumeProfile d (3 * r) ≤ (4 : ℝ) ^ d * r ^ d := by
    unfold latticeVolumeProfile
    calc
      (1 + 3 * r) ^ d ≤ (4 * r) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = _ := mul_pow _ _ _
  have hden : 18 * r ^ 2 * latticeVolumeProfile d (3 * r) ≤
      18 * r ^ 2 * ((4 : ℝ) ^ d * r ^ d) := by
    gcongr
  have h := div_le_div_of_nonneg_left (mul_nonneg hc.le (Real.exp_nonneg (-(1 / (2 * c)))))
    (show 0 < 18 * r ^ 2 * latticeVolumeProfile d (3 * r) by positivity) hden
  rw [pow_add]
  convert h using 1 <;> field_simp

/-- The subordinated lattice kernel has an inverse-polynomial lower bound. -/
theorem weightedLattice_criticalSubordinate_polynomial_lower {d : ℕ} (hd : 0 < d) :
    ∃ A : ℝ≥0∞, 0 < A ∧ ∀ x y (r : ℕ), 1 ≤ r →
      (weightedLattice d hd).graph.dist x y ≤ r →
      A * ENNReal.ofReal (1 / (r : ℝ) ^ (d + 2)) ≤
        criticalSubordinateDensity (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) x y := by
  obtain ⟨c, hc, δ, hδ, hblock⟩ := weightedLattice_criticalSubordinate_lower hd
  let a : ℝ≥0∞ := (∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j))⁻¹
  let b : ℝ≥0∞ := 8⁻¹ * δ
  let k : ℝ := c * Real.exp (-(1 / (2 * c))) / (18 * (4 : ℝ) ^ d)
  have ha : 0 < a := by
    apply ENNReal.inv_pos.mpr
    exact ne_of_lt summable_criticalSubordinationCoefficient.tsum_ofReal_lt_top
  have hb : 0 < b := by
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top) hδ.ne'
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨a * b * ENNReal.ofReal k, by positivity, ?_⟩
  intro x y r hr hdist
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hreal := ENNReal.ofReal_le_ofReal (quadratic_block_profile_le d hc hrR)
  have hlower := hblock x y r hr hdist
  calc
    _ = a * b * ENNReal.ofReal (k * (1 / (r : ℝ) ^ (d + 2))) := by
      rw [ENNReal.ofReal_mul hk.le]
      ring
    _ ≤ a * b * ENNReal.ofReal ((1 / (18 * (r : ℝ) ^ 2)) *
        (c / latticeVolumeProfile d (3 * r) * Real.exp (-(1 / (2 * c))))) := by
      gcongr
    _ = (a * ENNReal.ofReal (1 / (18 * (r : ℝ) ^ 2))) *
        (b * ENNReal.ofReal
          (c / latticeVolumeProfile d (3 * r) * Real.exp (-(1 / (2 * c))))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      ring
    _ ≤ _ := hlower

/-- The subordinated kernel dominates the critical lattice jump profile. -/
theorem weightedLattice_criticalSubordinate_jump_lower {d : ℕ} (hd : 0 < d) :
    ∃ A : ℝ≥0∞, 0 < A ∧ ∀ x y,
      A * ENNReal.ofReal
        (1 / (1 + ((weightedLattice d hd).graph.dist x y : ℝ)) ^ (d + 2)) ≤
        criticalSubordinateDensity (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) x y := by
  obtain ⟨A, hA, h⟩ := weightedLattice_criticalSubordinate_polynomial_lower hd
  refine ⟨A, hA, ?_⟩
  intro x y
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
    h x y ((weightedLattice d hd).graph.dist x y + 1) (by omega) (by omega)

end LatticeProb.Graph.LongRangeKernel
