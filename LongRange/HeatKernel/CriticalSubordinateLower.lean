import LongRange.HeatKernel.CriticalAveragedGaussianLower
import LongRange.HeatKernel.CriticalSubordinationBounds

/-!
# Lower bound for quadratic-scale subordination

A Gaussian lower bound on a quadratic block transfers to the subordinated
lattice kernel.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The averaged walk has a common lower bound throughout a quadratic block. -/
theorem weightedLattice_averaged_quadratic_block_lower {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ x y (r j : ℕ), 1 ≤ r →
        (weightedLattice d hd).graph.dist x y ≤ r → r ≤ j + 1 → j + 1 ≤ 2 * r →
        (8⁻¹ * δ) * ENNReal.ofReal
          (c / latticeVolumeProfile d (3 * r) * Real.exp (-(1 / (2 * c)))) ≤
        densityPower (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) (2 * (j + 1) ^ 2) x y := by
  obtain ⟨c, hc, δ, hδ, hgauss⟩ := weightedLattice_averaged_gaussian_lower hd
  refine ⟨c, hc, δ, hδ, ?_⟩
  intro x y r j hr hdist hjlo hjhi
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hjloR : (r : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hjlo
  have hjhiR : (j : ℝ) + 1 ≤ 2 * r := by exact_mod_cast hjhi
  have hdistR : ((weightedLattice d hd).graph.dist x y : ℝ) ≤ r := by exact_mod_cast hdist
  have hnlo : 2 * (r : ℝ) ^ 2 ≤ ((2 * (j + 1) ^ 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg ((j : ℝ) + 1 - r)]
  have hnhi : ((2 * (j + 1) ^ 2 : ℕ) : ℝ) ≤ 8 * (r : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg (2 * (r : ℝ) - ((j : ℝ) + 1))]
  have hroot : ((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ)) ≤ 3 * r := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hvol : latticeVolumeProfile d
      (((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ))) ≤
      latticeVolumeProfile d (3 * r) := by
    unfold latticeVolumeProfile
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hvpos : 0 < latticeVolumeProfile d (3 * r) := by
    unfold latticeVolumeProfile
    positivity
  have hvpos' : 0 < latticeVolumeProfile d
      (((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    positivity
  have hpre : c / latticeVolumeProfile d (3 * r) ≤
      c / latticeVolumeProfile d (((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ))) :=
    div_le_div_of_nonneg_left hc.le hvpos' hvol
  have hdist2 : ((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hdistR 2
  have hexp : - (1 / (2 * c)) ≤
      - (((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 /
        (c * ((2 * (j + 1) ^ 2 : ℕ) : ℝ))) := by
    apply neg_le_neg
    apply (div_le_iff₀ (by positivity)).2
    have heq : (1 / (2 * c)) * (c * ((2 * (j + 1) ^ 2 : ℕ) : ℝ)) =
        ((2 * (j + 1) ^ 2 : ℕ) : ℝ) / 2 := by
      field_simp
    rw [heq]
    linarith
  have hn : 1 ≤ 2 * (j + 1) ^ 2 := by nlinarith
  have hreach : (weightedLattice d hd).graph.dist x y ≤ 2 * (j + 1) ^ 2 := by
    nlinarith
  have h := hgauss x y (2 * (j + 1) ^ 2) hn hreach
  apply le_trans ?_ h
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  norm_num only [Real.rpow_two, sub_self, sub_zero, one_div_one, Real.rpow_one] at ⊢
  exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (div_nonneg hc.le hvpos'.le)

/-- A quadratic block gives a lower bound for the subordinated lattice kernel. -/
theorem weightedLattice_criticalSubordinate_lower {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ x y (r : ℕ), 1 ≤ r → (weightedLattice d hd).graph.dist x y ≤ r →
        ((∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j))⁻¹ *
          ENNReal.ofReal (1 / (18 * (r : ℝ) ^ 2))) *
          ((8⁻¹ * δ) * ENNReal.ofReal
            (c / latticeVolumeProfile d (3 * r) * Real.exp (-(1 / (2 * c))))) ≤
        criticalSubordinateDensity (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) x y := by
  obtain ⟨c, hc, δ, hδ, hblock⟩ := weightedLattice_averaged_quadratic_block_lower hd
  refine ⟨c, hc, δ, hδ, ?_⟩
  intro x y r hr hdist
  apply criticalSubordinateDensity_ge_of_block _ _ _ _ hr
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  apply hblock x y r j hr hdist <;> omega

end LatticeProb.Graph.LongRangeKernel
