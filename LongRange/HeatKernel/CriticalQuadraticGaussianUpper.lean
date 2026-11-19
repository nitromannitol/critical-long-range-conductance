import LongRange.HeatKernel.CriticalGaussianUpper

/-!
# Gaussian upper bound at quadratic times

The averaged nearest-neighbour walk has a Gaussian upper bound in terms of
its quadratic time scale and the corresponding polynomial volume profile.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The averaged walk at quadratic times has Gaussian decay at the spatial scale. -/
theorem weightedLattice_averaged_quadratic_gaussian_upper {d : ℕ} (hd : 0 < d) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ x y (j : ℕ),
      densityPower (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) (2 * (j + 1) ^ 2) x y ≤
        ENNReal.ofReal (A / latticeVolumeProfile d ((j : ℝ) + 1) *
          Real.exp (-(((weightedLattice d hd).graph.dist x y : ℝ) / ((j : ℝ) + 1) / c) ^ 2)) := by
  obtain ⟨A, hA, hupper⟩ := weightedLattice_averaged_gaussian_upper hd
  let c : ℝ := 1 + 2 * A
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : 2 * A ≤ c ^ 2 := by dsimp [c]; nlinarith [sq_nonneg (2 * A)]
  refine ⟨A, c, hA, hc, ?_⟩
  intro x y j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hn : 1 ≤ 2 * (j + 1) ^ 2 := by
    have : 1 ≤ (j + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h := hupper x y (2 * (j + 1) ^ 2) hn
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  norm_num only [Real.rpow_two, sub_self, sub_zero, one_div_one, Real.rpow_one]
  have hroot : (j : ℝ) + 1 ≤
      ((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt hj.le (by positivity)).2
    push_cast
    nlinarith [sq_nonneg ((j : ℝ) + 1)]
  have hvol : latticeVolumeProfile d ((j : ℝ) + 1) ≤ latticeVolumeProfile d
      (((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hv : 0 < latticeVolumeProfile d ((j : ℝ) + 1) := by
    unfold latticeVolumeProfile
    positivity
  have hpre : A / latticeVolumeProfile d
      (((2 * (j + 1) ^ 2 : ℕ) : ℝ) ^ (1 / (2 : ℝ))) ≤
      A / latticeVolumeProfile d ((j : ℝ) + 1) :=
    div_le_div_of_nonneg_left hA.le hv hvol
  have hden : A * ((2 * (j + 1) ^ 2 : ℕ) : ℝ) ≤ (((j : ℝ) + 1) * c) ^ 2 := by
    push_cast
    nlinarith [mul_nonneg (sq_nonneg ((j : ℝ) + 1)) (sub_nonneg.mpr hc2)]
  have hexp : -(((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 /
      (A * ((2 * (j + 1) ^ 2 : ℕ) : ℝ))) ≤
      -(((weightedLattice d hd).graph.dist x y : ℝ) / ((j : ℝ) + 1) / c) ^ 2 := by
    apply neg_le_neg
    rw [div_div, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (div_nonneg hA.le hv.le)

end LatticeProb.Graph.LongRangeKernel
