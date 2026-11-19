import LongRange.HeatKernel.CriticalBinomial
import LongRange.Support.Graph.LongRangeKernel.LatticeDistance

/-!
# Gaussian upper bound for the averaged lattice walk

The binomial mixture transfers the Gaussian upper bound of the nearest-neighbour
walk to the averaged walk, as in Lemma 2.2 of Murugan and Saloff-Coste.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

/-- The averaged nearest-neighbour density satisfies the Gaussian upper bound. -/
theorem weightedLattice_averaged_gaussian_upper {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y (n : ℕ), 1 ≤ n →
      densityPower (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) n x y ≤ ENNReal.ofReal
        (C / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (C * n)) ^ (1 / ((2 : ℝ) - 1))))) := by
  obtain ⟨A, hA, hupper⟩ := weightedLattice_gaussian_upper hd
  refine ⟨2 * A, by positivity, ?_⟩
  intro x y n hn
  have hm : ∀ z, (weightedLattice d hd).mass z ≠ 0 := by
    intro z
    rw [weightedLattice_mass]
    exact one_ne_zero
  apply densityPower_averaged_le_of_le _ hm
  intro k hk
  have hnk : 1 ≤ n + k := by omega
  have h := hupper x y (n + k) hnk
  change densityPower (weightedLattice d hd).mass
    (weightedLattice d hd).referenceDensity (n + k) x y ≤ _ at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  norm_num only [Real.rpow_two, sub_self, sub_zero, one_div_one, Real.rpow_one]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmax : ((n + k : ℕ) : ℝ) ≤ 2 * n := by exact_mod_cast (show n + k ≤ 2 * n by omega)
  have hroot : (n : ℝ) ^ (1 / (2 : ℝ)) ≤ ((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hnR.le (by exact_mod_cast (show n ≤ n + k by omega)) (by norm_num)
  have hv : latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) ≤
      latticeVolumeProfile d (((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hvpos : 0 < latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    positivity
  have hpre : A / latticeVolumeProfile d (((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ))) ≤
      (2 * A) / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) := by
    calc
      _ ≤ A / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) :=
        div_le_div_of_nonneg_left hA.le hvpos hv
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hvpos.le
  have hexp : -(((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 /
      (A * ((n + k : ℕ) : ℝ))) ≤ -(((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 /
      (2 * A * n)) := by
    apply neg_le_neg
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hmax hA.le
    nlinarith
  exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (div_nonneg (by positivity) hvpos.le)

end LatticeProb.Graph.LongRangeKernel
