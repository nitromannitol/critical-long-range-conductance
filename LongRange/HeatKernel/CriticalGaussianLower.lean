import LongRange.HeatKernel.CriticalBinomialWindow
import LongRange.Support.Graph.LongRangeKernel.LatticeGaussianLower

/-!
# Gaussian lower bounds for the averaged lattice walk

The Gaussian lower bound for adjacent nearest-neighbour powers is uniform
across the times appearing in the binomial mixture.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

/-- The Gaussian lower bound for adjacent powers is uniform from time `n` to `2n`. -/
theorem weightedLattice_gaussian_lower_uniform {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y (n k : ℕ), 1 ≤ n → k ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal
        (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat (n + k) x y +
          (weightedLattice d hd).heat (n + k + 1) x y := by
  obtain ⟨a, ha, hgauss⟩ := weightedLattice_gaussian_lower hd
  let c := a / (2 : ℝ) ^ d
  have hc : 0 < c := by dsimp [c]; positivity
  have hca : c ≤ a := by
    dsimp [c]
    exact div_le_self ha.le (one_le_pow₀ (by norm_num))
  refine ⟨c, hc, ?_⟩
  intro x y n k hn hk hdist
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnkR : ((n + k : ℕ) : ℝ) ≤ 2 * n := by
    exact_mod_cast (show n + k ≤ 2 * n by omega)
  have ht : 0 ≤ (n : ℝ) ^ (1 / (2 : ℝ)) := Real.rpow_nonneg hnR.le _
  have hroot : ((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ)) ≤
      2 * (n : ℝ) ^ (1 / (2 : ℝ)) := by
    calc
      _ ≤ (2 * (n : ℝ)) ^ (1 / (2 : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hnkR (by norm_num)
      _ = (2 : ℝ) ^ (1 / (2 : ℝ)) * (n : ℝ) ^ (1 / (2 : ℝ)) :=
        Real.mul_rpow (by norm_num) hnR.le
      _ ≤ 2 * (n : ℝ) ^ (1 / (2 : ℝ)) := by
        gcongr
        exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hv : latticeVolumeProfile d (((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ))) ≤
      (2 : ℝ) ^ d * latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    calc
      _ ≤ (2 * (1 + (n : ℝ) ^ (1 / (2 : ℝ)))) ^ d :=
        pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = _ := by rw [mul_pow]
  have hvpos : 0 < latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    positivity
  have hvpos' : 0 < latticeVolumeProfile d (((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ))) := by
    unfold latticeVolumeProfile
    positivity
  have hpre : c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) ≤
      a / latticeVolumeProfile d (((n + k : ℕ) : ℝ) ^ (1 / (2 : ℝ))) := by
    apply (div_le_div_iff₀ hvpos hvpos').2
    dsimp [c]
    have h := mul_le_mul_of_nonneg_left hv (div_nonneg ha.le (by positivity : 0 ≤ (2 : ℝ) ^ d))
    have hp : (2 : ℝ) ^ d ≠ 0 := by positivity
    field_simp at h ⊢
    nlinarith
  have hexp : -(((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 / (c * n)) ≤
      -(((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 / (a * ((n + k : ℕ) : ℝ))) := by
    apply neg_le_neg
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have hnkle : (n : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast (show n ≤ n + k by omega)
    nlinarith
  have h := hgauss x y (n + k) (by omega) (by omega)
  apply (ENNReal.ofReal_le_ofReal ?_).trans h
  norm_num only [Real.rpow_two, sub_self, sub_zero, one_div_one, Real.rpow_one] at ⊢
  exact mul_le_mul hpre (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (div_nonneg ha.le hvpos'.le)

/-- A positive central binomial mass transfers the Gaussian lower bound to the averaged walk. -/
theorem weightedLattice_averaged_gaussian_lower_of_central_mass {d : ℕ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ∀ (s : Finset ℕ) (δ : ℝ≥0∞),
      (∀ k ∈ s, n / 4 ≤ k ∧ k ≤ 3 * n / 4) →
      δ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * ∑ k ∈ s, (n.choose k : ℝ≥0∞) →
      (8⁻¹ * δ) * ENNReal.ofReal
        (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        densityPower (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) n x y := by
  obtain ⟨c, hc, hgauss⟩ := weightedLattice_gaussian_lower_uniform hd
  refine ⟨c, hc, ?_⟩
  intro x y n hn hdist s δ hs hδ
  have hm : ∀ z, (weightedLattice d hd).mass z ≠ 0 := by
    intro z
    rw [weightedLattice_mass]
    exact one_ne_zero
  apply densityPower_averaged_ge_of_central_mass _ hm _ (by omega) s hs x y δ _ hδ
  intro k hk
  have h := hgauss x y n k hn (by have := (hs k hk).2; omega) hdist
  change _ ≤ densityPower (weightedLattice d hd).mass
    (weightedLattice d hd).referenceDensity (n + k) x y +
      densityPower (weightedLattice d hd).mass
        (weightedLattice d hd).referenceDensity (n + (k + 1)) x y at h ⊢
  exact h

end LatticeProb.Graph.LongRangeKernel
