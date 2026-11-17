import LongRange.HeatKernel.CriticalSubordinationSmallScale

/-!
# Gaussian sum for quadratic subordination

The small-scale Gaussian bound and the coefficient tail combine into a
critical-profile bound for the full quadratic subordination series.
-/

namespace LatticeProb.Graph.LongRangeKernel

/-- The full Gaussian majorant is summable and bounded by the critical profile. -/
theorem criticalSubordination_gaussian_sum_le (d r : ℕ) {c : ℝ}
    (hr : 1 ≤ r) (hc : 0 < c) :
    let f : ℕ → ℝ := fun j =>
      criticalSubordinationCoefficient j / latticeVolumeProfile d ((j : ℝ) + 1) *
        Real.exp (-((r : ℝ) / ((j : ℝ) + 1) / c) ^ 2)
    Summable f ∧ (∑' j, f j) ≤
      (((d + 3).factorial : ℝ) * (c ^ 2) ^ (d + 3) + 2) /
        ((1 + (r : ℝ)) ^ 2 * latticeVolumeProfile d r) := by
  let f : ℕ → ℝ := fun j =>
    criticalSubordinationCoefficient j / latticeVolumeProfile d ((j : ℝ) + 1) *
      Real.exp (-((r : ℝ) / ((j : ℝ) + 1) / c) ^ 2)
  let g : ℕ → ℝ := fun j =>
    criticalSubordinationCoefficient j / latticeVolumeProfile d ((j : ℝ) + 1)
  let K : ℝ := ((d + 3).factorial : ℝ) * (c ^ 2) ^ (d + 3)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hg0 (j : ℕ) : 0 ≤ g j := by
    dsimp [g, criticalSubordinationCoefficient, quadraticScale, latticeVolumeProfile]
    positivity
  have hg_le (j : ℕ) : g j ≤ criticalSubordinationCoefficient j := by
    dsimp [g]
    have hv : 1 ≤ latticeVolumeProfile d ((j : ℝ) + 1) := by
      unfold latticeVolumeProfile
      exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    exact div_le_self (by unfold criticalSubordinationCoefficient quadraticScale; positivity) hv
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hg_le
    summable_criticalSubordinationCoefficient
  have hf0 (j : ℕ) : 0 ≤ f j := by
    change 0 ≤ g j * Real.exp _
    exact mul_nonneg (hg0 j) (Real.exp_nonneg _)
  have hf_le (j : ℕ) : f j ≤ g j := by
    dsimp [f, g]
    apply mul_le_of_le_one_right (hg0 j)
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (sq_nonneg _)
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hf_le hgs
  have hsmall (j : ℕ) (hj : j ∈ Finset.range r) :
      f j ≤ K / ((r : ℝ) * (1 + r) ^ 2 * (1 + r) ^ d) := by
    have hjr : (j : ℝ) + 1 ≤ r := by
      exact_mod_cast (show j + 1 ≤ r by simpa using Finset.mem_range.mp hj)
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    have h := quadraticScale_gaussian_term_le d hj1 hjr hc
    convert h using 1
    · dsimp [f, criticalSubordinationCoefficient, quadraticScale, latticeVolumeProfile]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have hfinite : (∑ j ∈ Finset.range r, f j) ≤
      K / ((1 + (r : ℝ)) ^ 2 * (1 + r) ^ d) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range r,
          K / ((r : ℝ) * (1 + r) ^ 2 * (1 + r) ^ d) := Finset.sum_le_sum hsmall
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
  have htail : (∑' j, f (j + r)) ≤
      (1 / (2 * (r : ℝ) ^ 2)) / latticeVolumeProfile d r := by
    have hcomp : (∑' j, f (j + r)) ≤ ∑' j, g (j + r) :=
      (hfs.comp_injective (fun _ _ h => by omega)).tsum_le_tsum
        (fun j => hf_le (j + r)) (hgs.comp_injective (fun _ _ h => by omega))
    apply hcomp.trans
    simpa [g, Nat.cast_add, Nat.cast_one] using criticalSubordinationCoefficient_volume_tail_le d hr
  have htail' : (1 / (2 * (r : ℝ) ^ 2)) / latticeVolumeProfile d r ≤
      2 / ((1 + (r : ℝ)) ^ 2 * latticeVolumeProfile d r) := by
    have hv : 0 < latticeVolumeProfile d r := by unfold latticeVolumeProfile; positivity
    have hnum : 1 / (2 * (r : ℝ) ^ 2) ≤ 2 / (1 + (r : ℝ)) ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [sq_nonneg ((r : ℝ) - 1)]
    have h := div_le_div_of_nonneg_right hnum hv.le
    simpa only [div_div] using h
  refine ⟨hfs, ?_⟩
  rw [← hfs.sum_add_tsum_nat_add r]
  have hsum := add_le_add hfinite (htail.trans htail')
  simpa [K, latticeVolumeProfile, add_div] using hsum

end LatticeProb.Graph.LongRangeKernel
