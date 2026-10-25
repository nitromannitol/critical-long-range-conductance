import LongRange.Poincare.SingleScale
import LongRange.Appendix.Kappa
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Summing disjoint shells and counting scales

The shell energies are nonnegative and have disjoint displacement supports. Scales between
lattice spacing and physical size one supply the logarithmic factor in the normalization.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Different triadic shells have disjoint displacement ranges. -/
theorem shell_disjoint {ε r : ℝ} (hε : 0 < ε) {k l : ℕ}
    (hk : ε * 3 ^ k ≤ r ∧ r < ε * 3 ^ (k + 1))
    (hl : ε * 3 ^ l ≤ r ∧ r < ε * 3 ^ (l + 1)) : k = l := by
  apply le_antisymm
  · by_contra h
    have hp : (3 : ℝ) ^ (l + 1) ≤ 3 ^ k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hm := mul_le_mul_of_nonneg_left hp hε.le
    linarith only [hm, hk.1, hl.2]
  · by_contra h
    have hp : (3 : ℝ) ^ (k + 1) ≤ 3 ^ l :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hm := mul_le_mul_of_nonneg_left hp hε.le
    linarith only [hm, hl.1, hk.2]

/-- The finite sum of shell summands is bounded pointwise by the full energy summand. -/
theorem sum_shellTerm_le {ε : ℝ} (hε : 0 < ε) (h : Site d → ℝ)
    (m : ℕ) (p : Site d × Site d) :
    (∑ k ∈ Finset.range m, shellTerm ε k h p) ≤
      jumpKernel (physical ε p.2) * (h (p.1 + p.2) - h p.1) ^ 2 := by
  classical
  by_cases hex : ∃ k ∈ Finset.range m,
      ε * 3 ^ k ≤ ‖physical ε p.2‖ ∧ ‖physical ε p.2‖ < ε * 3 ^ (k + 1)
  · obtain ⟨k, hk, hkp⟩ := hex
    rw [Finset.sum_eq_single k]
    · exact le_of_eq (if_pos hkp)
    · intro l _ hl
      unfold shellTerm
      apply if_neg
      intro hlp
      exact hl (shell_disjoint hε hlp hkp)
    · intro hk'
      exact (hk' hk).elim
  · have hz : ∀ k ∈ Finset.range m, shellTerm ε k h p = 0 := by
      intro k hk
      exact if_neg (fun hkp => hex ⟨k, hk, hkp⟩)
    rw [Finset.sum_eq_zero hz]
    exact mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)

/-- Summability justifies summing finitely many disjoint shell energies. -/
theorem sum_shell_energy_le (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {h : Site d → ℝ} (hh : SupportedIn ε U h) (m : ℕ) :
    (∑ k ∈ Finset.range m, ∑' p, shellTerm ε k h p) ≤
      ∑' p : Site d × Site d,
        jumpKernel (physical ε p.2) * (h (p.1 + p.2) - h p.1) ^ 2 := by
  have hs (k : ℕ) : Summable (shellTerm ε k h) := summable_single_scale d hd hε hU hh k
  rw [← Summable.tsum_finsetSum (fun k _ => hs k)]
  exact (summable_sum (fun k _ => hs k)).tsum_le_tsum
    (sum_shellTerm_le hε.1 h m)
    (summable_h1CritSq hd hε.1 (hh.hasFiniteSupport hε.1 hU))

/-- There are enough scales below size one to absorb the logarithmic normalization. -/
theorem exists_shell_count {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ m : ℕ, 1 ≤ m ∧ (∀ k < m, ε * 3 ^ k ≤ 1) ∧
      1 + |Real.log ε| ≤ (1 + Real.log 3) * m := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
    ((one_le_div hε.1).mpr hε.2.le) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · intro k hk
    have hp : (3 : ℝ) ^ k ≤ 3 ^ n :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hq := hp.trans hn
    have hc := (le_div_iff₀ hε.1).mp hq
    simpa only [mul_comm] using hc
  · have hl := Real.log_le_log (div_pos zero_lt_one hε.1) hn'.le
    rw [one_div, Real.log_inv, Real.log_pow,
      ← abs_of_nonpos (Real.log_nonpos hε.1.le hε.2.le)] at hl
    have hm : (1 : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    push_cast at hl ⊢
    nlinarith only [hl, hm]

end

end LongRange.Poincare
