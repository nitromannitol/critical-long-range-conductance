import LongRange.HeatKernel.CriticalSubordinationVolumeTail

/-!
# Small-scale bounds for quadratic subordination

The polynomial volume profile and quadratic scale satisfy the comparison used
in the small-scale part of the subordinate kernel estimate.
-/

namespace LatticeProb.Graph.LongRangeKernel

/-- Comparison of the quadratic-scale coefficients at two ordered scales. -/
theorem quadraticScale_volume_ratio_le (d : ℕ) {n r : ℝ}
    (hn : 1 ≤ n) (hnr : n ≤ r) :
    1 / (n * (1 + n) ^ 2 * (1 + n) ^ d) ≤
      (1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) * (r / n) ^ (d + 3) := by
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le hn0 hnr
  have hratio : (1 + r) / (1 + n) ≤ r / n := by
    apply (div_le_div_iff₀ (by positivity) hn0).2
    nlinarith
  have hrat0 : 0 ≤ (1 + r) / (1 + n) := by positivity
  have hp := pow_le_pow_left₀ hrat0 hratio (d + 2)
  have hfac : 0 ≤ (1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) * (r / n) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hp hfac
  have heq1 :
      (1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) * (r / n) *
        ((1 + r) / (1 + n)) ^ (d + 2) =
          1 / (n * (1 + n) ^ 2 * (1 + n) ^ d) := by
    rw [div_pow, pow_add]
    field_simp
    ring
  have heq2 :
      (1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) * (r / n) *
        (r / n) ^ (d + 2) =
          (1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) * (r / n) ^ (d + 3) := by
    rw [show d + 3 = (d + 2) + 1 by omega, pow_succ]
    ring
  linarith

/-- A polynomial multiplied by exponential decay has a uniform bound. -/
theorem pow_mul_exp_neg_le_factorial (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m * Real.exp (-x) ≤ (m.factorial : ℝ) := by
  have hf : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h := Real.pow_div_factorial_le_exp x hx m
  have h' : x ^ m ≤ (m.factorial : ℝ) * Real.exp x := by
    have := (div_le_iff₀ hf).mp h
    nlinarith
  have hm := mul_le_mul_of_nonneg_right h' (Real.exp_nonneg (-x))
  simpa [Real.exp_neg, mul_assoc] using hm

/-- Gaussian decay absorbs every polynomial uniformly over scales at least one. -/
theorem pow_mul_gaussian_le (m : ℕ) {t c : ℝ} (ht : 1 ≤ t) (hc : 0 < c) :
    t ^ m * Real.exp (-(t / c) ^ 2) ≤ (m.factorial : ℝ) * (c ^ 2) ^ m := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have ht0 : 0 ≤ t := by linarith
  have hexp : Real.exp (-(t / c) ^ 2) ≤ Real.exp (-(t / c ^ 2)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have : t ≤ t ^ 2 := by nlinarith
    have := div_le_div_of_nonneg_right this hc2.le
    simpa [div_pow] using this
  have hm := pow_mul_exp_neg_le_factorial m (x := t / c ^ 2) (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hm (show 0 ≤ (c ^ 2) ^ m by positivity)
  have heq : (t / c ^ 2) ^ m * Real.exp (-(t / c ^ 2)) * (c ^ 2) ^ m =
      t ^ m * Real.exp (-(t / c ^ 2)) := by
    rw [div_pow]
    field_simp
  calc
    _ ≤ t ^ m * Real.exp (-(t / c ^ 2)) := by gcongr
    _ ≤ _ := by linarith

/-- Each small-scale term is bounded by the same critical-profile expression. -/
theorem quadraticScale_gaussian_term_le (d : ℕ) {n r c : ℝ}
    (hn : 1 ≤ n) (hnr : n ≤ r) (hc : 0 < c) :
    (1 / (n * (1 + n) ^ 2 * (1 + n) ^ d)) * Real.exp (-(r / n / c) ^ 2) ≤
      ((d + 3).factorial : ℝ) * (c ^ 2) ^ (d + 3) /
        (r * (1 + r) ^ 2 * (1 + r) ^ d) := by
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := lt_of_lt_of_le hn0 hnr
  have ht : 1 ≤ r / n := (le_div_iff₀ hn0).2 (by linarith)
  have h := quadraticScale_volume_ratio_le d hn hnr
  have hg := pow_mul_gaussian_le (d + 3) ht hc
  have ha : 0 ≤ 1 / (r * (1 + r) ^ 2 * (1 + r) ^ d) := by positivity
  calc
    _ ≤ ((1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) * (r / n) ^ (d + 3)) *
        Real.exp (-(r / n / c) ^ 2) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = (1 / (r * (1 + r) ^ 2 * (1 + r) ^ d)) *
        ((r / n) ^ (d + 3) * Real.exp (-(r / n / c) ^ 2)) := by ring
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hg ha
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

/-- The small-scale Gaussian sum has the critical volume and quadratic decay. -/
theorem quadraticScale_gaussian_sum_le (d r : ℕ) {c : ℝ} (hr : 1 ≤ r) (hc : 0 < c) :
    (∑ n ∈ Finset.Icc 1 r,
      (1 / ((n : ℝ) * (1 + n) ^ 2 * (1 + n) ^ d)) *
        Real.exp (-((r : ℝ) / n / c) ^ 2)) ≤
      ((d + 3).factorial : ℝ) * (c ^ 2) ^ (d + 3) /
        ((1 + (r : ℝ)) ^ 2 * (1 + r) ^ d) := by
  let K : ℝ := ((d + 3).factorial : ℝ) * (c ^ 2) ^ (d + 3)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hsum : (∑ n ∈ Finset.Icc 1 r,
      (1 / ((n : ℝ) * (1 + n) ^ 2 * (1 + n) ^ d)) *
        Real.exp (-((r : ℝ) / n / c) ^ 2)) ≤
      ∑ _n ∈ Finset.Icc 1 r, K / (r * (1 + (r : ℝ)) ^ 2 * (1 + r) ^ d) := by
    apply Finset.sum_le_sum
    intro n hn
    have h := Finset.mem_Icc.mp hn
    apply quadraticScale_gaussian_term_le d
    · exact_mod_cast h.1
    · exact_mod_cast h.2
    · exact hc
  calc
    _ ≤ _ := hsum
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc]
      simp only [nsmul_eq_mul]
      dsimp [K]
      field_simp

end LatticeProb.Graph.LongRangeKernel
