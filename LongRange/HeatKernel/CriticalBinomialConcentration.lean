import LongRange.HeatKernel.CriticalBinomialWindow
import LatticeProb.Walk.BinomWindow

/-!
# Concentration of the binomial weights

The binomial weights in the averaged walk concentrate in the central window.
-/

open scoped ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- A binomial upper tail above three quarters has uniformly small mass at large times. -/
theorem binomial_upper_tail_le {n : ℕ} (hn : 128 ≤ n) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 3 * n / 4 + 1 ≤ k) :
    ∑ k ∈ s, LatticeProb.binomWeight k n ≤ (1 / 5 : ℝ) := by
  let m := 3 * n / 4 + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hnm : n < 2 * m := by dsimp [m]; omega
  have hnR : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn : (m : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast (show m ≤ n + 1 by dsimp [m]; omega)
  have hgap : (n : ℝ) / 2 ≤ 2 * m - n := by
    have hh' : (n : ℝ) ≤ 4 * m - 2 * n := by
      have ht : (n : ℝ) + 2 * n ≤ 4 * m := by
        exact_mod_cast (show n + 2 * n ≤ 4 * m by dsimp [m]; omega)
      linarith
    linarith
  have hsquare : (n : ℝ) ^ 2 / 4 ≤ (2 * (m : ℝ) - n) ^ 2 := by
    nlinarith [sq_nonneg (2 * (m : ℝ) - n - (n : ℝ) / 2)]
  have hquot : (n : ℝ) / 32 ≤ (2 * (m : ℝ) - n) ^ 2 / (4 * m) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (m : ℝ))).2
    nlinarith
  have hexp : Real.exp (-4 : ℝ) ≤ 1 / 5 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    rw [Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith
  calc
    _ ≤ Real.exp (-((2 * (m : ℝ) - n) ^ 2) / (4 * m)) :=
      LatticeProb.window_row_le hm hnm s hs
    _ ≤ Real.exp (-4 : ℝ) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    _ ≤ _ := hexp

/-- A binomial lower tail below one quarter has uniformly small mass at large times. -/
theorem binomial_lower_tail_le {n : ℕ} (hn : 128 ≤ n) (s : Finset ℕ)
    (hs : ∀ k ∈ s, k < n / 4) :
    ∑ k ∈ s, LatticeProb.binomWeight k n ≤ (1 / 5 : ℝ) := by
  have hinj : Set.InjOn (fun k : ℕ => n - k) s := by
    intro a ha b hb hab
    have ha' := hs a ha
    have hb' := hs b hb
    dsimp only at hab
    omega
  have hsym : (∑ k ∈ s.image (fun k => n - k), LatticeProb.binomWeight k n) =
      ∑ k ∈ s, LatticeProb.binomWeight k n := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by have := hs k hk; omega
    rw [LatticeProb.binomWeight_of_le (by omega : n - k ≤ n),
      LatticeProb.binomWeight_of_le hk', Nat.choose_symm hk']
  rw [← hsym]
  apply binomial_upper_tail_le hn
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
  have hj' := hs j hj
  omega

/-- At large times at least three fifths of the mass lies in the central window. -/
theorem central_binomial_mass_large {n : ℕ} (hn : 128 ≤ n) :
    (3 / 5 : ℝ) ≤ ∑ k ∈ Finset.Icc (n / 4) (3 * n / 4), LatticeProb.binomWeight k n := by
  let all := Finset.range (n + 1)
  let center := Finset.Icc (n / 4) (3 * n / 4)
  let lower := all.filter (fun k => k < n / 4)
  let upper := all.filter (fun k => 3 * n / 4 < k)
  let w := fun k => LatticeProb.binomWeight k n
  have hsubset : center ⊆ all := by
    intro k hk
    simp only [center, Finset.mem_Icc] at hk
    simp only [all, Finset.mem_range]
    omega
  have hdis : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    simp only [lower, upper, Finset.mem_filter] at hk hk'
    omega
  have hpartition : lower ∪ upper = all \ center := by
    ext k
    simp only [lower, upper, all, center, Finset.mem_union, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
    omega
  have hlo : (∑ k ∈ lower, w k) ≤ 1 / 5 := by
    apply binomial_lower_tail_le hn
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hhi : (∑ k ∈ upper, w k) ≤ 1 / 5 := by
    apply binomial_upper_tail_le hn
    intro k hk
    have h := (Finset.mem_filter.mp hk).2
    omega
  have hsum := Finset.sum_union (f := w) hdis
  have hdiff := Finset.sum_sdiff (f := w) hsubset
  have hall : (∑ k ∈ all, w k) = 1 := by
    exact LatticeProb.sum_binomWeight_row (by omega)
  rw [hpartition] at hsum
  change (3 / 5 : ℝ) ≤ ∑ k ∈ center, w k
  linarith


/-- The central binomial window has a positive uniform mass. -/
theorem central_binomial_mass_uniform :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ n, δ ≤ (2 : ℝ≥0∞)⁻¹ ^ n *
      ∑ k ∈ Finset.Icc (n / 4) (3 * n / 4), (n.choose k : ℝ≥0∞) := by
  apply central_binomial_mass_uniform_of_eventually (δ := ENNReal.ofReal (3 / 5))
    (by norm_num) 128
  intro n hn
  have h := ENNReal.ofReal_le_ofReal (central_binomial_mass_large hn)
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => LatticeProb.binomWeight_nonneg k n),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have hmem := Finset.mem_Icc.mp hk
    omega
  rw [LatticeProb.binomWeight_of_le hkn, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  norm_num [ENNReal.ofReal_div_of_pos]

end LatticeProb.Graph.LongRangeKernel
