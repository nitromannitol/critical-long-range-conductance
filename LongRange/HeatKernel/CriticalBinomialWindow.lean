import LongRange.HeatKernel.CriticalBinomial

/-!
# Binomial weights in the central window

Adjacent binomial coefficients have comparable weights throughout the central
window, as used in Lemma 2.2 of Murugan and Saloff-Coste.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- Adjacent binomial coefficients in the central window differ by at most a factor of four. -/
theorem choose_central_window_comparable {n k : ℕ} (hn : 0 < n)
    (hlo : n / 4 ≤ k) (hhi : k ≤ 3 * n / 4) :
    (n.choose k : ℝ) ≤ 4 * (n.choose (k + 1) : ℝ) ∧
      (n.choose (k + 1) : ℝ) ≤ 4 * (n.choose k : ℝ) := by
  have hlt : k < n := by omega
  have hleft : n - k ≤ 4 * (k + 1) := by omega
  have hright : k + 1 ≤ 4 * (n - k) := by omega
  have hp : 0 < (k + 1 : ℝ) := by positivity
  have hq : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have heq : (n.choose (k + 1) : ℝ) * (k + 1) =
      (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hleftR : ((n - k : ℕ) : ℝ) ≤ 4 * ((k : ℝ) + 1) := by exact_mod_cast hleft
  have hrightR : (k : ℝ) + 1 ≤ 4 * ((n - k : ℕ) : ℝ) := by exact_mod_cast hright
  constructor
  · have h := mul_le_mul_of_nonneg_left hrightR (Nat.cast_nonneg (α := ℝ) (n.choose (k + 1)))
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hleftR (Nat.cast_nonneg (α := ℝ) (n.choose k))
    nlinarith

/-- Pairing adjacent terms in the central window costs a bounded factor. -/
theorem sum_choose_central_pairs_le {n : ℕ} (hn : 0 < n) (s : Finset ℕ)
    (hs : ∀ k ∈ s, n / 4 ≤ k ∧ k ≤ 3 * n / 4) (f : ℕ → ℝ≥0∞) :
    (∑ k ∈ s, (n.choose k : ℝ≥0∞) * (f k + f (k + 1))) ≤
      8 * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * f k := by
  have hsn : s ⊆ Finset.range n := by
    intro k hk
    have h := hs k hk
    exact Finset.mem_range.mpr (by omega)
  let F : ℕ → ℝ≥0∞ := fun k => (n.choose k : ℝ≥0∞) * f k
  have hfirst : (∑ k ∈ s, F k) ≤ ∑ k ∈ Finset.range (n + 1), F k :=
    Finset.sum_le_sum_of_subset (hsn.trans (Finset.range_mono (by omega)))
  have hshift : (∑ k ∈ s, F (k + 1)) ≤ ∑ k ∈ Finset.range (n + 1), F k := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, F (k + 1) := Finset.sum_le_sum_of_subset hsn
      _ ≤ _ := by
        have h := Finset.sum_range_succ' F n
        rw [h]
        exact le_add_right le_rfl
  have hsecond : (∑ k ∈ s, (n.choose k : ℝ≥0∞) * f (k + 1)) ≤
      4 * ∑ k ∈ Finset.range (n + 1), F k := by
    calc
      _ ≤ ∑ k ∈ s, 4 * F (k + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hcomp := (choose_central_window_comparable hn (hs k hk).1 (hs k hk).2).1
        have hnat : n.choose k ≤ 4 * n.choose (k + 1) := by exact_mod_cast hcomp
        have hcast : (n.choose k : ℝ≥0∞) ≤ 4 * (n.choose (k + 1) : ℝ≥0∞) := by
          exact_mod_cast hnat
        dsimp only [F]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hcast (bot_le : (0 : ℝ≥0∞) ≤ f (k + 1))
      _ = 4 * ∑ k ∈ s, F (k + 1) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hshift (bot_le : (0 : ℝ≥0∞) ≤ _)
  calc
    _ = (∑ k ∈ s, F k) + ∑ k ∈ s, (n.choose k : ℝ≥0∞) * f (k + 1) := by
      simp only [F, mul_add, Finset.sum_add_distrib]
    _ ≤ (∑ k ∈ Finset.range (n + 1), F k) +
        4 * ∑ k ∈ Finset.range (n + 1), F k := add_le_add hfirst hsecond
    _ ≤ 8 * ∑ k ∈ Finset.range (n + 1), F k := by
      have h : (1 : ℝ≥0∞) + 4 ≤ 8 := by norm_num
      simpa only [add_mul, one_mul] using mul_le_mul_of_nonneg_right h
        (bot_le : (0 : ℝ≥0∞) ≤ _)

/-- The averaged power dominates the central mixture of adjacent powers. -/
theorem densityPower_averaged_ge_central_pairs {X : Type*} (m : X → ℝ≥0)
    (hm : ∀ x, m x ≠ 0) (p : X → X → ℝ≥0∞) {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : ∀ k ∈ s, n / 4 ≤ k ∧ k ≤ 3 * n / 4) (x y : X) :
    ((2 : ℝ≥0∞)⁻¹ ^ n * 8⁻¹) *
        (∑ k ∈ s, (n.choose k : ℝ≥0∞) *
          (densityPower m p (n + k) x y + densityPower m p (n + (k + 1)) x y)) ≤
      densityPower m (averagedDensity m p) n x y := by
  rw [densityPower_averaged_eq_binomial m hm]
  have hpairs := sum_choose_central_pairs_le hn s hs (fun k => densityPower m p (n + k) x y)
  calc
    _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ n * 8⁻¹) *
        (8 * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) *
          densityPower m p (n + k) x y) :=
      mul_le_mul_of_nonneg_left hpairs (bot_le : (0 : ℝ≥0∞) ≤ _)
    _ = _ := by
      have h8 : (8 : ℝ≥0∞)⁻¹ * 8 = 1 :=
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      calc
        _ = ((2 : ℝ≥0∞)⁻¹ ^ n * ((8 : ℝ≥0∞)⁻¹ * 8)) *
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) *
              densityPower m p (n + k) x y := by ac_rfl
        _ = _ := by rw [h8, mul_one]

/-- A lower bound on paired powers transfers through any central window of positive mass. -/
theorem densityPower_averaged_ge_of_central_mass {X : Type*} (m : X → ℝ≥0)
    (hm : ∀ x, m x ≠ 0) (p : X → X → ℝ≥0∞) {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : ∀ k ∈ s, n / 4 ≤ k ∧ k ≤ 3 * n / 4) (x y : X)
    (δ B : ℝ≥0∞)
    (hδ : δ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * ∑ k ∈ s, (n.choose k : ℝ≥0∞))
    (hB : ∀ k ∈ s, B ≤ densityPower m p (n + k) x y +
      densityPower m p (n + (k + 1)) x y) :
    (8⁻¹ * δ) * B ≤ densityPower m (averagedDensity m p) n x y := by
  have hsum : (∑ k ∈ s, (n.choose k : ℝ≥0∞)) * B ≤
      ∑ k ∈ s, (n.choose k : ℝ≥0∞) *
        (densityPower m p (n + k) x y + densityPower m p (n + (k + 1)) x y) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (hB k hk) (bot_le : (0 : ℝ≥0∞) ≤ _)
  calc
    _ ≤ (8⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ n * ∑ k ∈ s, (n.choose k : ℝ≥0∞))) * B := by
      gcongr
    _ = ((2 : ℝ≥0∞)⁻¹ ^ n * 8⁻¹) *
        ((∑ k ∈ s, (n.choose k : ℝ≥0∞)) * B) := by ac_rfl
    _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ n * 8⁻¹) *
        (∑ k ∈ s, (n.choose k : ℝ≥0∞) *
          (densityPower m p (n + k) x y + densityPower m p (n + (k + 1)) x y)) :=
      mul_le_mul_of_nonneg_left hsum (bot_le : (0 : ℝ≥0∞) ≤ _)
    _ ≤ _ := densityPower_averaged_ge_central_pairs m hm p hn s hs x y

end LatticeProb.Graph.LongRangeKernel
