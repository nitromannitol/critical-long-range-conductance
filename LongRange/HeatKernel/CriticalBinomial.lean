import LongRange.HeatKernel.CriticalSubordination

/-!
# Binomial expansion for averaged Markov densities

The powers of the average of a Markov density and its square are binomial
mixtures of powers of the original density.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

variable {X : Type*}

private theorem sum_choose_succ (f : ℕ → ℝ≥0∞) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ≥0∞) * f k) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * f k) +
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * f (k + 1) := by
  have h1 := Finset.sum_range_succ' (fun k => ((n + 1).choose k : ℝ≥0∞) * f k) (n + 1)
  have h2 : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℝ≥0∞) * f (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * f (k + 1)) +
        ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ≥0∞) * f (k + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
  have h3 := Finset.sum_range_succ' (fun k => (n.choose k : ℝ≥0∞) * f k) n
  have h4 := Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℝ≥0∞) * f (k + 1)) n
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1 h3
  simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, zero_mul, add_zero] at h4
  rw [h1, h2, h3, h4]
  ac_rfl

private theorem densityComp_sum_power (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (p : X → X → ℝ≥0∞) (a b n : ℕ) (c : ℕ → ℝ≥0∞) (x y : X) :
    densityComp m (densityPower m p a)
      (fun z w => ∑ k ∈ Finset.range (n + 1), c k * densityPower m p (b + k) z w) x y =
    ∑ k ∈ Finset.range (n + 1), c k * densityPower m p (a + (b + k)) x y := by
  unfold densityComp
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro k _
  rw [densityPower_add m hm p a (b + k)]
  unfold densityComp
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  ac_rfl

private theorem densityComp_averaged (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (p f : X → X → ℝ≥0∞) (x y : X) :
    densityComp m (averagedDensity m p) f x y = (2 : ℝ≥0∞)⁻¹ *
      (densityComp m (densityPower m p 1) f x y +
        densityComp m (densityPower m p 2) f x y) := by
  have h1 : densityPower m p 1 = p := by
    funext x y
    exact densityComp_identity_right m hm p x y
  rw [h1]
  simp only [densityComp, averagedDensity, add_mul, mul_assoc, ENNReal.tsum_mul_left,
    ENNReal.tsum_add]

private theorem densityComp_const_mul (m : X → ℝ≥0) (p f : X → X → ℝ≥0∞)
    (c : ℝ≥0∞) (x y : X) :
    densityComp m p (fun z w => c * f z w) x y = c * densityComp m p f x y := by
  unfold densityComp
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  dsimp only
  ac_rfl

/-- The powers of `(P + P²) / 2` are binomial mixtures of the powers of `P`. -/
theorem densityPower_averaged_eq_binomial (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (p : X → X → ℝ≥0∞) (n : ℕ) (x y : X) :
    densityPower m (averagedDensity m p) n x y = (2 : ℝ≥0∞)⁻¹ ^ n *
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * densityPower m p (n + k) x y := by
  induction n generalizing x y with
  | zero => simp [densityPower]
  | succ n ih =>
    change densityComp m (averagedDensity m p) (densityPower m (averagedDensity m p) n) x y = _
    have hfun : densityPower m (averagedDensity m p) n = fun z w =>
        (2 : ℝ≥0∞)⁻¹ ^ n * ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ≥0∞) * densityPower m p (n + k) z w := by
      funext z w
      exact ih z w
    rw [hfun]
    rw [densityComp_averaged m hm, densityComp_const_mul, densityComp_const_mul]
    rw [densityComp_sum_power m hm, densityComp_sum_power m hm]
    rw [pow_succ, ← mul_add, ← mul_assoc, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ n)]
    congr 1
    rw [sum_choose_succ]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro k _ <;>
      congr 1 <;> congr 1 <;> omega

/-- The binomial coefficients in the averaged density have total mass one. -/
theorem sum_averagedDensity_weights (n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ n * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) = 1 := by
  have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞)) = (2 : ℝ≥0∞) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hsum, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]

/-- A uniform upper bound on the relevant powers of `P` bounds the averaged power. -/
theorem densityPower_averaged_le_of_le (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (p : X → X → ℝ≥0∞) (n : ℕ) (x y : X) (B : ℝ≥0∞)
    (hB : ∀ k ≤ n, densityPower m p (n + k) x y ≤ B) :
    densityPower m (averagedDensity m p) n x y ≤ B := by
  rw [densityPower_averaged_eq_binomial m hm]
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * B := by
      gcongr with k hk
      exact hB k (by have := Finset.mem_range.mp hk; omega)
    _ = ((2 : ℝ≥0∞)⁻¹ ^ n *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞)) * B := by
      rw [← Finset.sum_mul, mul_assoc]
    _ = B := by rw [sum_averagedDensity_weights, one_mul]

end LatticeProb.Graph.LongRangeKernel
