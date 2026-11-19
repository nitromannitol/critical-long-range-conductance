import LongRange.Support.Analysis.Davies.FiniteForm

/-!
# A two-point power inequality

A discrete chain-rule estimate for nonnegative values.
-/

namespace LatticeProb.Davies

/-- A two-point chain-rule estimate for natural powers. -/
theorem sq_pow_sub_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) (hp : 1 ≤ p) :
    (b ^ p - a ^ p) ^ 2 ≤ (p : ℝ) * ((b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (b - a)) := by
  let S : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range n, b ^ i * a ^ (n - 1 - i)
  let E : Finset ℕ := (Finset.range p).image (fun i ↦ 2 * i)
  have hsub : E ⊆ Finset.range (2 * p - 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hE : (∑ i ∈ Finset.range p, (b ^ i * a ^ (p - 1 - i)) ^ 2) =
      ∑ i ∈ E, b ^ i * a ^ (2 * p - 1 - 1 - i) := by
    dsimp [E]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [mul_pow, ← pow_mul, ← pow_mul]
      congr 1 <;> congr 1 <;> omega
    · intro i _ j _ hij
      dsimp only at hij
      omega
  have hsum : (∑ i ∈ Finset.range p, (b ^ i * a ^ (p - 1 - i)) ^ 2) ≤
      S (2 * p - 1) := by
    rw [hE]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦
      mul_nonneg (pow_nonneg hb _) (pow_nonneg ha _))
  have hcauchy : (S p) ^ 2 ≤ (p : ℝ) * S (2 * p - 1) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range p)
      (f := fun i ↦ b ^ i * a ^ (p - 1 - i))
    simp only [Finset.card_range] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hscaled := mul_le_mul_of_nonneg_right hcauchy (sq_nonneg (b - a))
  have hpgeom : S p * (b - a) = b ^ p - a ^ p := geom_sum₂_mul b a p
  have hqgeom : S (2 * p - 1) * (b - a) =
      b ^ (2 * p - 1) - a ^ (2 * p - 1) := geom_sum₂_mul b a _
  calc
    (b ^ p - a ^ p) ^ 2 = (S p) ^ 2 * (b - a) ^ 2 := by rw [← hpgeom]; ring
    _ ≤ ((p : ℝ) * S (2 * p - 1)) * (b - a) ^ 2 := hscaled
    _ = (p : ℝ) * ((b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (b - a)) := by
      rw [← hqgeom]
      ring

end LatticeProb.Davies
