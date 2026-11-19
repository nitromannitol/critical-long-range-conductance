import LongRange.Support.Analysis.Davies.GridEndpoint

/-!
# Exponents in the Davies iteration

Bounds for the accumulated perturbation and killing contributions on the time grid.
-/

namespace LatticeProb.Davies

open Finset

noncomputable section

/-- The exponent contributed by one step of the power iteration. -/
def gridExponent (l t Λsq δ : ℝ) (n : ℕ) : ℝ :=
  (((2 * (2 ^ (n + 1) : ℕ) + 1 : ℝ) * Λsq + δ / (2 ^ (n + 1) : ℕ)) *
    (timeGrid l t (n + 2) - timeGrid l t (n + 1)))

/-- The increment of a geometric time grid in a form convenient for summation. -/
theorem timeGrid_increment_shifted {l t : ℝ} (hl : 2 < l) (n : ℕ) :
    timeGrid l t (n + 2) - timeGrid l t (n + 1) =
      ((l - 1) / l) * t * (1 / l) ^ (n + 1) := by
  have hl0 : l ≠ 0 := by linarith
  dsimp [timeGrid]
  rw [pow_succ]
  simp only [div_eq_mul_inv, one_mul]
  field_simp
  ring

/-- A single step exponent is bounded by a geometric perturbation and its time increment. -/
theorem gridExponent_le {l t Λsq δ : ℝ} (hl : 2 < l) (ht : 0 < t)
    (hΛ : 0 ≤ Λsq) (hδ : 0 ≤ δ) (n : ℕ) :
    gridExponent l t Λsq δ n ≤
      (((l - 1) / l) * t * Λsq) * (3 * (2 / l) ^ (n + 1)) +
        δ * (timeGrid l t (n + 2) - timeGrid l t (n + 1)) := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hp0 : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hdiv : δ / (2 : ℝ) ^ (n + 1) ≤ δ := (div_le_self hδ hp)
  have hrate : (2 * (2 : ℝ) ^ (n + 1) + 1) * Λsq + δ / (2 : ℝ) ^ (n + 1) ≤
      3 * (2 : ℝ) ^ (n + 1) * Λsq + δ := by
    nlinarith [mul_nonneg hΛ (sub_nonneg.mpr hp)]
  have hincr : 0 ≤ timeGrid l t (n + 2) - timeGrid l t (n + 1) := by
    have h := timeGrid_lt_succ hl ht (n + 1)
    simpa only [Nat.add_assoc, Nat.reduceAdd, sub_nonneg] using h.le
  calc
    gridExponent l t Λsq δ n ≤
        (3 * (2 : ℝ) ^ (n + 1) * Λsq + δ) *
          (timeGrid l t (n + 2) - timeGrid l t (n + 1)) := by
      apply mul_le_mul_of_nonneg_right _ hincr
      simpa only [gridExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one] using hrate
    _ = _ := by
      rw [timeGrid_increment_shifted hl]
      rw [div_pow]
      simp only [div_eq_mul_inv, one_pow]
      ring

/-- Time increments used by the iteration have total length at most the terminal time. -/
theorem sum_timeGrid_increment_le {l t : ℝ} (hl : 2 < l) (ht : 0 < t) (N : ℕ) :
    (∑ n ∈ range N, (timeGrid l t (n + 2) - timeGrid l t (n + 1))) ≤ t := by
  have htel : ∀ N : ℕ, (∑ n ∈ range N, (timeGrid l t (n + 2) - timeGrid l t (n + 1))) =
      timeGrid l t (N + 1) - timeGrid l t 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      have he : N + 1 + 1 = N + 2 := by omega
      rw [he]
      ring
  rw [htel]
  have h₁ := timeGrid_nonneg hl ht.le 1
  have h₂ := timeGrid_lt hl ht (N + 1)
  linarith

/-- The total exponent in any finite Davies iteration has a uniform bound. -/
theorem sum_gridExponent_le {l t Λsq δ : ℝ} (hl : 2 < l) (ht : 0 < t)
    (hΛ : 0 ≤ Λsq) (hδ : 0 ≤ δ) (N : ℕ) :
    (∑ n ∈ range N, gridExponent l t Λsq δ n) ≤
      ((l - 1) / l) * t * Λsq * (6 / (l - 2)) + δ * t := by
  have hlpos : 0 < l := by linarith
  have hdiff : 0 < l - 1 := by linarith
  have ha : 0 ≤ ((l - 1) / l) * t * Λsq := by positivity
  have hsum : (∑ n ∈ range N, 3 * (2 / l) ^ (n + 1)) ≤ 6 / (l - 2) := by
    have h := (hasSum_davies_correction hl).summable.sum_le_tsum (range N)
      (fun n _ ↦ by positivity)
    rw [(hasSum_davies_correction hl).tsum_eq] at h
    exact h
  calc
    _ ≤ ∑ n ∈ range N, ((((l - 1) / l) * t * Λsq) * (3 * (2 / l) ^ (n + 1)) +
        δ * (timeGrid l t (n + 2) - timeGrid l t (n + 1))) :=
      sum_le_sum fun n _ ↦ gridExponent_le hl ht hΛ hδ n
    _ = (((l - 1) / l) * t * Λsq) * (∑ n ∈ range N, 3 * (2 / l) ^ (n + 1)) +
        δ * (∑ n ∈ range N, (timeGrid l t (n + 2) - timeGrid l t (n + 1))) := by
      rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsum ha)
      (mul_le_mul_of_nonneg_left (sum_timeGrid_increment_le hl ht N) hδ)

end
end LatticeProb.Davies
