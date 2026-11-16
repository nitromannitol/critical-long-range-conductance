import LongRangeHeat.Defs

/-!
# Initial value of the lattice heat series

The exponential series has the prescribed initial value at time zero.
-/

namespace LongRangeHeat

open LatticeProb.Euclidean.Lattice

/-- The lattice heat series starts from the restriction of the initial data. -/
theorem latticeHeat_zero {d : ℕ} (ε : ℝ) (a : LongRange.Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) : latticeHeat ε a f 0 = restrict ε f := by
  funext q
  unfold latticeHeat
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- A geometric bound on the iterates implies convergence of the lattice heat series. -/
theorem summable_latticeHeat_of_iterate_bound {d : ℕ} (ε : ℝ)
    (a : LongRange.Edge d → ℝ) (f : (Fin d → ℝ) → ℝ) (t : ℝ) (q : LatticeProb.Site d)
    {M K : ℝ} (_hM : 0 ≤ M) (_hK : 0 ≤ K)
    (h : ∀ n : ℕ, |(LongRange.generator ε a)^[n] (restrict ε f) q| ≤ M * K ^ n) :
    Summable (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
      (LongRange.generator ε a)^[n] (restrict ε f) q) := by
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial (|t| * K)).mul_left M)
  intro n
  have hf : |(n.factorial : ℝ)| = n.factorial := abs_of_nonneg (Nat.cast_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, hf]
  have hfac : 0 ≤ |t| ^ n / (n.factorial : ℝ) := by positivity
  calc
    |t| ^ n / (n.factorial : ℝ) * |(LongRange.generator ε a)^[n] (restrict ε f) q|
        ≤ |t| ^ n / (n.factorial : ℝ) * (M * K ^ n) := mul_le_mul_of_nonneg_left (h n) hfac
    _ = M * ((|t| * K) ^ n / (n.factorial : ℝ)) := by rw [mul_pow]; ring

end LongRangeHeat
