import LongRange.HeatKernel.CriticalBinomial

/-!
# Binomial weights in the central window

Adjacent binomial coefficients have comparable weights throughout the central
window, as used in Lemma 2.2 of Murugan and Saloff-Coste.
-/

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

end LatticeProb.Graph.LongRangeKernel
