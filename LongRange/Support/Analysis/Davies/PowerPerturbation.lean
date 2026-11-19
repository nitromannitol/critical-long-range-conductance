import LongRange.Support.Analysis.Davies.PowerInequality
import LongRange.Support.Analysis.Davies.Perturbation

/-!
# Power estimates for perturbed jump forms

Algebraic bounds for two values and a conjugating exponential weight.
-/

namespace LatticeProb.Davies

/-- The cross-power difference is bounded by the difference of the squares of the powers. -/
theorem abs_cross_pow_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p : ℕ) (hp : 1 ≤ p) :
    |a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b| ≤
      |b ^ p - a ^ p| * (a ^ p + b ^ p) := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    have hcross : b * a ^ (2 * p - 1) - b ^ (2 * p - 1) * a =
        -(a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b) := by ring
    rw [hcross, abs_neg, abs_sub_comm (a ^ p) (b ^ p), add_comm (b ^ p) (a ^ p)] at h
    exact h
  have hpab := pow_le_pow_left₀ ha hab p
  have hq : a ^ (2 * p - 2) ≤ b ^ (2 * p - 2) := pow_le_pow_left₀ ha hab _
  have hn : 0 ≤ a * b * (b ^ (2 * p - 2) - a ^ (2 * p - 2)) :=
    mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr hq)
  have hqex : 2 * p - 1 = (2 * p - 2) + 1 := by omega
  have hpex : 2 * p = (2 * p - 1) + 1 := by omega
  have hmul (x : ℝ) : x ^ (2 * p) = (x ^ p) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hpower (x : ℝ) : (x ^ p) ^ 2 = x ^ (2 * p - 1) * x := by
    calc
      (x ^ p) ^ 2 = x ^ (2 * p) := (hmul x).symm
      _ = x ^ (2 * p - 1) * x := by
        conv_lhs => rw [hpex]
        exact pow_succ _ _
  have hcross : 0 ≤ a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b := by
    rw [hqex, pow_succ, pow_succ]
    nlinarith
  have hbound : a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b ≤
      (b ^ p - a ^ p) * (a ^ p + b ^ p) := by
    have hprod : 0 ≤ (b - a) * (b ^ (2 * p - 1) + a ^ (2 * p - 1)) :=
      mul_nonneg (sub_nonneg.mpr hab) (add_nonneg (pow_nonneg hb _) (pow_nonneg ha _))
    have hid : (b ^ p - a ^ p) * (a ^ p + b ^ p) -
        (a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b) =
        (b - a) * (b ^ (2 * p - 1) + a ^ (2 * p - 1)) := by
      calc
        _ = (b ^ p) ^ 2 - (a ^ p) ^ 2 -
            (a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b) := by ring
        _ = _ := by rw [hpower a, hpower b]; ring
    linarith
  rw [abs_of_nonneg hcross, abs_of_nonneg (sub_nonneg.mpr hpab)]
  exact hbound

/-- The sum of two cross-powers is at most the sum of the corresponding even powers. -/
theorem cross_pow_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p : ℕ) (hp : 1 ≤ p) :
    a * b ^ (2 * p - 1) + a ^ (2 * p - 1) * b ≤ (a ^ p) ^ 2 + (b ^ p) ^ 2 := by
  have hqex : 2 * p = (2 * p - 1) + 1 := by omega
  have hmul (x : ℝ) : x ^ (2 * p) = (x ^ p) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hpower (x : ℝ) : (x ^ p) ^ 2 = x ^ (2 * p - 1) * x := by
    calc
      (x ^ p) ^ 2 = x ^ (2 * p) := (hmul x).symm
      _ = x ^ (2 * p - 1) * x := by
        conv_lhs => rw [hqex]
        exact pow_succ _ _
  have hd : 0 ≤ (b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (b - a) := by
    rcases le_total a b with hab | hba
    · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hab _)) (sub_nonneg.mpr hab)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (pow_le_pow_left₀ hb hba _)) (sub_nonpos.mpr hba)
  have hid : (a ^ p) ^ 2 + (b ^ p) ^ 2 -
      (a * b ^ (2 * p - 1) + a ^ (2 * p - 1) * b) =
      (b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (b - a) := by
    rw [hpower a, hpower b]
    ring
  linarith

end LatticeProb.Davies
