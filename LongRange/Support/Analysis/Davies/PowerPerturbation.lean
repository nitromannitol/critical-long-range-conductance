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

namespace LatticeProb.Davies

private theorem weighted_young (P X Y Z : ℝ) (hP : 0 < P) :
    X * Y * Z / 2 ≤ X ^ 2 / (2 * P) + P / 8 * Y ^ 2 * Z ^ 2 := by
  apply le_of_mul_le_mul_left ?_ hP
  have hs := sq_nonneg (2 * X - P * Y * Z)
  field_simp
  nlinarith

/-- The nonlinear two-point estimate for an exponential perturbation. -/
theorem pair_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) (hp : 1 ≤ p)
    (h : ℝ) :
    (Real.exp h * b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (Real.exp (-h) * b - a) ≥
      (b ^ p - a ^ p) ^ 2 / (2 * p) - (2 * p + 1) / 4 *
        ((Real.exp h - 1) ^ 2 + (Real.exp (-h) - 1) ^ 2) *
          (a ^ (2 * p) + b ^ (2 * p)) := by
  let P : ℝ := p
  let A := a ^ p
  let B := b ^ p
  let x := Real.exp h
  let y := Real.exp (-h)
  let α := x - 1
  let β := y - 1
  let m := a * b ^ (2 * p - 1)
  let n := a ^ (2 * p - 1) * b
  let D := (b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (b - a)
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hA : 0 ≤ A := pow_nonneg ha _
  have hB : 0 ≤ B := pow_nonneg hb _
  have hm : 0 ≤ m := mul_nonneg ha (pow_nonneg hb _)
  have hn : 0 ≤ n := mul_nonneg (pow_nonneg ha _) hb
  have hxy : x * y = 1 := by
    dsimp [x, y]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsum : 0 ≤ α + β := by
    have h₁ := Real.add_one_le_exp h
    have h₂ := Real.add_one_le_exp (-h)
    dsimp [α, β, x, y]
    linarith
  have hneg : α + β = -(α * β) := by
    dsimp [α, β]
    nlinarith [hxy]
  have hsum_sq : α + β ≤ (α ^ 2 + β ^ 2) / 2 := by
    nlinarith [sq_nonneg (α + β)]
  have hdiff_sq : (α - β) ^ 2 ≤ 2 * (α ^ 2 + β ^ 2) := by
    nlinarith [sq_nonneg (α + β)]
  have hAB_sq : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
    nlinarith [sq_nonneg (A - B)]
  have hmn : |m - n| ≤ |B - A| * (A + B) :=
    abs_cross_pow_sub_le ha hb p hp
  have hmn_sum : m + n ≤ A ^ 2 + B ^ 2 := cross_pow_add_le ha hb p hp
  have hD : (B - A) ^ 2 / P ≤ D := by
    apply (div_le_iff₀ hP).2
    simpa only [A, B, D, P, mul_comm] using sq_pow_sub_pow_le ha hb p hp
  have hterm : (α - β) * (m - n) ≤ |B - A| * |α - β| * (A + B) := by
    calc
      (α - β) * (m - n) ≤ |(α - β) * (m - n)| := le_abs_self _
      _ = |α - β| * |m - n| := abs_mul _ _
      _ ≤ |α - β| * (|B - A| * (A + B)) :=
        mul_le_mul_of_nonneg_left hmn (abs_nonneg _)
      _ = _ := by ring
  have hprod : (α + β) * (m + n) ≤
      (α ^ 2 + β ^ 2) / 2 * (A ^ 2 + B ^ 2) :=
    mul_le_mul hsum_sq hmn_sum (add_nonneg hm hn)
      (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num))
  have hprod_sq : (α - β) ^ 2 * (A + B) ^ 2 ≤
      (2 * (α ^ 2 + β ^ 2)) * (2 * (A ^ 2 + B ^ 2)) :=
    mul_le_mul hdiff_sq hAB_sq (sq_nonneg _)
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hyoung := weighted_young P |B - A| |α - β| (A + B) hP
  rw [sq_abs, sq_abs] at hyoung
  have hR : ((α - β) * (m - n) + (α + β) * (m + n)) / 2 ≤
      (B - A) ^ 2 / (2 * P) + (2 * P + 1) / 4 *
        (α ^ 2 + β ^ 2) * (A ^ 2 + B ^ 2) := by
    nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hprod_sq)]
  have hid : (x * b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (y * b - a) =
      D - ((α - β) * (m - n) + (α + β) * (m + n)) / 2 := by
    dsimp only [D, α, β, m, n]
    calc
      _ = (b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (b - a) -
          (((x - 1) - (y - 1)) * (a * b ^ (2 * p - 1) - a ^ (2 * p - 1) * b) +
            ((x - 1) + (y - 1)) * (a * b ^ (2 * p - 1) + a ^ (2 * p - 1) * b)) / 2 +
          (x * y - 1) * b ^ (2 * p - 1) * b := by ring
      _ = _ := by rw [hxy]; ring
  have hpow (z : ℝ) : z ^ (2 * p) = (z ^ p) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  change (x * b ^ (2 * p - 1) - a ^ (2 * p - 1)) * (y * b - a) ≥ _
  rw [hid, hpow a, hpow b]
  change D - ((α - β) * (m - n) + (α + β) * (m + n)) / 2 ≥
    (B - A) ^ 2 / (2 * P) - (2 * P + 1) / 4 *
      (α ^ 2 + β ^ 2) * (A ^ 2 + B ^ 2)
  have hD' : 2 * ((B - A) ^ 2 / (2 * P)) ≤ D := by
    convert hD using 1; field_simp
  linarith

end LatticeProb.Davies
