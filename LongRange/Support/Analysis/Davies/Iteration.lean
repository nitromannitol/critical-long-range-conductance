import LongRange.Support.Analysis.Davies.Comparison
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Constants for the Davies iteration

Geometric sums and bounds for the time grid used in the iteration.
-/

namespace LatticeProb.Davies

open Filter Finset
open scoped Topology

noncomputable section

/-- The exponential correction on the geometric time grid has a finite sum. -/
theorem hasSum_davies_correction {l : ℝ} (hl : 2 < l) :
    HasSum (fun n : ℕ ↦ 3 * (2 / l) ^ (n + 1)) (6 / (l - 2)) := by
  have hlpos : 0 < l := by linarith
  have hq0 : 0 ≤ 2 / l := by positivity
  have hq1 : 2 / l < 1 := (div_lt_one hlpos).2 hl
  have hsum := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (3 * (2 / l))
  convert hsum using 1
  · ext n
    rw [pow_succ]
    ring
  · field_simp; ring

/-- The geometric sum controlling the contribution of the killing parameter. -/
theorem hasSum_davies_killing {l : ℝ} (hl : 2 < l) :
    HasSum (fun n : ℕ ↦ (1 / (2 * l)) ^ n) (2 * l / (2 * l - 1)) := by
  have hden : 0 < 2 * l := by linarith
  have hq0 : 0 ≤ 1 / (2 * l) := by positivity
  have hq1 : 1 / (2 * l) < 1 := (div_lt_one hden).2 (by linarith)
  have hsum := hasSum_geometric_of_lt_one hq0 hq1
  convert hsum using 1
  field_simp

/-- The time-grid coefficient multiplying the killing parameter is at most one. -/
theorem davies_killing_coefficient_le_one {l : ℝ} (hl : 2 < l) :
    2 * (l - 1) / (2 * l - 1) ≤ 1 := by
  have hden : 0 < 2 * l - 1 := by linarith
  apply (div_le_one hden).2
  linarith

/-- The choice of the geometric parameter gives the desired perturbation exponent. -/
theorem davies_exponent_coefficient_le {l ε : ℝ} (hε : 0 < ε)
    (hl : 2 < l) (hchoice : 2 + 6 / ε ≤ l) :
    (l - 1) / l * (1 + 6 / (l - 2)) ≤ 1 + ε := by
  have hlpos : 0 < l := by linarith
  have hltwo : 0 < l - 2 := by linarith
  have hεbound : 6 ≤ ε * (l - 2) := by
    have := (div_le_iff₀ hε).1 (show 6 / ε ≤ l - 2 by linarith)
    nlinarith
  have hratio : (l - 1) / l ≤ 1 := (div_le_one hlpos).2 (by linarith)
  have hratio0 : 0 ≤ (l - 1) / l := div_nonneg (by linarith) hlpos.le
  have hcorr : 6 / (l - 2) ≤ ε := (div_le_iff₀ hltwo).2 hεbound
  nlinarith [mul_le_mul_of_nonneg_left hcorr hratio0,
    mul_le_mul_of_nonneg_right hratio hε.le]

/-- The geometric subdivision of a positive time interval. -/
def timeGrid (l t : ℝ) (n : ℕ) : ℝ := t * (1 - l⁻¹ ^ n)

theorem timeGrid_nonneg {l t : ℝ} (hl : 2 < l) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ timeGrid l t n := by
  have hlpos : 0 < l := by linarith
  have hq : l⁻¹ ≤ 1 := (inv_le_one₀ hlpos).2 (by linarith)
  exact mul_nonneg ht (sub_nonneg.mpr (pow_le_one₀ (inv_nonneg.mpr hlpos.le) hq))

theorem timeGrid_lt_succ {l t : ℝ} (hl : 2 < l) (ht : 0 < t) (n : ℕ) :
    timeGrid l t n < timeGrid l t (n + 1) := by
  have hlpos : 0 < l := by linarith
  have hqpos : 0 < l⁻¹ := inv_pos.mpr hlpos
  have hq : l⁻¹ < 1 := (inv_lt_one₀ hlpos).2 (by linarith)
  have hp : 0 < l⁻¹ ^ n := pow_pos hqpos _
  dsimp [timeGrid]
  rw [pow_succ]
  nlinarith [mul_pos hp (sub_pos.mpr hq)]

theorem timeGrid_lt {l t : ℝ} (hl : 2 < l) (ht : 0 < t) (n : ℕ) :
    timeGrid l t n < t := by
  have hlpos : 0 < l := by linarith
  have hp : 0 < l⁻¹ ^ n := pow_pos (inv_pos.mpr hlpos) _
  dsimp [timeGrid]
  nlinarith [mul_pos ht hp]

theorem timeGrid_increment {l t : ℝ} (hl : 2 < l) (n : ℕ) :
    timeGrid l t (n + 1) - timeGrid l t n =
      (l - 1) * l ^ (-(n + 1 : ℤ)) * t := by
  have hl0 : l ≠ 0 := by linarith
  have hexp : (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
  have hid : (l - 1) * l⁻¹ = 1 - l⁻¹ := by field_simp
  calc
    _ = t * (l⁻¹ ^ n * (1 - l⁻¹)) := by
      dsimp [timeGrid]
      rw [pow_succ]
      ring
    _ = _ := by
      rw [hexp, zpow_neg, zpow_natCast, pow_succ, mul_inv_rev, inv_pow, ← hid]
      ring

/-- A product with half the exponents has the square root of the original product as its limit. -/
theorem tendsto_prod_mul_rpow {a P : ℝ} {f w : ℕ → ℝ} (ha : 0 < a)
    (hf : ∀ n, 0 ≤ f n) (hw : HasSum w (1 / 2 : ℝ))
    (hp : HasProd (fun n ↦ Real.rpow (f n) (2 * w n)) P) :
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.range N, Real.rpow (a ^ 2 * f n) (w n))
      atTop (𝓝 (a * Real.rpow P (1 / 2))) := by
  have hsum := hw.tendsto_sum_nat
  have hpow : Tendsto (fun N : ℕ ↦ Real.rpow (a ^ 2) (∑ n ∈ Finset.range N, w n))
      atTop (𝓝 (Real.rpow (a ^ 2) (1 / 2))) :=
    (Real.continuous_const_rpow (ne_of_gt (sq_pos_of_pos ha))).tendsto _ |>.comp hsum
  have hprod : Tendsto (fun N : ℕ ↦ Real.rpow (∏ n ∈ Finset.range N,
      Real.rpow (f n) (2 * w n)) (1 / 2)) atTop (𝓝 (Real.rpow P (1 / 2))) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto _ |>.comp hp.tendsto_prod_nat
  have hbase : Real.rpow (a ^ 2) (1 / 2) = a := by
    change (a ^ 2 : ℝ) ^ (1 / (2 : ℝ)) = a
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hfinal : Tendsto (fun N : ℕ ↦
      Real.rpow (a ^ 2) (∑ n ∈ Finset.range N, w n) *
      Real.rpow (∏ n ∈ Finset.range N, Real.rpow (f n) (2 * w n)) (1 / 2))
      atTop (𝓝 (a * Real.rpow P (1 / 2))) := by
    simpa only [hbase] using hpow.mul hprod
  convert hfinal using 1
  ext N
  change (∏ n ∈ Finset.range N, (a ^ 2 * f n) ^ (w n)) =
    (a ^ 2 : ℝ) ^ (∑ n ∈ Finset.range N, w n) *
      (∏ n ∈ Finset.range N, (f n) ^ (2 * w n)) ^ (1 / (2 : ℝ))
  rw [Real.rpow_sum_of_pos (sq_pos_of_pos ha), ← Real.finsetProd_rpow]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro n hn
    rw [← Real.rpow_mul (hf n)]
    have hexp : 2 * w n * (1 / 2 : ℝ) = w n := by ring
    rw [hexp, Real.mul_rpow (sq_nonneg a) (hf n)]
  · intro n hn
    exact Real.rpow_nonneg (hf n) _

/-- The source product profile gives the limit used in the finite Davies iteration. -/
theorem ckkw_product_limit {φ : ℝ → ℝ} {l c C a t : ℝ}
    (hl : 2 < l) (ha : 0 < a) (ht : 0 < t)
    (hφ : ∀ s > 0, 0 < φ s) (hprofile : External.ckkwProductBound φ l c C) :
    ∃ P : ℝ, HasProd (fun n : ℕ ↦ Real.rpow
      (φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * t)) ((2 : ℝ) ^ (-(n + 1 : ℤ)))) P ∧
      P ≤ C * φ (c * t) ∧
      Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.range N, Real.rpow
        (a ^ 2 * φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * t))
        ((1 / 2 : ℝ) / 2 / 2 ^ n)) atTop (𝓝 (a * Real.rpow P (1 / 2))) := by
  obtain ⟨P, hp, hP⟩ := hprofile t ht
  refine ⟨P, hp, hP, ?_⟩
  let f : ℕ → ℝ := fun n ↦ φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * t)
  let w : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) / 2 / 2 ^ n
  have hlpos : 0 < l := by linarith
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    apply (hφ _ (mul_pos (mul_pos (by linarith) (zpow_pos hlpos _)) ht)).le
  have hw : HasSum w (1 / 2 : ℝ) := hasSum_geometric_two' (1 / 2)
  have hexp : ∀ n : ℕ, 2 * w n = (2 : ℝ) ^ (-(n + 1 : ℤ)) := by
    intro n
    dsimp [w]
    have heq : (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [heq, zpow_neg, zpow_natCast, pow_succ]
    field_simp
  have hp' : HasProd (fun n ↦ Real.rpow (f n) (2 * w n)) P := by
    simpa only [hexp, f] using hp
  exact tendsto_prod_mul_rpow ha hf hw hp'

/-- The product limit is bounded by the source product profile. -/
theorem ckkw_product_limit_le {φ : ℝ → ℝ} {l c C a t : ℝ}
    (hl : 2 < l) (ha : 0 < a) (ht : 0 < t)
    (hφ : ∀ s > 0, 0 < φ s) (hprofile : External.ckkwProductBound φ l c C) :
    ∃ Q : ℝ,
      Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.range N, Real.rpow
        (a ^ 2 * φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * t))
        ((1 / 2 : ℝ) / 2 / 2 ^ n)) atTop (𝓝 Q) ∧
      Q ≤ a * Real.rpow (C * φ (c * t)) (1 / 2) := by
  obtain ⟨P, hp, hP, hlim⟩ := ckkw_product_limit hl ha ht hφ hprofile
  have hP0 : 0 ≤ P := by
    apply ge_of_tendsto hp.tendsto_prod_nat
    filter_upwards with N
    apply Finset.prod_nonneg
    intro n hn
    apply Real.rpow_nonneg
    apply (hφ _ ?_).le
    have hlpos : 0 < l := by linarith
    exact mul_pos (mul_pos (by linarith) (zpow_pos hlpos _)) ht
  refine ⟨a * Real.rpow P (1 / 2), hlim, ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hP0 hP (by norm_num)) ha.le

/-- A scalar product iteration passes finite bounds to the limit. -/
theorem le_of_product_iteration {M A E D : ℕ → ℝ} {z B P : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hD : ∀ n, 0 ≤ D n) (hM0 : 0 ≤ M 0)
    (hstep : ∀ n, M (n + 1) ≤ A n * Real.exp (E n) * M n)
    (hcoordinate : ∀ n, z ≤ D n * M n)
    (hsum : ∀ n, (∑ k ∈ Finset.range n, E k) ≤ B)
    (hprod : Tendsto (fun n ↦ ∏ k ∈ Finset.range n, A k) atTop (𝓝 P))
    (hDlim : Tendsto D atTop (𝓝 1)) : z ≤ P * Real.exp B * M 0 := by
  have hiter : ∀ n, M n ≤ (∏ k ∈ Finset.range n, A k) *
      Real.exp (∑ k ∈ Finset.range n, E k) * M 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : 0 ≤ A n * Real.exp (E n) := mul_nonneg (hA n) (Real.exp_pos _).le
      have hmul := mul_le_mul_of_nonneg_left ih hc
      calc
        M (n + 1) ≤ A n * Real.exp (E n) * M n := hstep n
        _ ≤ A n * Real.exp (E n) * ((∏ k ∈ Finset.range n, A k) *
            Real.exp (∑ k ∈ Finset.range n, E k) * M 0) := hmul
        _ = (∏ k ∈ Finset.range (n + 1), A k) *
            Real.exp (∑ k ∈ Finset.range (n + 1), E k) * M 0 := by
          rw [Finset.prod_range_succ, Finset.sum_range_succ, Real.exp_add]
          ring
  have hbounded : ∀ n, M n ≤ (∏ k ∈ Finset.range n, A k) * Real.exp B * M 0 := by
    intro n
    have hprod0 : 0 ≤ ∏ k ∈ Finset.range n, A k := Finset.prod_nonneg fun k hk ↦ hA k
    have hexp : Real.exp (∑ k ∈ Finset.range n, E k) ≤ Real.exp B :=
      Real.exp_le_exp.mpr (hsum n)
    exact (hiter n).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hprod0) hM0)
  have hlim : Tendsto (fun n ↦ D n * ((∏ k ∈ Finset.range n, A k) * Real.exp B * M 0))
      atTop (𝓝 (P * Real.exp B * M 0)) := by
    convert hDlim.mul ((hprod.mul_const (Real.exp B)).mul_const (M 0)) using 1; simp
  apply ge_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n ↦ (hcoordinate n).trans
    (mul_le_mul_of_nonneg_left (hbounded n) (hD n))

end
end LatticeProb.Davies
