import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Exponential lower bounds from midpoint log-convexity

A nonnegative function `a` on `[0, ∞)` with `a((s + u) / 2) ^ 2 ≤ a(s) a(u)` and
`a(h) ≥ a(0) - h E - C h ^ 2` satisfies `a(t) ≥ a(0) exp(-t E / a(0))`. Along the grid
`k t / n` the ratios of consecutive values increase, so `a(t) ≥ a(0) (a(t / n) / a(0)) ^ n`,
and the first-order bound gives the exponential in the limit `n → ∞`.
-/

namespace LatticeProb

open Filter Topology
open scoped NNReal

/-- For a nonnegative sequence with `b (k + 1) ^ 2 ≤ b k * b (k + 2)` and `b 0 > 0`, the
ratios of consecutive terms increase, so `b n ≥ b 0 (b 1 / b 0) ^ n`. -/
theorem mul_div_pow_le_of_sq_le_mul {b : ℕ → ℝ} (h0 : 0 < b 0) (hnn : ∀ k, 0 ≤ b k)
    (hb : ∀ k, b (k + 1) ^ 2 ≤ b k * b (k + 2)) (n : ℕ) :
    b 0 * (b 1 / b 0) ^ n ≤ b n := by
  set ρ := b 1 / b 0 with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (hnn 1) h0.le
  have hstep (k : ℕ) : ρ * b k ≤ b (k + 1) := by
    induction k with
    | zero => rw [hρ, div_mul_cancel₀ _ h0.ne']
    | succ k ih =>
      rcases (hnn (k + 1)).eq_or_lt with hz | hpos
      · rw [← hz, mul_zero]
        exact hnn _
      · have hk : 0 < b k := by
          rcases (hnn k).eq_or_lt with hz' | hp
          · have h := hb k
            rw [← hz', zero_mul] at h
            nlinarith
          · exact hp
        have h1 : b k * (ρ * b (k + 1)) ≤ b k * b (k + 2) :=
          calc
            b k * (ρ * b (k + 1)) = ρ * b k * b (k + 1) := by ring
            _ ≤ b (k + 1) * b (k + 1) := mul_le_mul_of_nonneg_right ih hpos.le
            _ = b (k + 1) ^ 2 := (sq _).symm
            _ ≤ b k * b (k + 2) := hb k
        exact le_of_mul_le_mul_left h1 hk
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      b 0 * ρ ^ (n + 1) = ρ * (b 0 * ρ ^ n) := by ring
      _ ≤ ρ * b n := mul_le_mul_of_nonneg_left ih hρ0
      _ ≤ b (n + 1) := hstep n

/-- A nonnegative midpoint log-convex function on `[0, ∞)` whose value at `h` is at least
`r - h E - C h ^ 2`, where `r > 0` is its value at zero, is at least `r exp(-t E / r)`. -/
theorem mul_exp_le_of_midpoint_sq_le {a : ℝ≥0 → ℝ} {r E C : ℝ} (hr : 0 < r) (h0 : a 0 = r)
    (hnn : ∀ t, 0 ≤ a t) (hconv : ∀ s u, a ((s + u) / 2) ^ 2 ≤ a s * a u)
    (hlow : ∀ h : ℝ≥0, r - h * E - C * h ^ 2 ≤ a h) (t : ℝ≥0) :
    r * Real.exp (-(t * E / r)) ≤ a t := by
  set g : ℕ → ℝ := fun n ↦ -(t * E / r) / n - C * t ^ 2 / r / n ^ 2 with hg
  have hlim : Tendsto (fun n : ℕ ↦ r * (1 + g n) ^ n) atTop
      (𝓝 (r * Real.exp (-(t * E / r)))) := by
    refine Tendsto.const_mul r (Real.tendsto_one_add_pow_exp_of_tendsto ?_)
    have h1 : Tendsto (fun n : ℕ ↦ -(t * E / r) - C * t ^ 2 / r / (n : ℝ)) atTop
        (𝓝 (-(t * E / r) - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [hg]
    field_simp
  have hgzero : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ -(t * E / r) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ ↦ C * t ^ 2 / r / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    simpa only [sub_zero] using h1.sub h2
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ne_atTop 0,
    hgzero.eventually (Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with n hn hgn
  have hn' : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set h : ℝ≥0 := t / n with hh
  set b : ℕ → ℝ := fun k ↦ a (k * h) with hb
  have hb0 : b 0 = r := by simp only [hb, Nat.cast_zero, zero_mul, h0]
  have hbn : b n = a t := by
    simp only [hb, hh]
    rw [mul_div_cancel₀ _ hn']
  have hb1 : b 1 = a h := by simp only [hb, Nat.cast_one, one_mul]
  have hconvb (k : ℕ) : b (k + 1) ^ 2 ≤ b k * b (k + 2) := by
    have hmid : ((k * h + (k + 2 : ℕ) * h) / 2 : ℝ≥0) = ((k + 1 : ℕ) : ℝ≥0) * h := by
      apply NNReal.eq
      push_cast
      ring
    have hc := hconv (k * h) ((k + 2 : ℕ) * h)
    rw [hmid] at hc
    exact hc
  have key := mul_div_pow_le_of_sq_le_mul (b := b) (by rw [hb0]; exact hr) (fun k ↦ hnn _)
    hconvb n
  rw [hb0, hbn, hb1] at key
  have hbase : 1 + g n ≤ a h / r := by
    rw [le_div_iff₀ hr]
    have hl := hlow h
    have hhr : (h : ℝ) = t / n := by simp only [hh, NNReal.coe_div, NNReal.coe_natCast]
    rw [hhr] at hl
    have heq : (1 + g n) * r = r - t / n * E - C * (t / n) ^ 2 := by
      simp only [hg]
      field_simp
      ring
    linarith
  calc
    r * (1 + g n) ^ n ≤ r * (a h / r) ^ n := by
      have hg1 : -1 < g n := hgn
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hbase n) hr.le
    _ ≤ a t := key

end LatticeProb
