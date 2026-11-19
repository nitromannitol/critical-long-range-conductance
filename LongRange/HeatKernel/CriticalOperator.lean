import LongRange.HeatKernel.CriticalEnergyReal

/-!
# Counting-space symmetric Markov kernels

Weighted square sums for symmetric Markov kernels on counting measure.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The weighted square at the initial site is summable on pairs. -/
theorem summable_kernel_square_left {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    Summable (fun p : X × X => (k p.1 p.2).toReal * f p.1 ^ 2) := by
  have h : (∑' p : X × X, k p.1 p.2 * ENNReal.ofReal (f p.1 ^ 2)) < ∞ := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_right, hk, one_mul]
    exact hf
  have hs := ENNReal.summable_toReal h.ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using hs

/-- The weighted square at the terminal site is summable on pairs. -/
theorem summable_kernel_square_right {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    Summable (fun p : X × X => (k p.1 p.2).toReal * f p.2 ^ 2) := by
  have h : (∑' p : X × X, k p.1 p.2 * ENNReal.ofReal (f p.2 ^ 2)) < ∞ := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp_rw [hsym, ENNReal.tsum_mul_right, hk, one_mul]
    exact hf
  have hs := ENNReal.summable_toReal h.ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using hs

/-- The mixed kernel pairing is absolutely summable on pairs. -/
theorem summable_kernel_mul {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    Summable (fun p : X × X => (k p.1 p.2).toReal * (f p.1 * f p.2)) := by
  have hs := (summable_kernel_square_left k hk f hf).add
    (summable_kernel_square_right k hk hsym f hf)
  apply Summable.of_norm_bounded hs
  intro ⟨x,y⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_mul]
  have h : 2 * (|f x| * |f y|) ≤ f x ^ 2 + f y ^ 2 := by
    nlinarith [sq_nonneg (|f x| - |f y|), sq_abs (f x), sq_abs (f y)]
  have hk0 : 0 ≤ (k x y).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr h)]

/-- The Dirichlet energy equals the absolutely convergent directed pairing. -/
theorem realKernelEnergy_eq_pairing {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    realKernelEnergy k f =
      ∑' p : X × X, (k p.1 p.2).toReal * (f p.1 * (f p.1 - f p.2)) := by
  let a : X × X → ℝ := fun p => (k p.1 p.2).toReal * f p.1 ^ 2
  let b : X × X → ℝ := fun p => (k p.1 p.2).toReal * f p.2 ^ 2
  let c : X × X → ℝ := fun p => (k p.1 p.2).toReal * (f p.1 * f p.2)
  have ha : Summable a := summable_kernel_square_left k hk f hf
  have hb : Summable b := summable_kernel_square_right k hk hsym f hf
  have hc : Summable c := summable_kernel_mul k hk hsym f hf
  have hab : (∑' p, b p) = ∑' p, a p := by
    rw [← (Equiv.prodComm X X).tsum_eq a]
    apply tsum_congr
    intro ⟨x, y⟩
    simp only [a, b, Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hsym]
  have he : Summable (fun p : X × X => (k p.1 p.2).toReal * (f p.1 - f p.2) ^ 2) := by
    convert (ha.add hb).sub (hc.mul_left 2) using 1
    ext ⟨x,y⟩
    dsimp [a, b, c]
    ring
  unfold realKernelEnergy
  rw [← he.tsum_prod]
  have heq : (∑' p : X × X, (k p.1 p.2).toReal * (f p.1 - f p.2) ^ 2) =
      (∑' p, a p) + (∑' p, b p) - 2 * ∑' p, c p := by
    calc
      _ = ∑' p, ((a p + b p) - 2 * c p) := by
        apply tsum_congr
        intro ⟨x,y⟩
        dsimp [a, b, c]
        ring
      _ = _ := by rw [Summable.tsum_sub (ha.add hb) (hc.mul_left 2),
        Summable.tsum_add ha hb, tsum_mul_left]
  have hpq : (∑' p : X × X, (k p.1 p.2).toReal *
      (f p.1 * (f p.1 - f p.2))) = (∑' p, a p) - ∑' p, c p := by
    calc
      _ = ∑' p, (a p - c p) := by
        apply tsum_congr
        intro ⟨x,y⟩
        dsimp [a, c]
        ring
      _ = _ := Summable.tsum_sub ha hc
  rw [heq, hpq, hab]
  ring

/-- Each real kernel row is a probability distribution. -/
theorem summable_real_kernel_row {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (x : X) :
    Summable (fun y => (k x y).toReal) ∧ (∑' y, (k x y).toReal) = 1 := by
  have h : (∑' y, k x y) ≠ ∞ := by simp only [hk, ne_eq, ENNReal.one_ne_top, not_false_eq_true]
  exact ⟨ENNReal.summable_toReal h, by rw [← ENNReal.tsum_toReal_eq
    (ENNReal.ne_top_of_tsum_ne_top h), hk, ENNReal.toReal_one]⟩

/-- The Markov operator is defined by an absolutely convergent row sum on square-summable inputs. -/
theorem summable_kernel_apply_row {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) (x : X) :
    Summable (fun y => (k x y).toReal * f y) := by
  have hs := (summable_real_kernel_row k hk x).1.add
    ((summable_kernel_square_right k hk hsym f hf).prod_factor x)
  apply Summable.of_norm_bounded hs
  intro y
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have h : |f y| ≤ 1 + f y ^ 2 := by
    nlinarith [sq_nonneg (|f y| - 1), sq_abs (f y)]
  have hk0 : 0 ≤ (k x y).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr h)]

/-- The real energy is the pairing of a square-summable function with its Markov defect. -/
theorem realKernelEnergy_eq_operator_pairing {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    Summable (fun x => f x * (f x - ∑' y, (k x y).toReal * f y)) ∧
    realKernelEnergy k f = ∑' x, f x * (f x - ∑' y, (k x y).toReal * f y) := by
  have hp : Summable (fun p : X × X => (k p.1 p.2).toReal *
      (f p.1 * (f p.1 - f p.2))) := by
    convert (summable_kernel_square_left k hk f hf).sub
      (summable_kernel_mul k hk hsym f hf) using 1
    ext ⟨x, y⟩
    ring
  have hrow (x : X) : (∑' y, (k x y).toReal * (f x * (f x - f y))) =
      f x * (f x - ∑' y, (k x y).toReal * f y) := by
    have hkrow := (summable_real_kernel_row k hk x).1
    have hfrow := summable_kernel_apply_row k hk hsym f hf x
    calc
      _ = ∑' y, ((k x y).toReal * (f x * f x) - f x * ((k x y).toReal * f y)) := by
        apply tsum_congr
        intro y
        ring
      _ = (∑' y, (k x y).toReal) * (f x * f x) -
          f x * ∑' y, (k x y).toReal * f y := by
        rw [Summable.tsum_sub (hkrow.mul_right _) (hfrow.mul_left _),
          tsum_mul_right, tsum_mul_left]
      _ = _ := by rw [(summable_real_kernel_row k hk x).2]; ring
  constructor
  · simpa only [hrow] using hp.prod
  · rw [realKernelEnergy_eq_pairing k hk hsym f hf, hp.tsum_prod]
    simp_rw [hrow]

end LatticeProb.Graph.LongRangeKernel
