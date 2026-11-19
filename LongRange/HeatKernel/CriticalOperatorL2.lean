import LongRange.HeatKernel.CriticalOperator

/-!
# Square-summability of the Markov operator

A symmetric Markov kernel contracts the counting-space squared norm.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- A Markov row obeys the square inequality. -/
theorem kernel_apply_sq_le {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) (x : X) :
    (∑' y, (k x y).toReal * f y) ^ 2 ≤
      ∑' y, (k x y).toReal * f y ^ 2 := by
  let t : ℝ := ∑' y, (k x y).toReal * f y
  have hkrow := (summable_real_kernel_row k hk x).1
  have hkr := (summable_real_kernel_row k hk x).2
  have hfrow := summable_kernel_apply_row k hk hsym f hf x
  have hsrow := (summable_kernel_square_right k hk hsym f hf).prod_factor x
  have hvar : Summable (fun y => (k x y).toReal * (f y - t) ^ 2) := by
    convert (hsrow.sub (hfrow.mul_left (2 * t))).add (hkrow.mul_right (t ^ 2)) using 1
    ext y
    ring
  have hv : 0 ≤ ∑' y, (k x y).toReal * (f y - t) ^ 2 :=
    tsum_nonneg (fun y => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  have heq : (∑' y, (k x y).toReal * (f y - t) ^ 2) =
      (∑' y, (k x y).toReal * f y ^ 2) - 2 * t * t + t ^ 2 := by
    calc
      _ = ∑' y, ((k x y).toReal * f y ^ 2 - 2 * t * ((k x y).toReal * f y) +
          (k x y).toReal * t ^ 2) := by
        apply tsum_congr
        intro y
        ring
      _ = _ := by
        rw [Summable.tsum_add (hsrow.sub (hfrow.mul_left (2 * t))) (hkrow.mul_right _),
          Summable.tsum_sub hsrow (hfrow.mul_left _), tsum_mul_left, tsum_mul_right, hkr]
        simp only [one_mul]
        rfl
  rw [heq] at hv
  dsimp only [t] at hv ⊢
  nlinarith

/-- Applying a symmetric Markov kernel preserves square-summability. -/
theorem kernel_apply_square_summable {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    (∑' x, ENNReal.ofReal ((∑' y, (k x y).toReal * f y) ^ 2)) < ∞ := by
  have hs : Summable (fun x => ∑' y, (k x y).toReal * f y ^ 2) :=
    (summable_kernel_square_right k hk hsym f hf).prod
  have hout : Summable (fun x => (∑' y, (k x y).toReal * f y) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun x => sq_nonneg _) (kernel_apply_sq_le k hk hsym f hf) hs
  exact hout.tsum_ofReal_lt_top

/-- A symmetric Markov kernel contracts the counting-space squared norm. -/
theorem kernel_apply_sq_tsum_le {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    (∑' x, (∑' y, (k x y).toReal * f y) ^ 2) ≤ ∑' x, f x ^ 2 := by
  have ha := summable_kernel_square_left k hk f hf
  have hb := summable_kernel_square_right k hk hsym f hf
  have hs : Summable (fun x => ∑' y, (k x y).toReal * f y ^ 2) := hb.prod
  have hout : Summable (fun x => (∑' y, (k x y).toReal * f y) ^ 2) := by
    exact Summable.of_nonneg_of_le (fun x => sq_nonneg _) (kernel_apply_sq_le k hk hsym f hf) hs
  have hswap : (∑' p : X × X, (k p.1 p.2).toReal * f p.2 ^ 2) =
      ∑' p : X × X, (k p.1 p.2).toReal * f p.1 ^ 2 := by
    rw [← (Equiv.prodComm X X).tsum_eq (fun p : X × X => (k p.1 p.2).toReal * f p.1 ^ 2)]
    apply tsum_congr
    intro ⟨x, y⟩
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [hsym]
  calc
    _ ≤ ∑' x, ∑' y, (k x y).toReal * f y ^ 2 :=
      hout.tsum_le_tsum (kernel_apply_sq_le k hk hsym f hf) hs
    _ = ∑' p : X × X, (k p.1 p.2).toReal * f p.2 ^ 2 := hb.tsum_prod.symm
    _ = ∑' p : X × X, (k p.1 p.2).toReal * f p.1 ^ 2 := hswap
    _ = ∑' x, ∑' y, (k x y).toReal * f x ^ 2 := ha.tsum_prod
    _ = ∑' x, f x ^ 2 := by
      apply tsum_congr
      intro x
      rw [tsum_mul_right, (summable_real_kernel_row k hk x).2, one_mul]

end LatticeProb.Graph.LongRangeKernel
