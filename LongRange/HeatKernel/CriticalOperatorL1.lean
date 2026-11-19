import LongRange.HeatKernel.CriticalOperatorHilbert

/-!
# Absolute summability under symmetric Markov operators

Symmetric Markov operators contract the absolute sum on counting measure.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The weighted absolute values are summable over pairs. -/
theorem summable_kernel_abs_right {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : X → ℝ) (hf : Summable (fun x => |f x|)) :
    Summable (fun p : X × X => (k p.1 p.2).toReal * |f p.2|) := by
  have h : (∑' p : X × X, k p.1 p.2 * ENNReal.ofReal |f p.2|) < ∞ := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    simp_rw [hsym, ENNReal.tsum_mul_right, hk, one_mul]
    exact hf.tsum_ofReal_lt_top
  have hs := ENNReal.summable_toReal h.ne
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] using hs

/-- A symmetric Markov operator preserves absolute summability and contracts its sum. -/
theorem markovOperatorCLM_summable_abs {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : lp (fun _ : X => ℝ) 2) (hf : Summable (fun x => |f x|)) :
    Summable (fun x => |markovOperatorCLM k hk hsym f x|) ∧
      (∑' x, |markovOperatorCLM k hk hsym f x|) ≤ ∑' x, |f x| := by
  have hs := summable_kernel_abs_right k hk hsym f hf
  have hrow (x : X) : Summable (fun y => (k x y).toReal * |f y|) := hs.prod_factor x
  have hpoint (x : X) : |markovOperatorCLM k hk hsym f x| ≤
      ∑' y, (k x y).toReal * |f y| := by
    change |∑' y, (k x y).toReal * f y| ≤ _
    have hnorm : Summable (fun y => ‖(k x y).toReal * f y‖) := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using hrow x
    have h := norm_tsum_le_tsum_norm hnorm
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using h
  have hsums : Summable (fun x => ∑' y, (k x y).toReal * |f y|) :=
    (summable_prod_of_nonneg
      (fun p => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))).1 hs |>.2
  have hout : Summable (fun x => |markovOperatorCLM k hk hsym f x|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint hsums
  refine ⟨hout, (hout.tsum_le_tsum hpoint hsums).trans ?_⟩
  have hcomm : (∑' x, ∑' y, (k x y).toReal * |f y|) =
      ∑' y, ∑' x, (k x y).toReal * |f y| := hs.tsum_comm.symm
  rw [hcomm]
  have hcol (y : X) : (∑' x, (k x y).toReal * |f y|) = |f y| := by
    simp_rw [hsym]
    rw [tsum_mul_right, (summable_real_kernel_row k hk y).2, one_mul]
  simp_rw [hcol]
  exact le_rfl

/-- Iterates of a symmetric Markov operator contract the absolute sum. -/
theorem markovOperatorCLM_pow_summable_abs {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : lp (fun _ : X => ℝ) 2) (hf : Summable (fun x => |f x|)) (n : ℕ) :
    Summable (fun x => |(markovOperatorCLM k hk hsym ^ n) f x|) ∧
      (∑' x, |(markovOperatorCLM k hk hsym ^ n) f x|) ≤ ∑' x, |f x| := by
  induction n with
  | zero => simpa using And.intro hf (le_refl (∑' x, |f x|))
  | succ n ih =>
      have h := markovOperatorCLM_summable_abs k hk hsym
        ((markovOperatorCLM k hk hsym ^ n) f) ih.1
      rw [pow_succ', mul_apply_eq_comp]
      exact ⟨h.1, h.2.trans ih.2⟩

end LatticeProb.Graph.LongRangeKernel
