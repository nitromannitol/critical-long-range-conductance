import LongRange.Support.Analysis.Semigroup.HeatKernel
import LongRange.Support.Analysis.Semigroup.DirichletForm

/-!
# First-order splitting of the transition probabilities

Separating the first two terms of the Poisson series writes the transition probabilities at
time `t` as `e^{-Rt}` times the identity, plus `e^{-Rt} R t` times the uniformized matrix, plus
a nonnegative remainder kernel. For symmetric rates the remainder is symmetric and its rows have
mass `1 - e^{-Rt} (1 + R t)`, which is of order `(R t) ^ 2`.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory
open scoped NNReal

noncomputable section

variable {S : Type*}

/-- The uniformized matrix of symmetric rates is a symmetric stochastic kernel. -/
theorem isSymmKernel_p (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i) :
    IsSymmKernel rates.p 1 where
  nonneg := rates.p_nonneg
  symm := rates.p_symm hs
  summable i := (rates.hasSum_p i).summable
  tsum_le i := (rates.hasSum_p i).tsum_eq.le

/-- The first power of the uniformized matrix is the matrix itself. -/
theorem kernelPow_p_one (rates : BoundedRates S) (i j : S) :
    kernelPow rates.p 1 i j = rates.p i j := by
  simp [kernelPow, kernelComp, ite_mul]

/-- The Poisson series of the matrix powers is absolutely summable. -/
theorem summable_poisson_kernelPow (rates : BoundedRates S) {x : ℝ} (hx : 0 ≤ x) (i j : S) :
    Summable fun n : ℕ ↦ Real.exp (-x) * x ^ n / n.factorial * kernelPow rates.p n i j := by
  refine ((Real.summable_pow_div_factorial x).mul_left (Real.exp (-x))).of_nonneg_of_le
    (fun n ↦ mul_nonneg (by positivity) (kernelPow_nonneg rates.p_nonneg n i j)) fun n ↦ ?_
  rw [← mul_div_assoc]
  exact mul_le_of_le_one_right (by positivity)
    (kernel_entry_le_one (kernelPow_nonneg rates.p_nonneg n)
      (kernelPow_hasSum rates.p_nonneg rates.hasSum_p n) i j)

/-- The Poisson series of the transition probabilities from its third term on. -/
def heatRemainder (rates : BoundedRates S) (t : ℝ≥0) (i j : S) : ℝ :=
  ∑' n : ℕ, Real.exp (-(rates.R * t)) * (rates.R * t) ^ (n + 2) / (n + 2).factorial *
    kernelPow rates.p (n + 2) i j

/-- The remainder kernel is nonnegative. -/
theorem heatRemainder_nonneg (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    0 ≤ rates.heatRemainder t i j :=
  tsum_nonneg fun _ ↦ mul_nonneg
    (div_nonneg (mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (mul_nonneg rates.R_pos.le t.2) _)) (Nat.cast_nonneg _))
    (kernelPow_nonneg rates.p_nonneg _ i j)

/-- Symmetric rates give a symmetric remainder kernel. -/
theorem heatRemainder_symm (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    (t : ℝ≥0) (i j : S) : rates.heatRemainder t i j = rates.heatRemainder t j i :=
  tsum_congr fun n ↦ by
    rw [kernelPow_symm rates.p_nonneg rates.hasSum_p (rates.p_symm hs) (n + 2) i j]

/-- The mass of the remainder rows is nonnegative. -/
theorem one_sub_exp_neg_sub_nonneg {x : ℝ} : 0 ≤ 1 - Real.exp (-x) - Real.exp (-x) * x := by
  have h := Real.add_one_le_exp x
  have hpos := Real.exp_pos (-x)
  have hmul : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

open scoped Classical in
/-- The transition probabilities split into identity, one uniformized step, and remainder. -/
theorem heatKernel_split (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    rates.heatKernel t i j =
      Real.exp (-(rates.R * t)) * (if i = j then 1 else 0) +
        Real.exp (-(rates.R * t)) * (rates.R * t) * rates.p i j +
          rates.heatRemainder t i j := by
  have hs := rates.summable_poisson_kernelPow (x := rates.R * t)
    (mul_nonneg rates.R_pos.le t.coe_nonneg) i j
  rw [rates.heatKernel_eq_tsum, ← hs.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    Nat.factorial_zero, Nat.cast_one, div_one, mul_one, pow_one, Nat.factorial_one,
    rates.kernelPow_p_one]
  rfl

/-- The rows of the remainder kernel have mass `1 - e^{-Rt} (1 + R t)`. -/
theorem hasSum_heatRemainder (rates : BoundedRates S) (t : ℝ≥0) (i : S) :
    HasSum (rates.heatRemainder t i)
      (1 - Real.exp (-(rates.R * t)) - Real.exp (-(rates.R * t)) * (rates.R * t)) := by
  classical
  have h0 := (hasSum_ite_eq i (1 : ℝ)).mul_left (Real.exp (-(rates.R * t)))
  have h1 := (rates.hasSum_p i).mul_left (Real.exp (-(rates.R * t)) * (rates.R * t))
  have h := ((rates.hasSum_heatKernel t i).sub h0).sub h1
  simp only [mul_one] at h
  refine h.congr_fun fun j ↦ ?_
  rw [rates.heatKernel_split t i j]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    ring
  · simp only [hij, Ne.symm hij, ite_false]
    ring

/-- For symmetric rates the remainder is a symmetric kernel of row mass `1 - e^{-Rt}(1 + R t)`. -/
theorem isSymmKernel_heatRemainder (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) :
    IsSymmKernel (rates.heatRemainder t)
      (1 - Real.exp (-(rates.R * t)) - Real.exp (-(rates.R * t)) * (rates.R * t)) where
  nonneg := rates.heatRemainder_nonneg t
  symm := rates.heatRemainder_symm hs t
  summable i := (rates.hasSum_heatRemainder t i).summable
  tsum_le i := (rates.hasSum_heatRemainder t i).tsum_eq.le

/-- The action of the transition probabilities on a bounded function, split at first order. -/
theorem kernelApply_heatKernel_split (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) {f : S → ℝ} {C : ℝ}
    (hf : ∀ j, |f j| ≤ C) (i : S) :
    kernelApply (rates.heatKernel t) f i =
      Real.exp (-(rates.R * t)) * f i +
        Real.exp (-(rates.R * t)) * (rates.R * t) * kernelApply rates.p f i +
          kernelApply (rates.heatRemainder t) f i := by
  classical
  have h0 : HasSum (fun j ↦ if j = i then Real.exp (-(rates.R * t)) * f i else 0)
      (Real.exp (-(rates.R * t)) * f i) := hasSum_ite_eq i _
  have h1 := (rates.summable_p_mul i f hf).hasSum.mul_left
    (Real.exp (-(rates.R * t)) * (rates.R * t))
  have h2 := ((rates.isSymmKernel_heatRemainder hs t).summable_mul_of_abs_le hf i).hasSum
  rw [kernelApply]
  refine (((h0.add h1).add h2).congr_fun fun j ↦ ?_).tsum_eq
  rw [rates.heatKernel_split t i j]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    ring
  · simp only [hij, Ne.symm hij, ite_false]
    ring

end

end LatticeProb.JumpChain.BoundedRates
