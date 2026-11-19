import LongRange.Support.Analysis.Semigroup.SymmetricKernel
import LongRange.Support.Prob.JumpChain.Duhamel

/-!
# The transition probabilities of a bounded-rate chain as a real kernel

The singleton masses of the uniformized transition kernel form a real stochastic kernel on the
countable state space. It is the Poisson series of the powers of the uniformized matrix, it is
the identity at time zero, it satisfies the Chapman–Kolmogorov identity, and it is symmetric
when the rates are. Acting on bounded functions, the semigroup law holds pointwise.
-/

namespace LatticeProb.JumpChain.BoundedRates

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The probability of moving from `i` to `j` in time `t`, as a real number. -/
def heatKernel (rates : BoundedRates S) (t : ℝ≥0) (i j : S) : ℝ :=
  (rates.transitionKernel t i {j}).toReal

/-- Transition probabilities are nonnegative. -/
theorem heatKernel_nonneg (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    0 ≤ rates.heatKernel t i j :=
  ENNReal.toReal_nonneg

/-- The transition probability is the Poisson series of powers of the uniformized matrix. -/
theorem heatKernel_eq_tsum (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    rates.heatKernel t i j =
      ∑' n : ℕ, Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial *
        kernelPow rates.p n i j :=
  rates.transitionKernel_real_singleton_eq_kernelPow t i j

/-- Each row of transition probabilities sums to one. -/
theorem hasSum_heatKernel (rates : BoundedRates S) (t : ℝ≥0) (i : S) :
    HasSum (rates.heatKernel t i) 1 := by
  have h1 : ∑' j, rates.heatKernel t i j = 1 := rates.tsum_transitionKernel_real_singleton t i
  have hs : Summable (rates.heatKernel t i) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h1
    exact zero_ne_one h1
  rw [← h1]
  exact hs.hasSum

/-- Transition probabilities are at most one. -/
theorem heatKernel_le_one (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    rates.heatKernel t i j ≤ 1 :=
  kernel_entry_le_one (rates.heatKernel_nonneg t) (rates.hasSum_heatKernel t) i j

/-- Symmetric rates give symmetric transition probabilities. -/
theorem heatKernel_symm (rates : BoundedRates S) (hs : ∀ i j, rates.q i j = rates.q j i)
    (t : ℝ≥0) (i j : S) : rates.heatKernel t i j = rates.heatKernel t j i := by
  rw [rates.heatKernel_eq_tsum, rates.heatKernel_eq_tsum]
  exact tsum_congr fun n ↦ by
    rw [kernelPow_symm rates.p_nonneg rates.hasSum_p (rates.p_symm hs) n i j]

/-- For symmetric rates the transition probabilities form a symmetric stochastic kernel. -/
theorem isSymmKernel_heatKernel (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) :
    IsSymmKernel (rates.heatKernel t) 1 where
  nonneg := rates.heatKernel_nonneg t
  symm := rates.heatKernel_symm hs t
  summable i := (rates.hasSum_heatKernel t i).summable
  tsum_le i := (rates.hasSum_heatKernel t i).tsum_eq.le

open scoped Classical in
/-- At time zero the transition probabilities are those of the identity. -/
theorem heatKernel_zero (rates : BoundedRates S) (i j : S) :
    rates.heatKernel 0 i j = if i = j then 1 else 0 := by
  rw [heatKernel, rates.transitionKernel_zero, Kernel.id_apply,
    Measure.dirac_apply' _ (measurableSet_singleton j)]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- The Chapman–Kolmogorov identity for transition probabilities. -/
theorem heatKernel_add (rates : BoundedRates S) (s t : ℝ≥0) (i j : S) :
    rates.heatKernel (s + t) i j = kernelComp (rates.heatKernel s) (rates.heatKernel t) i j := by
  rw [heatKernel, rates.transitionKernel_add_singleton, kernelComp,
    ENNReal.tsum_toReal_eq fun k ↦ ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)]
  exact tsum_congr fun k ↦ ENNReal.toReal_mul

/-- At time zero the action is the identity. -/
theorem kernelApply_heatKernel_zero (rates : BoundedRates S) (f : S → ℝ) (i : S) :
    kernelApply (rates.heatKernel 0) f i = f i := by
  classical
  rw [kernelApply]
  simp only [rates.heatKernel_zero, ite_mul, one_mul, zero_mul]
  exact tsum_ite_eq' i f

/-- The semigroup law for the action on bounded functions. -/
theorem kernelApply_heatKernel_add (rates : BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (s t : ℝ≥0) {f : S → ℝ} {C : ℝ}
    (hf : ∀ j, |f j| ≤ C) (i : S) :
    kernelApply (rates.heatKernel (s + t)) f i =
      kernelApply (rates.heatKernel s) (kernelApply (rates.heatKernel t) f) i := by
  rw [(rates.isSymmKernel_heatKernel hs s).kernelApply_kernelApply
    (rates.isSymmKernel_heatKernel hs t) hf i]
  exact tsum_congr fun j ↦ by rw [rates.heatKernel_add]

end

end LatticeProb.JumpChain.BoundedRates
