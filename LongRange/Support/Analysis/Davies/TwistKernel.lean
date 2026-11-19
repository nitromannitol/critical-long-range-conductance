import LongRange.Support.Analysis.Davies.TwistBound

/-!
# Kernels of finite twisted semigroups

The kernel identities used in the duality and semigroup-squaring step.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The matrix kernel of the conjugated finite semigroup. -/
def twistKernel (ψ : ι → ℝ) (t : ℝ) (i j : ι) : ℝ :=
  Real.exp (ψ i) * F.semigroup t i j * Real.exp (-ψ j)

/-- The twisted semigroup acts by its matrix kernel. -/
theorem twist_eq_sum (ψ f : ι → ℝ) (t : ℝ) (i : ι) :
    F.twist ψ f t i = ∑ j, F.twistKernel ψ t i j * f j := by
  simp only [twist, twistKernel, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Twisted kernels have nonnegative entries at nonnegative times. -/
theorem twistKernel_nonneg (ψ : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    0 ≤ F.twistKernel ψ t i j := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (F.semigroup_nonneg t ht i j))
    (Real.exp_pos _).le

/-- Transposition of the twisted kernel reverses the perturbation. -/
theorem twistKernel_neg_flip (ψ : ι → ℝ) (t : ℝ) (i j : ι) :
    F.twistKernel (-ψ) t j i = F.twistKernel ψ t i j := by
  have hs := congrFun (congrFun (F.semigroup_transpose t) j) i
  change F.semigroup t i j = F.semigroup t j i at hs
  simp only [twistKernel, Pi.neg_apply, neg_neg]
  rw [hs]
  ring

/-- Twisted kernels compose according to the semigroup law. -/
theorem twistKernel_add (ψ : ι → ℝ) (s t : ℝ) (i j : ι) :
    F.twistKernel ψ (s + t) i j = ∑ k, F.twistKernel ψ s i k * F.twistKernel ψ t k j := by
  rw [twistKernel, F.semigroup_add]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, twistKernel]
  apply Finset.sum_congr rfl
  intro k _
  have he : Real.exp (-ψ k) * Real.exp (ψ k) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = (Real.exp (ψ i) * (F.semigroup s i k * F.semigroup t k j) * Real.exp (-ψ j)) *
        (Real.exp (-ψ k) * Real.exp (ψ k)) := by rw [he, mul_one]
    _ = _ := by ring

end
end LatticeProb.Davies.FiniteJumpForm
