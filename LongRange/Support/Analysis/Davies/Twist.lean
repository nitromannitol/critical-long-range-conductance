import LongRange.Support.Analysis.Davies.FiniteForm

/-!
# Conjugated finite semigroups

Positivity and differentiation for exponential conjugations of finite jump semigroups.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The conjugated semigroup preserves nonnegative functions. -/
theorem twist_nonneg (ψ f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {t : ℝ} (ht : 0 ≤ t)
    (i : ι) : 0 ≤ F.twist ψ f t i := by
  unfold twist
  apply mul_nonneg (Real.exp_pos _).le
  change 0 ≤ ∑ j, F.semigroup t i j * (Real.exp (-ψ j) * f j)
  exact Finset.sum_nonneg fun j _ ↦
    mul_nonneg (F.semigroup_nonneg t ht i j) (mul_nonneg (Real.exp_pos _).le (hf j))

/-- Exponential conjugation of the semigroup is differentiable in time. -/
theorem hasDerivAt_twist (ψ f : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (fun s ↦ F.twist ψ f s i)
      (Real.exp (ψ i) * (F.gen *ᵥ (fun j ↦ Real.exp (-ψ j) * F.twist ψ f t j)) i) t := by
  have ht := (hasDerivAt_pi.mp
    (F.hasDerivAt_semigroup_mulVec (fun j ↦ Real.exp (-ψ j) * f j) t)) i
  have hv : (fun j ↦ Real.exp (-ψ j) * F.twist ψ f t j) =
      F.semigroup t *ᵥ (fun j ↦ Real.exp (-ψ j) * f j) := by
    funext j
    simp only [twist, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [hv]
  exact ht.const_mul (Real.exp (ψ i))

/-- A conjugated semigroup at any real time sends a nonzero function to a nonzero function. -/
theorem twist_ne_zero (ψ f : ι → ℝ) (hf : f ≠ 0) (t : ℝ) : F.twist ψ f t ≠ 0 := by
  intro h
  let w : ι → ℝ := fun j ↦ Real.exp (-ψ j) * f j
  have hw : F.semigroup t *ᵥ w = 0 := by
    funext i
    have hi := congrFun h i
    change Real.exp (ψ i) * (F.semigroup t *ᵥ w) i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (Real.exp_ne_zero _)
  have hinv : F.semigroup (-t) * F.semigroup t = 1 := by
    rw [← F.semigroup_add, neg_add_cancel]
    simp [semigroup, NormedSpace.exp_zero]
  have hz := congrArg (fun g : ι → ℝ ↦ F.semigroup (-t) *ᵥ g) hw
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] at hz
  apply hf
  funext i
  have hi := congrFun hz i
  change Real.exp (-ψ i) * f i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left (Real.exp_ne_zero _)

/-- A single coordinate picks out an entry of the conjugated semigroup. -/
theorem twist_single (ψ : ι → ℝ) (t : ℝ) (i j : ι) :
    F.twist ψ (Pi.single j 1) t i =
      Real.exp (ψ i) * F.semigroup t i j * Real.exp (-ψ j) := by
  simp [twist, Matrix.mulVec, dotProduct, Pi.single_apply, mul_assoc]

end
end LatticeProb.Davies.FiniteJumpForm
