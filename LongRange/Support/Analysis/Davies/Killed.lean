import LongRange.Support.Analysis.Davies.FiniteForm
import LongRange.Support.External.ChenKimKumagaiWang
import LongRange.Support.Prob.JumpChain.KilledL2

/-!
# Finite killed jump forms

Restriction to a finite set retains the outgoing jump rate as a killing term.
The finite Davies functional is controlled by the full-space functional.
-/

namespace LatticeProb.Davies

open External
open scoped Matrix.Norms.Operator ENNReal

noncomputable section

variable {S : Type*} (rates : JumpChain.BoundedRates S)

/-- Restrict a symmetric jump chain to a finite set, retaining outgoing jumps as killing. -/
def killedForm (hs : ∀ i j, rates.q i j = rates.q j i) (U : Finset S) :
    FiniteJumpForm U := by
  classical
  exact
    { q := fun x y ↦ rates.q x y
      κ := fun x ↦ (∑' y, rates.q x y) - ∑ y : U, rates.q x y
      q_nonneg := fun x y ↦ rates.q_nonneg x y
      q_symm := fun x y ↦ hs x y
      κ_nonneg := fun x ↦ by
        apply sub_nonneg.mpr
        simpa only [Finset.sum_coe_sort] using
          (rates.summable x).sum_le_tsum U (fun y _ ↦ rates.q_nonneg x y) }

private theorem finite_sum_le_toReal (U : Finset S) (f : S → ℝ) (M : ℝ≥0∞)
    (hf : ∀ y, 0 ≤ f y) (hM : M ≠ ⊤) (h : (∑' y, ENNReal.ofReal (f y)) ≤ M) :
    (∑ y ∈ U, f y) ≤ M.toReal := by
  have hsum : 0 ≤ ∑ y ∈ U, f y := Finset.sum_nonneg (fun y _ ↦ hf y)
  rw [← ENNReal.toReal_ofReal hsum]
  apply ENNReal.toReal_mono hM
  rw [ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ hf y)]
  exact (ENNReal.sum_le_tsum U).trans h

/-- The finite Davies functional is bounded by its full-space counterpart. -/
theorem killedForm_lambdaBound (hs : ∀ i j, rates.q i j = rates.q j i)
    (U : Finset S) (ψ : S → ℝ) (hΛ : ckkwLambdaSq rates ψ ≠ ⊤) :
    (killedForm rates hs U).LambdaBound (ψ ∘ (↑)) (ckkwLambdaSq rates ψ).toReal := by
  classical
  refine ⟨ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro i
    change (∑ j : U, rates.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2) ≤ _
    rw [show (∑ j : U, rates.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2) =
      ∑ j ∈ U, rates.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2 from
        Finset.sum_coe_sort U (fun j ↦ rates.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2)]
    have heq (y : S) : rates.q i y * (Real.exp (ψ y - ψ i) - 1) ^ 2 / 2 =
        (1 / 2 : ℝ) * rates.q i y * (Real.exp (ψ y - ψ i) - 1) ^ 2 := by ring
    simp_rw [heq]
    apply finite_sum_le_toReal U _ _ (fun y ↦ mul_nonneg (mul_nonneg (by norm_num) (rates.q_nonneg i y)) (sq_nonneg _)) hΛ
    exact (le_iSup (fun x ↦ ∑' j, ENNReal.ofReal
      ((1 / 2 : ℝ) * rates.q x j * (Real.exp (ψ j - ψ x) - 1) ^ 2)) i).trans
      (le_max_left _ _)
  · intro i
    change (∑ j : U, rates.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2 / 2) ≤ _
    rw [show (∑ j : U, rates.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2 / 2) =
      ∑ j ∈ U, rates.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2 / 2 from
        Finset.sum_coe_sort U (fun j ↦ rates.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2 / 2)]
    have heq (y : S) : rates.q i y * (Real.exp (ψ i - ψ y) - 1) ^ 2 / 2 =
        (1 / 2 : ℝ) * rates.q i y * (Real.exp (ψ i - ψ y) - 1) ^ 2 := by ring
    simp_rw [heq]
    apply finite_sum_le_toReal U _ _ (fun y ↦ mul_nonneg (mul_nonneg (by norm_num) (rates.q_nonneg i y)) (sq_nonneg _)) hΛ
    exact (le_iSup (fun x ↦ ∑' j, ENNReal.ofReal
      ((1 / 2 : ℝ) * rates.q x j * (Real.exp (ψ x - ψ j) - 1) ^ 2)) i).trans
      (le_max_right _ _)

end
end LatticeProb.Davies
