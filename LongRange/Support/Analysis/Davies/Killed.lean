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
open scoped Matrix.Norms.Operator ENNReal NNReal

noncomputable section
attribute [local instance] Classical.propDecidable

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

/-- The killed Poisson kernel agrees with the finite-form matrix exponential. -/
theorem killedKernel_eq_semigroup (hs : ∀ i j, rates.q i j = rates.q j i)
    (U : Finset S) (t : ℝ≥0) (x y : U) :
    rates.killedKernel (U : Set S) t x y = (killedForm rates hs U).semigroup t x y := by
  classical
  let A : Matrix U U ℝ := Matrix.of fun a b ↦ rates.p a b
  let G := (killedForm rates hs U).gen
  have heq : (rates.R * (t : ℝ)) • A = (t : ℝ) • G +
      algebraMap ℝ (Matrix U U ℝ) (rates.R * t) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, A, G,
      FiniteJumpForm.gen, Matrix.of_apply, killedForm, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    rw [rates.p_eq_add]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, rates.q_self, zero_div, add_zero, add_sub_cancel]
      field_simp [rates.R_pos.ne']
      ring
    · have hval : (j : S) ≠ i := fun h ↦ hij (Subtype.ext h.symm)
      simp only [ite_eq_right hij, ite_eq_right hval, zero_add]
      field_simp [rates.R_pos.ne']
      ring
  rw [rates.killedKernel_eq_matrix_exp (U : Set S) t x y]
  change Real.exp (-(rates.R * t)) * (NormedSpace.exp ((rates.R * (t : ℝ)) • A)) x y =
    (NormedSpace.exp ((t : ℝ) • G)) x y
  have hc : Commute ((t : ℝ) • G)
      (algebraMap ℝ (Matrix U U ℝ) (rates.R * t)) := (Algebra.commutes _ _).symm
  have hexp : NormedSpace.exp ((rates.R * (t : ℝ)) • A) =
      Real.exp (rates.R * t) • NormedSpace.exp ((t : ℝ) • G) := by
    calc
      _ = NormedSpace.exp ((t : ℝ) • G) *
          NormedSpace.exp (algebraMap ℝ (Matrix U U ℝ) (rates.R * t)) := by
            rw [heq]
            exact NormedSpace.exp_add_of_commute hc
      _ = NormedSpace.exp ((t : ℝ) • G) *
          algebraMap ℝ (Matrix U U ℝ) (Real.exp (rates.R * t)) := by
            have hm : algebraMap ℝ (Matrix U U ℝ) (Real.exp (rates.R * t)) =
                NormedSpace.exp (algebraMap ℝ (Matrix U U ℝ) (rates.R * t)) := by
              rw [Real.exp_eq_exp_ℝ]
              exact NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (rates.R * t)
            rw [hm]
      _ = _ := by
        rw [← Algebra.commutes (Real.exp (rates.R * t)) (NormedSpace.exp ((t : ℝ) • G)),
          ← Algebra.smul_def]
  rw [hexp]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Real.exp_neg]
  have hpos : Real.exp (rates.R * t) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

end
end LatticeProb.Davies
