import LongRange.Support.Analysis.Davies.Perturbation

/-!
# The one-power twisted form estimate

The exponential perturbation of a finite jump form is controlled by its jump carré du champ.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

omit [DecidableEq ι] in
/-- The form under an exponential twist is bounded below by its untwisted value. -/
theorem form_twist_one {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) :
    F.form (fun i ↦ Real.exp (ψ i) * f i) (fun i ↦ Real.exp (-ψ i) * f i) ≥
      F.form f f - Λsq * ∑ i, f i ^ 2 := by
  let err : ι → ι → ℝ := fun i j ↦ F.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2
  have herr (i : ι) : ∑ j, err i j ≤ Λsq := hΛ.2.1 i
  have hweighted : (∑ i, ∑ j, err i j * f i ^ 2) ≤ Λsq * ∑ i, f i ^ 2 := by
    calc
      (∑ i, ∑ j, err i j * f i ^ 2) = ∑ i, (∑ j, err i j) * f i ^ 2 := by
        simp only [Finset.sum_mul]
      _ ≤ ∑ i, Λsq * f i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (herr i) (sq_nonneg _)
      _ = Λsq * ∑ i, f i ^ 2 := by rw [Finset.mul_sum]
  have hswap : (∑ i, ∑ j, err j i * f j ^ 2) = ∑ i, ∑ j, err i j * f i ^ 2 := by
    rw [Finset.sum_comm]
  have hedge (i j : ι) :
      F.q i j * ((Real.exp (ψ j) * f j - Real.exp (ψ i) * f i) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i)) ≥
      F.q i j * (f j - f i) ^ 2 - err i j * f i ^ 2 - err j i * f j ^ 2 := by
    have he : (Real.exp (ψ j) * f j - Real.exp (ψ i) * f i) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i) =
        (Real.exp (ψ j - ψ i) * f j - f i) *
          (Real.exp (ψ i - ψ j) * f j - f i) := by
      rw [Real.exp_sub, Real.exp_sub, Real.exp_neg, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    have h := mul_le_mul_of_nonneg_left (pair_one (f i) (f j) (ψ j - ψ i))
      (F.q_nonneg i j)
    rw [he]
    dsimp only [err]
    rw [F.q_symm j i]
    have hneg : -(ψ j - ψ i) = ψ i - ψ j := by ring
    rw [hneg] at h
    nlinarith
  have hsum : (∑ i, ∑ j,
      F.q i j * ((Real.exp (ψ j) * f j - Real.exp (ψ i) * f i) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i))) ≥
      (∑ i, ∑ j, F.q i j * (f j - f i) ^ 2) -
        (∑ i, ∑ j, err i j * f i ^ 2) - (∑ i, ∑ j, err j i * f j ^ 2) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hedge i j
  have hkill (i : ι) : F.κ i * (Real.exp (ψ i) * f i) *
      (Real.exp (-ψ i) * f i) = F.κ i * f i * f i := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [hswap] at hsum
  have hsum' : (∑ i, ∑ j,
      F.q i j * (Real.exp (ψ j) * f j - Real.exp (ψ i) * f i) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i)) ≥
      (∑ i, ∑ j, F.q i j * (f j - f i) * (f j - f i)) -
        (∑ i, ∑ j, err i j * f i ^ 2) - (∑ i, ∑ j, err i j * f i ^ 2) := by
    simpa only [mul_assoc, pow_two] using hsum
  unfold form
  simp_rw [hkill]
  linarith

end
end LatticeProb.Davies.FiniteJumpForm
