import LongRange.Support.Analysis.Davies.PowerPerturbation
import LongRange.Support.Analysis.Davies.TwistedForm

/-!
# The power twisted form estimate

The nonlinear two-point inequality yields the finite-form perturbation bound.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] (F : FiniteJumpForm ι)

/-- The power perturbation estimate for a finite symmetric jump form. -/
theorem form_twist_pow {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℕ) (hp : 1 ≤ p) :
    F.form (fun i ↦ Real.exp (ψ i) * f i ^ (2 * p - 1))
        (fun i ↦ Real.exp (-ψ i) * f i) ≥
      F.form (fun i ↦ f i ^ p) (fun i ↦ f i ^ p) / (2 * p) -
        (2 * p + 1) * Λsq * ∑ i, f i ^ (2 * p) := by
  let P : ℝ := 2 * p
  let err : ι → ι → ℝ := fun i j ↦ F.q i j *
    ((Real.exp (ψ j - ψ i) - 1) ^ 2 + (Real.exp (ψ i - ψ j) - 1) ^ 2) / 2
  have hP : 1 ≤ P := by
    dsimp [P]
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have herr (i : ι) : ∑ j, err i j ≤ 2 * Λsq := by
    have h₁ := hΛ.2.1 i
    have h₂ := hΛ.2.2 i
    dsimp only [err]
    simp only [mul_add, add_div, Finset.sum_add_distrib]
    linarith
  have herr_symm (i j : ι) : err j i = err i j := by
    dsimp [err]
    rw [F.q_symm j i]
    ring
  have hweighted : (∑ i, ∑ j, err i j * f i ^ (2 * p)) ≤
      2 * Λsq * ∑ i, f i ^ (2 * p) := by
    calc
      (∑ i, ∑ j, err i j * f i ^ (2 * p)) =
          ∑ i, (∑ j, err i j) * f i ^ (2 * p) := by simp only [Finset.sum_mul]
      _ ≤ ∑ i, (2 * Λsq) * f i ^ (2 * p) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (herr i) (pow_nonneg (hf i) _)
      _ = 2 * Λsq * ∑ i, f i ^ (2 * p) := by rw [Finset.mul_sum]
  have hswap : (∑ i, ∑ j, err i j * f j ^ (2 * p)) =
      ∑ i, ∑ j, err i j * f i ^ (2 * p) := by
    rw [Finset.sum_comm]
    simp_rw [herr_symm]
  have hedge (i j : ι) :
      F.q i j * ((Real.exp (ψ j) * f j ^ (2 * p - 1) -
          Real.exp (ψ i) * f i ^ (2 * p - 1)) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i)) ≥
      F.q i j * (f j ^ p - f i ^ p) ^ 2 / P - (P + 1) / 2 *
        (err i j * f i ^ (2 * p) + err i j * f j ^ (2 * p)) := by
    have he : (Real.exp (ψ j) * f j ^ (2 * p - 1) -
          Real.exp (ψ i) * f i ^ (2 * p - 1)) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i) =
        (Real.exp (ψ j - ψ i) * f j ^ (2 * p - 1) - f i ^ (2 * p - 1)) *
          (Real.exp (ψ i - ψ j) * f j - f i) := by
      rw [Real.exp_sub, Real.exp_sub, Real.exp_neg, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    have h := mul_le_mul_of_nonneg_left (pair_pow (hf i) (hf j) p hp (ψ j - ψ i))
      (F.q_nonneg i j)
    rw [he]
    dsimp only [err, P]
    have hneg : -(ψ j - ψ i) = ψ i - ψ j := by ring
    rw [hneg] at h
    convert h using 1; ring
  have hsum : (∑ i, ∑ j,
      F.q i j * ((Real.exp (ψ j) * f j ^ (2 * p - 1) -
          Real.exp (ψ i) * f i ^ (2 * p - 1)) *
        (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i))) ≥
      (∑ i, ∑ j, F.q i j * (f j ^ p - f i ^ p) ^ 2) / P -
        (P + 1) * (∑ i, ∑ j, err i j * f i ^ (2 * p)) := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hedge i j
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.mul_sum] at h
    rw [hswap] at h
    linarith
  have hexp : 2 * p - 1 + 1 = 2 * p := by omega
  have hpow (i : ι) : (f i ^ p) ^ 2 = f i ^ (2 * p) := by
    rw [← pow_mul]
    congr 1
    omega
  have hkill (i : ι) : F.κ i * (Real.exp (ψ i) * f i ^ (2 * p - 1)) *
      (Real.exp (-ψ i) * f i) = F.κ i * f i ^ (2 * p) := by
    calc
      _ = F.κ i * (f i ^ (2 * p - 1) * f i) := by
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ = _ := by rw [← pow_succ, hexp]
  have hkill_nonneg : 0 ≤ ∑ i, F.κ i * f i ^ (2 * p) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (F.κ_nonneg i) (pow_nonneg (hf i) _)
  have hkill_le : (∑ i, F.κ i * f i ^ (2 * p)) / P ≤
      ∑ i, F.κ i * f i ^ (2 * p) := div_le_self hkill_nonneg hP
  have herror := mul_le_mul_of_nonneg_left hweighted (show 0 ≤ P + 1 by linarith)
  have hsum' : (∑ i, ∑ j, F.q i j *
      (Real.exp (ψ j) * f j ^ (2 * p - 1) - Real.exp (ψ i) * f i ^ (2 * p - 1)) *
      (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i)) ≥
      (∑ i, ∑ j, F.q i j * (f j ^ p - f i ^ p) * (f j ^ p - f i ^ p)) / P -
        (P + 1) * (∑ i, ∑ j, err i j * f i ^ (2 * p)) := by
    simpa only [mul_assoc, pow_two] using hsum
  have hsquared (i : ι) : F.κ i * f i ^ p * f i ^ p = F.κ i * f i ^ (2 * p) := by
    rw [mul_assoc, ← pow_two, hpow]
  unfold form
  dsimp only
  simp_rw [hkill, hsquared]
  change (∑ i, ∑ j, F.q i j *
      (Real.exp (ψ j) * f j ^ (2 * p - 1) - Real.exp (ψ i) * f i ^ (2 * p - 1)) *
      (Real.exp (-ψ j) * f j - Real.exp (-ψ i) * f i)) / 2 +
      (∑ i, F.κ i * f i ^ (2 * p)) ≥
      ((∑ i, ∑ j, F.q i j * (f j ^ p - f i ^ p) * (f j ^ p - f i ^ p)) / 2 +
        ∑ i, F.κ i * f i ^ (2 * p)) / P - (P + 1) * Λsq * ∑ i, f i ^ (2 * p)
  rw [add_div]
  have hdiv (u : ℝ) : u / 2 / P = (u / P) / 2 := by ring
  rw [hdiv]
  nlinarith

end
end LatticeProb.Davies.FiniteJumpForm
