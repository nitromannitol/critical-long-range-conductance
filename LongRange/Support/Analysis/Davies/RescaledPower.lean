import LongRange.Support.Analysis.Davies.FiniteDavies

/-!
# Rescaled twisted power sums

Differentiation and the form bound for exponentially rescaled power sums.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The rescaled even power sum has the expected product derivative. -/
theorem hasDerivAt_rescaled_powSum (ψ f : ι → ℝ) (p : ℕ) (c t : ℝ) :
    HasDerivAt (fun s ↦ Real.exp (-(2 * (p : ℝ) * c) * s) *
      ∑ i, (F.twist ψ f s i) ^ (2 * p))
      (Real.exp (-(2 * (p : ℝ) * c) * t) *
        (-(2 * (p : ℝ)) * F.form
          (fun i ↦ Real.exp (ψ i) * (F.twist ψ f t i) ^ (2 * p - 1))
          (fun i ↦ Real.exp (-ψ i) * F.twist ψ f t i) -
          (2 * (p : ℝ) * c) * ∑ i, (F.twist ψ f t i) ^ (2 * p))) t := by
  have he : HasDerivAt (fun s ↦ Real.exp (-(2 * (p : ℝ) * c) * s))
      (Real.exp (-(2 * (p : ℝ) * c) * t) * (-(2 * (p : ℝ) * c))) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul (-(2 * (p : ℝ) * c))).exp
  have hn := F.hasDerivAt_powSum ψ f p t
  have hh := he.mul hn
  change HasDerivAt (fun s ↦ Real.exp (-(2 * (p : ℝ) * c) * s) *
      ∑ i, (F.twist ψ f s i) ^ (2 * p)) _ t at hh
  convert hh using 1; ring

/-- The rescaled power-sum derivative is bounded by the unperturbed form. -/
theorem rescaled_powSum_deriv_le_form {ψ : ι → ℝ} {Λsq : ℝ}
    (hΛ : F.LambdaBound ψ Λsq) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (p : ℕ) (hp : 1 ≤ p) (δ : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    deriv (fun s ↦ Real.exp (-(2 * (p : ℝ) *
        (((2 * (p : ℝ) + 1) * Λsq) + δ / p)) * s) *
      ∑ i, (F.twist ψ f s i) ^ (2 * p)) t ≤
    Real.exp (-(2 * (p : ℝ) * (((2 * (p : ℝ) + 1) * Λsq) + δ / p)) * t) *
      (-F.form (fun i ↦ (F.twist ψ f t i) ^ p)
        (fun i ↦ (F.twist ψ f t i) ^ p) -
        2 * δ * ∑ i, (F.twist ψ f t i) ^ (2 * p)) := by
  let r : ℝ := (2 * (p : ℝ) + 1) * Λsq
  let c : ℝ := r + δ / p
  let N : ℝ := ∑ i, (F.twist ψ f t i) ^ (2 * p)
  let E : ℝ := F.form
    (fun i ↦ Real.exp (ψ i) * (F.twist ψ f t i) ^ (2 * p - 1))
    (fun i ↦ Real.exp (-ψ i) * F.twist ψ f t i)
  let Q : ℝ := F.form (fun i ↦ (F.twist ψ f t i) ^ p)
    (fun i ↦ (F.twist ψ f t i) ^ p)
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hform := F.form_twist_pow hΛ (F.twist ψ f t)
    (fun i ↦ F.twist_nonneg ψ f hf ht i) p hp
  change E ≥ Q / (2 * (p : ℝ)) - r * N at hform
  have hP : 0 < 2 * (p : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hform hP.le
  have hc : 2 * (p : ℝ) * c = 2 * (p : ℝ) * r + 2 * δ := by
    dsimp only [c]
    field_simp
  have hin : -(2 * (p : ℝ)) * E - (2 * (p : ℝ) * c) * N ≤ -Q - 2 * δ * N := by
    rw [hc]
    field_simp at hmul
    nlinarith
  have he := F.hasDerivAt_rescaled_powSum ψ f p c t
  change deriv (fun s ↦ Real.exp (-(2 * (p : ℝ) * c) * s) *
      ∑ i, (F.twist ψ f s i) ^ (2 * p)) t ≤
    Real.exp (-(2 * (p : ℝ) * c) * t) * (-Q - 2 * δ * N)
  rw [he.deriv]
  exact mul_le_mul_of_nonneg_left hin (Real.exp_pos _).le

end
end LatticeProb.Davies.FiniteJumpForm
