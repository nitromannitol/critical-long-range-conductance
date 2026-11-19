import LongRange.Support.Analysis.Davies.Twist
import LongRange.Support.Analysis.Davies.TwistedPowerForm

/-!
# Power sums of a twisted finite semigroup

Time derivatives and estimates for the finite sums used in Davies iteration.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The perturbation rate used for each power in Davies iteration. -/
def levelRate (Λsq : ℝ) (p : ℕ) : ℝ :=
  if p = 1 then Λsq else (2 * p + 1) * Λsq

/-- The derivative of an even power sum of the twisted semigroup. -/
theorem hasDerivAt_powSum (ψ f : ι → ℝ) (p : ℕ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∑ i, (F.twist ψ f s i) ^ (2 * p))
      (-(2 * p : ℝ) * F.form
        (fun i ↦ Real.exp (ψ i) * (F.twist ψ f t i) ^ (2 * p - 1))
        (fun i ↦ Real.exp (-ψ i) * F.twist ψ f t i)) t := by
  let u : ι → ℝ := fun i ↦ Real.exp (ψ i) * (F.twist ψ f t i) ^ (2 * p - 1)
  let v : ι → ℝ := fun i ↦ Real.exp (-ψ i) * F.twist ψ f t i
  have hsum : HasDerivAt (fun s ↦ ∑ i, (F.twist ψ f s i) ^ (2 * p))
      (∑ i, ((2 * p : ℕ) : ℝ) * (F.twist ψ f t i) ^ (2 * p - 1) *
        (Real.exp (ψ i) * (F.gen *ᵥ v) i)) t := by
    exact HasDerivAt.fun_sum fun i _ ↦ (F.hasDerivAt_twist ψ f t i).pow (2 * p)
  have heq : (∑ i, ((2 * p : ℕ) : ℝ) * (F.twist ψ f t i) ^ (2 * p - 1) *
        (Real.exp (ψ i) * (F.gen *ᵥ v) i)) =
      -(2 * p : ℝ) * F.form u v := by
    calc
      _ = (2 * (p : ℝ)) * ∑ i, u i * (F.gen *ᵥ v) i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [u]
        push_cast
        ring
      _ = -(2 * p : ℝ) * F.form u v := by
        rw [F.sum_mul_gen_mulVec]
        ring
  rw [← heq]
  exact hsum

omit [DecidableEq ι] in
/-- The twisted form is bounded below by its power-dependent error term. -/
theorem form_twist_level {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℕ) (hp : 1 ≤ p) :
    -levelRate Λsq p * (∑ i, f i ^ (2 * p)) ≤
      F.form (fun i ↦ Real.exp (ψ i) * f i ^ (2 * p - 1))
        (fun i ↦ Real.exp (-ψ i) * f i) := by
  by_cases hp1 : p = 1
  · subst p
    have h₁ := F.form_twist_one hΛ f
    have h₂ := F.form_self_nonneg f
    simp only [levelRate, ↓reduceIte, Nat.reduceMul, Nat.reduceSub, pow_one] at *
    linarith
  · have h₁ := F.form_twist_pow hΛ f hf p hp
    have h₂ := F.form_self_nonneg (fun i ↦ f i ^ p)
    have h₃ : 0 ≤ F.form (fun i ↦ f i ^ p) (fun i ↦ f i ^ p) / (2 * p : ℝ) :=
      div_nonneg h₂ (by positivity)
    simp only [levelRate, ite_eq_right hp1]
    linarith

/-- The exponentially compensated even power sum decreases at nonnegative times. -/
theorem antitoneOn_level {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℕ) (hp : 1 ≤ p) :
    AntitoneOn (fun t ↦ Real.exp (-(2 * (p : ℝ) * levelRate Λsq p) * t) *
      ∑ i, (F.twist ψ f t i) ^ (2 * p)) (Set.Ici 0) := by
  let r := levelRate Λsq p
  let N : ℝ → ℝ := fun t ↦ ∑ i, (F.twist ψ f t i) ^ (2 * p)
  let E : ℝ → ℝ := fun t ↦ F.form
    (fun i ↦ Real.exp (ψ i) * (F.twist ψ f t i) ^ (2 * p - 1))
    (fun i ↦ Real.exp (-ψ i) * F.twist ψ f t i)
  have hd (t : ℝ) : HasDerivAt (fun s ↦ Real.exp (-(2 * (p : ℝ) * r) * s) * N s)
      (Real.exp (-(2 * (p : ℝ) * r) * t) *
        (-(2 * (p : ℝ)) * E t - (2 * (p : ℝ) * r) * N t)) t := by
    have he : HasDerivAt (fun s ↦ Real.exp (-(2 * (p : ℝ) * r) * s))
        (Real.exp (-(2 * (p : ℝ) * r) * t) * (-(2 * (p : ℝ) * r))) t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul (-(2 * (p : ℝ) * r))).exp
    have hn := F.hasDerivAt_powSum ψ f p t
    change HasDerivAt N (-(2 * (p : ℝ)) * E t) t at hn
    have hh := he.mul hn
    change HasDerivAt (fun s ↦ Real.exp (-(2 * (p : ℝ) * r) * s) * N s)
      ((Real.exp (-(2 * (p : ℝ) * r) * t) * (-(2 * (p : ℝ) * r))) * N t +
        Real.exp (-(2 * (p : ℝ) * r) * t) * (-(2 * (p : ℝ)) * E t)) t at hh
    convert hh using 1; ring
  change AntitoneOn (fun t ↦ Real.exp (-(2 * (p : ℝ) * r) * t) * N t) (Set.Ici 0)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t _
    exact (hd t).continuousAt.continuousWithinAt
  · intro t _
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
      exact this.le
    rw [(hd t).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hform := F.form_twist_level hΛ (F.twist ψ f t)
      (fun i ↦ F.twist_nonneg ψ f hf ht0 i) p hp
    change -r * N t ≤ E t at hform
    have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hform)]

end
end LatticeProb.Davies.FiniteJumpForm
