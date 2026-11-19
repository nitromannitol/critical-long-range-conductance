import LongRange.Support.Analysis.Davies.GridIteration

/-!
# Finite twisted-semigroup bound

The product iteration gives a two-to-infinity estimate for finite jump forms.
-/

namespace LatticeProb.Davies.FiniteJumpForm

open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The two-to-infinity estimate for a nonzero initial function. -/
theorem twist_le_of_ne_zero {ψ : ι → ℝ} {Λsq δ c₁ c₂ l t c C ε : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (hN : F.Nash θ δ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (hl : 2 < l) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hchoice : 2 + 6 / ε ≤ l)
    (hprofile : External.ckkwProductBound φ l c C) (i : ι) :
    F.twist ψ f t i ≤ c₂ * (C * φ (c * (t / (c₁ * c₂) ^ 2))) ^ (1 / 2 : ℝ) *
      Real.exp (t * ((1 + ε) * Λsq + δ)) * (∑ i, f i ^ 2) ^ (1 / 2 : ℝ) := by
  let K : ℝ := c₂ * (C * φ (c * (t / (c₁ * c₂) ^ 2))) ^ (1 / 2 : ℝ)
  let B : ℝ := ((l - 1) / l) * t * Λsq * (6 / (l - 2)) + δ * t
  let N : ℝ := (∑ i, f i ^ 2) ^ (1 / 2 : ℝ)
  have ht' : 0 < c * (t / (c₁ * c₂) ^ 2) := by positivity
  have hK : 0 ≤ K := mul_nonneg (by linarith)
    (Real.rpow_nonneg (mul_nonneg hC.le (hinv.2.1 _ ht').1.le) _)
  have hN0 : 0 ≤ N := Real.rpow_nonneg (sum_nonneg fun i _ ↦ sq_nonneg (f i)) _
  have hgrid := F.twist_le_gridProduct hΛ hδ f hf hf0 hN hc₁ hc₂ hinv hpos hm hratio
    hcompare hl ht hprofile i
  have hinit := F.gridPower_zero_le hΛ f hf hl ht
  have ht₁ : timeGrid l t 1 = (l - 1) / l * t := by
    have hl0 : l ≠ 0 := by linarith
    dsimp [timeGrid]
    field_simp
  have hcoeff := davies_exponent_coefficient_le hε hl hchoice
  have hexp : B + Λsq * timeGrid l t 1 ≤ t * ((1 + ε) * Λsq + δ) := by
    rw [ht₁]
    have h := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hΛ.1) δ) ht.le
    dsimp [B]
    nlinarith
  calc
    F.twist ψ f t i ≤ K * Real.exp B * F.gridPower ψ f l t 0 := hgrid
    _ ≤ K * Real.exp B * (Real.exp (Λsq * timeGrid l t 1) * N) :=
      mul_le_mul_of_nonneg_left hinit (mul_nonneg hK (Real.exp_pos _).le)
    _ = K * (Real.exp B * Real.exp (Λsq * timeGrid l t 1)) * N := by ring
    _ = K * Real.exp (B + Λsq * timeGrid l t 1) * N :=
      congrArg (fun x : ℝ ↦ K * x * N) (Real.exp_add B _).symm
    _ ≤ K * Real.exp (t * ((1 + ε) * Λsq + δ)) * N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hK) hN0

/-- The two-to-infinity estimate for a finite twisted semigroup. -/
theorem twist_le {ψ : ι → ℝ} {Λsq δ c₁ c₂ l t c C ε : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hN : F.Nash θ δ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (hl : 2 < l) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hchoice : 2 + 6 / ε ≤ l)
    (hprofile : External.ckkwProductBound φ l c C) (i : ι) :
    F.twist ψ f t i ≤ c₂ * (C * φ (c * (t / (c₁ * c₂) ^ 2))) ^ (1 / 2 : ℝ) *
      Real.exp (t * ((1 + ε) * Λsq + δ)) * (∑ i, f i ^ 2) ^ (1 / 2 : ℝ) := by
  by_cases hf0 : f = 0
  · subst f
    simp [twist, Matrix.mulVec, dotProduct]
  · exact F.twist_le_of_ne_zero hΛ hδ f hf hf0 hN hc₁ hc₂ hinv hpos hm hratio
      hcompare hl ht hc hC hε hchoice hprofile i

end
end LatticeProb.Davies.FiniteJumpForm
