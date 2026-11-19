import LongRange.Support.Analysis.Davies.GridExponent

/-!
# Product iteration on a finite semigroup

The finite power estimates and the source product profile yield a pointwise bound.
-/

namespace LatticeProb.Davies.FiniteJumpForm

open Filter Finset Matrix
open scoped Matrix.Norms.Operator
open scoped Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The product iteration bounds a terminal coordinate by the first grid level. -/
theorem twist_le_gridProduct {ψ : ι → ℝ} {Λsq δ c₁ c₂ l t c C : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (hN : F.Nash θ δ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (hl : 2 < l) (ht : 0 < t)
    (hprofile : External.ckkwProductBound φ l c C) (i : ι) :
    F.twist ψ f t i ≤ c₂ * (C * φ (c * (t / (c₁ * c₂) ^ 2))) ^ (1 / 2 : ℝ) *
      Real.exp (((l - 1) / l) * t * Λsq * (6 / (l - 2)) + δ * t) *
      F.gridPower ψ f l t 0 := by
  have hc₂pos : 0 < c₂ := by linarith
  have ht' : 0 < t / (c₁ * c₂) ^ 2 := by positivity
  let A : ℕ → ℝ := fun n ↦
    (c₂ ^ 2 * φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * (t / (c₁ * c₂) ^ 2))) ^
      ((1 / 2 : ℝ) / 2 / 2 ^ n)
  let D : ℕ → ℝ := fun n ↦ Real.exp
    (levelRate Λsq (2 ^ n) * (t - timeGrid l t (n + 1)))
  let B : ℝ := ((l - 1) / l) * t * Λsq * (6 / (l - 2)) + δ * t
  obtain ⟨Q, hQ, hQle⟩ := ckkw_product_limit_le hl hc₂pos ht'
    (fun s hs ↦ (hinv.2.1 s hs).1) hprofile
  have hA (n : ℕ) : 0 ≤ A n := by
    apply Real.rpow_nonneg
    apply mul_nonneg (sq_nonneg c₂)
    apply (hinv.2.1 _ ?_).1.le
    have hlpos : 0 < l := by linarith
    exact mul_pos (mul_pos (by linarith) (zpow_pos hlpos _)) ht'
  have hD (n : ℕ) : 0 ≤ D n := (Real.exp_pos _).le
  have hM0 : 0 ≤ F.gridPower ψ f l t 0 := Real.rpow_nonneg
    (sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf
      (timeGrid_nonneg hl ht.le 1) i) _) _
  have hstep (n : ℕ) : F.gridPower ψ f l t (n + 1) ≤
      A n * Real.exp (gridExponent l t Λsq δ n) * F.gridPower ψ f l t n := by
    exact F.gridPower_step hΛ hδ f hf hf0 hN hc₁ hc₂ hinv hpos hm hratio hcompare hl ht n
  have hcoord (n : ℕ) : F.twist ψ f t i ≤ D n * F.gridPower ψ f l t n :=
    F.coordinate_le_gridPower hΛ f hf hl ht n i
  have hlim : Tendsto D atTop (𝓝 1) := tendsto_exp_levelRate_remaining hΛ.1 hl ht.le
  have hbound := le_of_product_iteration hA hD hM0 hstep hcoord
    (fun n ↦ sum_gridExponent_le hl ht hΛ.1 hδ n) hQ hlim
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hQle (Real.exp_pos B).le) hM0)

/-- The conjugated semigroup is the identity at time zero. -/
theorem twist_zero (ψ f : ι → ℝ) (i : ι) : F.twist ψ f 0 i = f i := by
  simp only [twist, semigroup, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec,
    ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- The first grid power is controlled by the initial two-power norm. -/
theorem gridPower_zero_le {ψ : ι → ℝ} {Λsq l t : ℝ}
    (hΛ : F.LambdaBound ψ Λsq) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hl : 2 < l) (ht : 0 < t) :
    F.gridPower ψ f l t 0 ≤ Real.exp (Λsq * timeGrid l t 1) *
      (∑ i, f i ^ 2) ^ (1 / 2 : ℝ) := by
  have h := F.twist_powSum_root_le hΛ f hf 1 (by norm_num)
    (show (0 : ℝ) ≤ 0 by rfl) (timeGrid_nonneg hl ht.le 1)
  simpa only [gridPower, Nat.zero_add, pow_one, Nat.reduceMul, Nat.cast_one,
    mul_one, pow_zero, div_one, one_div, sub_zero, levelRate, ↓reduceIte, F.twist_zero] using h

end
end LatticeProb.Davies.FiniteJumpForm
