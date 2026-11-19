import LongRange.Support.Analysis.Davies.PowerBounds
import LongRange.Support.Analysis.Davies.Iteration

/-!
# Root bounds for Davies iteration

Root estimates for the finite power sums used on consecutive time intervals.
-/

namespace LatticeProb.Davies

noncomputable section

/-- Taking a nonnegative root of a product estimate separates its factors. -/
theorem rpow_le_of_le_exp_mul_sq {x y a b r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (h : x ≤ a * Real.exp b * y ^ 2) :
    x ^ r ≤ a ^ r * Real.exp (b * r) * y ^ (2 * r) := by
  calc
    x ^ r ≤ (a * Real.exp b * y ^ 2) ^ r := Real.rpow_le_rpow hx h hr
    _ = a ^ r * Real.exp (b * r) * y ^ (2 * r) := by
      rw [Real.mul_rpow (mul_nonneg ha (Real.exp_pos b).le) (sq_nonneg y),
        Real.mul_rpow ha (Real.exp_pos b).le, ← Real.exp_mul,
        Real.rpow_mul hy]
      rw [Real.rpow_two]

namespace FiniteJumpForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The Nash step in terms of roots of consecutive even power sums. -/
theorem powSum_root_step {ψ : ι → ℝ} {Λsq δ c₁ c₂ : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (q : ℕ) (hq : 1 ≤ q) (hN : F.Nash θ δ)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    let p : ℕ := 2 * q
    (∑ i, (F.twist ψ f t i) ^ (2 * p)) ^ ((2 * (p : ℝ))⁻¹) ≤
      (c₂ ^ 2 * φ ((t - s) / (c₁ * c₂) ^ 2)) ^ ((2 * (p : ℝ))⁻¹) *
      Real.exp (((2 * (p : ℝ) + 1) * Λsq + δ / (p : ℝ)) * (t - s)) *
      (∑ i, (F.twist ψ f s i) ^ p) ^ ((p : ℝ)⁻¹) := by
  let p : ℕ := 2 * q
  have hp : 0 < (p : ℝ) := by dsimp [p]; positivity
  have hx : 0 ≤ ∑ i, F.twist ψ f t i ^ (2 * p) :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf (le_trans hs hst.le) i) _
  have hy : 0 ≤ ∑ i, F.twist ψ f s i ^ p :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf hs i) _
  have harg : 0 < (t - s) / (c₁ * c₂) ^ 2 := by positivity
  have ha : 0 ≤ c₂ ^ 2 * φ ((t - s) / (c₁ * c₂) ^ 2) :=
    mul_nonneg (sq_nonneg _) (hinv.2.1 _ harg).1.le
  have hr : 0 ≤ (2 * (p : ℝ))⁻¹ := by positivity
  have h := F.powSum_step hΛ hδ f hf hf0 q hq hN hc₁ hc₂ hinv hpos hm hratio hcompare hs hst
  change (∑ i, F.twist ψ f t i ^ (2 * p)) ≤ _ at h
  have hh := rpow_le_of_le_exp_mul_sq hx hy ha hr h
  have h₁ : 2 * (2 * (p : ℝ))⁻¹ = (p : ℝ)⁻¹ := by field_simp
  have h₂ : ((2 * (p : ℝ) * ((2 * (p : ℝ) + 1) * Λsq) + 2 * δ) * (t - s)) *
      (2 * (p : ℝ))⁻¹ = (((2 * (p : ℝ) + 1) * Λsq + δ / (p : ℝ)) * (t - s)) := by
    field_simp
  rw [h₁, h₂] at hh
  exact hh

/-- The compensated growth estimate for roots of even power sums. -/
theorem twist_powSum_root_le {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℕ) (hp : 1 ≤ p)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∑ i, (F.twist ψ f t i) ^ (2 * p)) ^ ((2 * (p : ℝ))⁻¹) ≤
      Real.exp (levelRate Λsq p * (t - s)) *
        (∑ i, (F.twist ψ f s i) ^ (2 * p)) ^ ((2 * (p : ℝ))⁻¹) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hx : 0 ≤ ∑ i, F.twist ψ f t i ^ (2 * p) :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf (le_trans hs hst) i) _
  have hy : 0 ≤ ∑ i, F.twist ψ f s i ^ (2 * p) :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf hs i) _
  have hr : 0 ≤ (2 * (p : ℝ))⁻¹ := by positivity
  have h := Real.rpow_le_rpow hx (F.twist_powSum_le hΛ f hf p hp hs hst) hr
  rw [Real.mul_rpow (Real.exp_pos _).le hy, ← Real.exp_mul] at h
  have he : ((2 * (p : ℝ) * levelRate Λsq p) * (t - s)) *
      (2 * (p : ℝ))⁻¹ = levelRate Λsq p * (t - s) := by field_simp
  rw [he] at h
  exact h

end FiniteJumpForm
end
end LatticeProb.Davies
