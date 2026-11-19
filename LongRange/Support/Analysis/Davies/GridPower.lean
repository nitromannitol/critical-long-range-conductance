import LongRange.Support.Analysis.Davies.PowerRoots

/-!
# Power levels on the Davies time grid

The finite Nash step specialized to successive powers of two on a geometric grid.
-/

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The root of the power sum at a grid time. -/
def gridPower (ψ f : ι → ℝ) (l t : ℝ) (n : ℕ) : ℝ :=
  (∑ i, (F.twist ψ f (timeGrid l t (n + 1)) i) ^ (2 ^ (n + 1))) ^
    ((1 / 2 : ℝ) / 2 ^ n)

/-- Each successive power is controlled by the preceding power on the time grid. -/
theorem gridPower_step {ψ : ι → ℝ} {Λsq δ c₁ c₂ l t : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (hN : F.Nash θ δ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (hl : 2 < l) (ht : 0 < t) (n : ℕ) :
    F.gridPower ψ f l t (n + 1) ≤
      (c₂ ^ 2 * φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * (t / (c₁ * c₂) ^ 2))) ^
        ((1 / 2 : ℝ) / 2 / 2 ^ n) *
      Real.exp (((2 * (2 ^ (n + 1) : ℕ) + 1) * Λsq + δ / (2 ^ (n + 1) : ℕ)) *
        (timeGrid l t (n + 2) - timeGrid l t (n + 1))) * F.gridPower ψ f l t n := by
  have hq : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h := F.powSum_root_step hΛ hδ f hf hf0 (2 ^ n) hq hN hc₁ hc₂ hinv hpos hm
    hratio hcompare (timeGrid_nonneg hl ht.le (n + 1)) (timeGrid_lt_succ hl ht (n + 1))
  have hnat : 2 * (2 ^ n : ℕ) = 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hnat2 : 2 * (2 * (2 ^ n : ℕ)) = 2 ^ (n + 1 + 1) := by rw [hnat, pow_succ]; ring
  have hr (m : ℕ) : (2 * (2 : ℝ) ^ m)⁻¹ = (1 / 2 : ℝ) / 2 ^ m := by
    field_simp
  have hr1 : ((2 : ℝ) ^ (n + 1))⁻¹ = (1 / 2 : ℝ) / 2 ^ n := by
    rw [pow_succ]
    field_simp
  have hdelta : (timeGrid l t (n + 1 + 1) - timeGrid l t (n + 1)) /
      (c₁ * c₂) ^ 2 = (l - 1) * l ^ (-(n + 2 : ℤ)) * (t / (c₁ * c₂) ^ 2) := by
    rw [timeGrid_increment hl]
    have he : (n + 1 + 1 : ℤ) = n + 2 := by ring
    push_cast
    rw [he]
    ring
  dsimp only [gridPower]
  dsimp only at h
  rw [hnat2, hnat] at h
  push_cast at h
  rw [hr (n + 1), hr1, hdelta] at h
  have hrfinal : (1 / 2 : ℝ) / 2 ^ (n + 1) = (1 / 2 : ℝ) / 2 / 2 ^ n := by
    rw [pow_succ]
    field_simp
  rw [hrfinal] at h
  rw [hrfinal]
  simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_pow, Nat.cast_ofNat] using h

end
end LatticeProb.Davies.FiniteJumpForm
