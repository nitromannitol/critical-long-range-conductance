import LongRange.Support.External.ChenKimKumagaiWang

/-!
# Comparison profiles for the Davies bound

Elementary properties of the monotone lower profile and its inverse tail.
-/

namespace LatticeProb.Davies

open MeasureTheory Set
open scoped ENNReal
open LatticeProb.External

noncomputable section

/-- The monotone profile lying below the Nash profile. -/
def thetaLow (c₁ c₂ : ℝ) (θstar : ℝ → ℝ) (r : ℝ) : ℝ :=
  c₁⁻¹ * θstar (c₂⁻¹ * r)

theorem thetaLow_pos {c₁ c₂ : ℝ} {θstar : ℝ → ℝ} (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hpos : ∀ r > 0, 0 < θstar r) {r : ℝ} (hr : 0 < r) :
    0 < thetaLow c₁ c₂ θstar r := by
  exact mul_pos (inv_pos.mpr (by linarith)) (hpos _ (mul_pos (inv_pos.mpr (by linarith)) hr))

theorem thetaLow_mono {c₁ c₂ : ℝ} {θstar : ℝ → ℝ} (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hm : MonotoneOn θstar (Ioi 0)) : MonotoneOn (thetaLow c₁ c₂ θstar) (Ioi 0) := by
  intro x hx y hy hxy
  have hc₂pos : 0 < c₂ := by linarith
  have hc₁nonneg : 0 ≤ c₁⁻¹ := inv_nonneg.mpr (by linarith)
  exact mul_le_mul_of_nonneg_left
    (hm (mul_pos (inv_pos.mpr hc₂pos) hx)
      (mul_pos (inv_pos.mpr hc₂pos) hy)
      (mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hc₂pos.le))) hc₁nonneg

theorem thetaLow_ratio_mono {c₁ c₂ : ℝ} {θstar : ℝ → ℝ} (hc₁ : 1 ≤ c₁)
    (hc₂ : 1 ≤ c₂) (hm : MonotoneOn (fun r ↦ θstar r / r) (Ioi 0)) :
    MonotoneOn (fun r ↦ thetaLow c₁ c₂ θstar r / r) (Ioi 0) := by
  intro x hx y hy hxy
  have hc₂0 : 0 < c₂ := by linarith
  have h := hm (mul_pos (inv_pos.mpr hc₂0) hx) (mul_pos (inv_pos.mpr hc₂0) hy)
    (mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hc₂0.le))
  have hc₁0 : 0 ≤ c₁⁻¹ * c₂⁻¹ := mul_nonneg (inv_nonneg.mpr (by linarith))
    (inv_nonneg.mpr hc₂0.le)
  have h' := mul_le_mul_of_nonneg_left h hc₁0
  dsimp [thetaLow]
  field_simp at h' ⊢
  nlinarith

theorem thetaLow_le {c₁ c₂ : ℝ} {θ θstar : ℝ → ℝ}
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) {r : ℝ} (hr : 0 < r) :
    thetaLow c₁ c₂ θstar r ≤ θ r := (hcompare r hr).1

theorem le_thetaLow_scaled {c₁ c₂ : ℝ} {θ θstar : ℝ → ℝ}
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) {r : ℝ} (hr : 0 < r) :
    θ r ≤ c₁ ^ 2 * thetaLow c₁ c₂ θstar (c₂ ^ 2 * r) := by
  have hc₁0 : c₁ ≠ 0 := by linarith
  have hc₂0 : c₂ ≠ 0 := by linarith
  calc
    θ r ≤ c₁ * θstar (c₂ * r) := (hcompare r hr).2
    _ = c₁ ^ 2 * thetaLow c₁ c₂ θstar (c₂ ^ 2 * r) := by
      have harg : c₂⁻¹ * (c₂ ^ 2 * r) = c₂ * r := by
        field_simp
        <;> ring
      rw [thetaLow, harg]
      field_simp
      <;> ring

theorem le_of_le_ckkwTail {θ φ : ℝ → ℝ} (h : ckkwInverseProfile θ φ)
    {s y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hle : s ≤ (ckkwTail θ y).toReal) : y ≤ φ s := by
  by_contra hn
  have hlt : φ s < y := lt_of_not_ge hn
  have hφ : 0 < φ s := (h.2.1 s hs).1
  have htail : ckkwTail θ y ≤ ckkwTail θ (φ s) :=
    lintegral_mono_set (Ioi_subset_Ioi hlt.le)
  have hreal := ENNReal.toReal_mono (h.1 (φ s) hφ).2 htail
  rw [(h.2.1 s hs).2] at hreal
  have heq : (ckkwTail θ y).toReal = s := le_antisymm hreal hle
  have := h.2.2 y hy
  rw [heq] at this
  linarith

end
end LatticeProb.Davies
