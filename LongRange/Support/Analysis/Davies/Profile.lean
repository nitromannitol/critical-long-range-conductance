import LongRange.Support.External.ChenKimKumagaiWang
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

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
      rw [thetaLow, harg]
      field_simp

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

/-- Change variables in a nonnegative tail integral under positive dilation. -/
theorem lintegral_tail_div (f : ℝ → ℝ≥0∞) {a x : ℝ} (ha : 0 < a) :
    (∫⁻ s in Ioi x, f (s / a)) = ENNReal.ofReal a * ∫⁻ s in Ioi (x / a), f s := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero (ne_of_gt ha))).toMeasurableEquiv
  have hpre : (fun s : ℝ ↦ a⁻¹ * s) ⁻¹' Ioi (x / a) = Ioi x := by
    ext s
    simp only [mem_preimage, mem_Ioi, div_eq_mul_inv]
    simpa [div_eq_mul_inv, mul_comm] using (div_lt_div_iff_of_pos_right ha : x / a < s / a ↔ x < s)
  have hmap : Measure.map e (volume.restrict (Ioi x)) =
      ENNReal.ofReal a • volume.restrict (Ioi (x / a)) := by
    have hpre' : e ⁻¹' Ioi (x / a) = Ioi x := hpre
    rw [← hpre', ← Measure.restrict_map e.measurable measurableSet_Ioi]
    change (Measure.map (fun s : ℝ ↦ a⁻¹ * s) volume).restrict _ = _
    rw [Real.map_volume_mul_left (inv_ne_zero (ne_of_gt ha))]
    simp only [inv_inv, abs_of_pos ha, Measure.restrict_smul]
  calc
    _ = ∫⁻ s, f s ∂Measure.map e (volume.restrict (Ioi x)) := by
      rw [lintegral_map_equiv]
      change (∫⁻ s in Ioi x, f (s / a)) = ∫⁻ s in Ioi x, f (a⁻¹ * s)
      simp only [div_eq_mul_inv, mul_comm]
    _ = _ := by rw [hmap, lintegral_smul_measure]; rfl

theorem lintegral_inv_thetaLow_le {c₁ c₂ : ℝ} {θ θstar φ : ℝ → ℝ}
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r)
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) {x : ℝ} (hx : 0 < x) :
    (∫⁻ s in Ioi x, ENNReal.ofReal ((thetaLow c₁ c₂ θstar s)⁻¹)) ≤
      ENNReal.ofReal ((c₁ * c₂) ^ 2) * ckkwTail θ (x / c₂ ^ 2) := by
  have hc₁pos : 0 < c₁ := by linarith
  have hc₂pos : 0 < c₂ := by linarith
  have ha : 0 < c₂ ^ 2 := sq_pos_of_pos hc₂pos
  have hpoint : ∀ s ∈ Ioi x, (thetaLow c₁ c₂ θstar s)⁻¹ ≤
      c₁ ^ 2 * (θ (s / c₂ ^ 2))⁻¹ := by
    intro s hs
    have hspos : 0 < s := lt_trans hx hs
    have htpos : 0 < θ (s / c₂ ^ 2) := (hinv.1 _ (div_pos hspos ha)).1
    have hlpos := thetaLow_pos hc₁ hc₂ hpos hspos
    have hcomp := le_thetaLow_scaled hc₁ hc₂ hcompare (div_pos hspos ha)
    have harg : c₂ ^ 2 * (s / c₂ ^ 2) = s := mul_div_cancel₀ s (ne_of_gt ha)
    rw [harg] at hcomp
    have hi := (inv_le_inv₀ (mul_pos (sq_pos_of_pos hc₁pos) hlpos) htpos).2 hcomp
    rw [mul_inv_rev] at hi
    have hsq : c₁ ^ 2 * (c₁ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hc₁pos))
    have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg c₁)
    calc
      (thetaLow c₁ c₂ θstar s)⁻¹ = c₁ ^ 2 * ((thetaLow c₁ c₂ θstar s)⁻¹ * (c₁ ^ 2)⁻¹) := by
        rw [← mul_assoc, mul_comm (c₁ ^ 2) ((thetaLow c₁ c₂ θstar s)⁻¹), mul_assoc, hsq, mul_one]
      _ ≤ _ := hmul
  calc
    _ ≤ ∫⁻ s in Ioi x, ENNReal.ofReal (c₁ ^ 2) * ENNReal.ofReal ((θ (s / c₂ ^ 2))⁻¹) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [← ENNReal.ofReal_mul (sq_nonneg c₁)]
      exact ENNReal.ofReal_le_ofReal (hpoint s hs)
    _ = ENNReal.ofReal (c₁ ^ 2) * ∫⁻ s in Ioi x, ENNReal.ofReal ((θ (s / c₂ ^ 2))⁻¹) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (c₁ ^ 2) * (ENNReal.ofReal (c₂ ^ 2) * ckkwTail θ (x / c₂ ^ 2)) := by
      change ENNReal.ofReal (c₁ ^ 2) * (∫⁻ s in Ioi x, (fun u ↦ ENNReal.ofReal ((θ u)⁻¹)) (s / c₂ ^ 2)) = _
      congr 1
      exact lintegral_tail_div (fun u ↦ ENNReal.ofReal ((θ u)⁻¹)) (x := x) ha
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg c₁)]; congr 1; ring

theorem lintegral_inv_thetaLow_ne_top {c₁ c₂ : ℝ} {θ θstar φ : ℝ → ℝ}
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : ckkwInverseProfile θ φ) (hpos : ∀ r > 0, 0 < θstar r)
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) {x : ℝ} (hx : 0 < x) :
    (∫⁻ s in Ioi x, ENNReal.ofReal ((thetaLow c₁ c₂ θstar s)⁻¹)) ≠ ∞ := by
  have hx' : 0 < x / c₂ ^ 2 := div_pos hx (sq_pos_of_pos (by linarith))
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hinv.1 _ hx').2)
    (lintegral_inv_thetaLow_le hc₁ hc₂ hinv hpos hcompare hx)

end
end LatticeProb.Davies
