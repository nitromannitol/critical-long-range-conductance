import LongRange.Support.Analysis.Davies.Profile
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differential comparison for monotone profiles

A right-sided slope argument permits monotone profiles with discontinuities.
-/

namespace LatticeProb.Davies

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- A decreasing integrand dominates its right endpoint on a positive interval. -/
theorem mul_sub_le_integral_of_antitone {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : AntitoneOn g (Icc a b)) :
    (b - a) * g b ≤ ∫ s in a..b, g s := by
  have hi : IntervalIntegrable g volume a b := by
    apply AntitoneOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hg
  have h := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) hi
    (fun s hs ↦ hg hs ⟨hab, le_rfl⟩ hs.2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

/-- Differential comparison without continuity of the profile. -/
theorem sub_le_integral_inv {θ β β' : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hθ : ∀ r > 0, 0 < θ r) (hm : MonotoneOn θ (Ioi 0)) (ht : t₀ ≤ t₁)
    (hβ : ∀ u ∈ Icc t₀ t₁, 0 < β u)
    (hd : ∀ u ∈ Icc t₀ t₁, HasDerivAt β (β' u) u)
    (hle : ∀ u ∈ Icc t₀ t₁, β' u ≤ -θ (β u)) :
    t₁ - t₀ ≤ ∫ s in β t₁..β t₀, (θ s)⁻¹ := by
  let g : ℝ → ℝ := fun s ↦ (θ s)⁻¹
  have hg : AntitoneOn g (Ioi 0) := by
    intro x hx y hy hxy
    exact (inv_le_inv₀ (hθ _ hy) (hθ _ hx)).2 (hm hx hy hxy)
  have hcont : ContinuousOn β (Icc t₀ t₁) := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn β (Icc t₀ t₁) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
    intro u hu
    have hu' : u ∈ Icc t₀ t₁ := interior_subset hu
    rw [(hd u hu').deriv]
    have := hle u hu'
    have := hθ _ (hβ u hu')
    linarith
  have horder : β t₁ ≤ β t₀ := hanti.antitoneOn ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hrange : MapsTo β (Icc t₀ t₁) (Icc (β t₁) (β t₀)) := by
    intro u hu
    exact ⟨hanti.antitoneOn hu ⟨ht, le_rfl⟩ hu.2,
      hanti.antitoneOn ⟨le_rfl, ht⟩ hu hu.1⟩
  have hmono : AntitoneOn g (Icc (β t₁) (β t₀)) := hg.mono (by
    intro x hx
    exact lt_of_lt_of_le (hβ t₁ ⟨ht, le_rfl⟩) hx.1)
  have hint : IntervalIntegrable g volume (β t₁) (β t₀) := by
    apply AntitoneOn.intervalIntegrable
    simpa only [uIcc_of_le horder] using hmono
  let F : ℝ → ℝ := fun u ↦ (u - t₀) - ∫ s in β u..β t₀, g s
  have hFcont : ContinuousOn F (Icc t₀ t₁) := by
    have hintcc : IntegrableOn g (uIcc (β t₁) (β t₀)) volume :=
      (intervalIntegrable_iff').mp hint
    have hprim := intervalIntegral.continuousOn_primitive_interval_left hintcc
    have hcomp := hprim.comp hcont (by simpa only [uIcc_of_le horder] using hrange)
    exact (continuousOn_id.sub continuousOn_const).sub hcomp
  have hbound : ∀ u ∈ Ico t₀ t₁, ∀ r : ℝ, (0 : ℝ) < r →
      ∃ᶠ z in 𝓝[>] u, slope F u z < r := by
    intro u hu r hr
    have hucc : u ∈ Icc t₀ t₁ := ⟨hu.1, hu.2.le⟩
    have hder := (hd u hucc).tendsto_slope.mono_left (nhdsGT_le_nhdsNE u)
    have hlim : 1 + β' u * g (β u) ≤ 0 := by
      have hp := hθ _ (hβ u hucc)
      have hdiv : β' u / θ (β u) ≤ -1 := by
        apply (div_le_iff₀ hp).2
        linarith [hle u hucc]
      dsimp [g]
      rw [← div_eq_mul_inv]
      linarith
    have htend : Tendsto (fun z ↦ 1 + slope β u z * g (β u)) (𝓝[>] u)
        (𝓝 (1 + β' u * g (β u))) :=
      tendsto_const_nhds.add (hder.mul tendsto_const_nhds)
    have hev := htend.eventually_lt_const (lt_of_le_of_lt hlim hr)
    have hzu : ∀ᶠ z : ℝ in 𝓝[>] u, u < z := eventually_mem_nhdsWithin
    have hzt : ∀ᶠ z : ℝ in 𝓝[>] u, z < t₁ :=
      (eventually_lt_nhds hu.2).filter_mono nhdsWithin_le_nhds
    apply Filter.Eventually.frequently
    filter_upwards [hev, hzu, hzt] with z hz huz hzt
    have hzcc : z ∈ Icc t₀ t₁ := ⟨le_trans hu.1 huz.le, hzt.le⟩
    have hβzu : β z ≤ β u := hanti.antitoneOn hucc hzcc huz.le
    have hu_range := hrange hucc
    have hz_range := hrange hzcc
    have hinterval : Icc (β z) (β u) ⊆ Ioi (0 : ℝ) := by
      intro s hs
      exact lt_of_lt_of_le (hβ z hzcc) hs.1
    have hintegral := mul_sub_le_integral_of_antitone hβzu (hg.mono hinterval)
    have hu_int : IntervalIntegrable g volume (β t₀) (β u) := by
      apply hint.mono_set
      apply uIcc_subset_uIcc
      · simpa only [uIcc_of_le horder] using (show β t₀ ∈ Icc (β t₁) (β t₀) from ⟨horder, le_rfl⟩)
      · simpa only [uIcc_of_le horder] using hu_range
    have hz_int : IntervalIntegrable g volume (β t₀) (β z) := by
      apply hint.mono_set
      apply uIcc_subset_uIcc
      · simpa only [uIcc_of_le horder] using (show β t₀ ∈ Icc (β t₁) (β t₀) from ⟨horder, le_rfl⟩)
      · simpa only [uIcc_of_le horder] using hz_range
    have hintdiff := intervalIntegral.integral_interval_sub_left hu_int hz_int
    have hdiff : (∫ s in β z..β t₀, g s) - (∫ s in β u..β t₀, g s) =
        ∫ s in β z..β u, g s := by
      rw [intervalIntegral.integral_symm (β t₀) (β z),
        intervalIntegral.integral_symm (β t₀) (β u)]
      linarith
    have hslope : slope F u z ≤ 1 + slope β u z * g (β u) := by
      rw [slope_def_field, slope_def_field]
      dsimp only [F]
      have hden : 0 < z - u := sub_pos.mpr huz
      apply (div_le_iff₀ hden).2
      have hcancel : (β z - β u) / (z - u) * g (β u) * (z - u) =
          (β z - β u) * g (β u) := by
        field_simp
      rw [add_mul, one_mul, hcancel]
      linarith
    exact lt_of_le_of_lt hslope hz
  have hfinal := image_le_of_liminf_slope_right_le_deriv_boundary hFcont
    (B := fun _ ↦ 0) (B' := fun _ ↦ 0) (by simp [F]) continuousOn_const
    (by intro x hx; exact (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt) hbound
    (show t₁ ∈ Icc t₀ t₁ from ⟨ht, le_rfl⟩)
  simpa only [F, Pi.zero_apply] using sub_nonpos.mp hfinal

end
end LatticeProb.Davies
