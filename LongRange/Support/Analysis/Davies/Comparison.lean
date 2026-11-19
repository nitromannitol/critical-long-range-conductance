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
open scoped Topology ENNReal
open LatticeProb.External

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

/-- The inverse tail bounds a positive function satisfying the Nash differential inequality. -/
theorem le_phi_of_deriv_le {c₁ c₂ : ℝ} {θ θstar φ β β' : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hinv : ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (ht : t₀ < t₁)
    (hβ : ∀ u ∈ Icc t₀ t₁, 0 < β u)
    (hd : ∀ u ∈ Icc t₀ t₁, HasDerivAt β (β' u) u)
    (hle : ∀ u ∈ Icc t₀ t₁, β' u ≤ -thetaLow c₁ c₂ θstar (β u)) :
    β t₁ ≤ c₂ ^ 2 * φ ((t₁ - t₀) / (c₁ * c₂) ^ 2) := by
  let low := thetaLow c₁ c₂ θstar
  have hlowpos : ∀ r > 0, 0 < low r := fun _ hr ↦ thetaLow_pos hc₁ hc₂ hpos hr
  have hlowmono : MonotoneOn low (Ioi 0) := thetaLow_mono hc₁ hc₂ hm
  have hcont : ContinuousOn β (Icc t₀ t₁) := fun u hu ↦ (hd u hu).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn β (Icc t₀ t₁) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
    intro u hu
    have hu' : u ∈ Icc t₀ t₁ := interior_subset hu
    rw [(hd u hu').deriv]
    have := hle u hu'
    have := hlowpos _ (hβ u hu')
    linarith
  have hord : β t₁ ≤ β t₀ := hanti.antitoneOn ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
  have hlo : 0 < β t₁ := hβ t₁ ⟨ht.le, le_rfl⟩
  have hθanti : AntitoneOn (fun s ↦ (low s)⁻¹) (Icc (β t₁) (β t₀)) := by
    intro x hx y hy hxy
    have hxpos := lt_of_lt_of_le hlo hx.1
    have hypos := lt_of_lt_of_le hlo hy.1
    exact (inv_le_inv₀ (hlowpos _ hypos) (hlowpos _ hxpos)).2
      (hlowmono hxpos hypos hxy)
  have hint : IntervalIntegrable (fun s ↦ (low s)⁻¹) volume (β t₁) (β t₀) := by
    apply AntitoneOn.intervalIntegrable
    simpa only [uIcc_of_le hord] using hθanti
  have hae : 0 ≤ᵐ[volume.restrict (Ioc (β t₁) (β t₀))] fun s ↦ (low s)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact inv_nonneg.mpr (hlowpos _ (lt_trans hlo hs.1)).le
  have hreal : t₁ - t₀ ≤ ∫ s in β t₁..β t₀, (low s)⁻¹ :=
    sub_le_integral_inv hlowpos hlowmono ht.le hβ hd hle
  have hen : ENNReal.ofReal (t₁ - t₀) ≤
      ENNReal.ofReal ((c₁ * c₂) ^ 2) * ckkwTail θ (β t₁ / c₂ ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (∫ s in β t₁..β t₀, (low s)⁻¹) := ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ s in Ioc (β t₁) (β t₀), ENNReal.ofReal ((low s)⁻¹) := by
        rw [intervalIntegral.integral_of_le hord]
        exact ofReal_integral_eq_lintegral_ofReal hint.1 hae
      _ ≤ ∫⁻ s in Ioi (β t₁), ENNReal.ofReal ((low s)⁻¹) :=
        lintegral_mono_set Ioc_subset_Ioi_self
      _ ≤ _ := lintegral_inv_thetaLow_le hc₁ hc₂ hinv hpos hcompare hlo
  have hc₁pos : 0 < c₁ := by linarith
  have hc₂pos : 0 < c₂ := by linarith
  have hden : 0 < (c₁ * c₂) ^ 2 := sq_pos_of_pos (mul_pos hc₁pos hc₂pos)
  have hc₂sq : 0 < c₂ ^ 2 := sq_pos_of_pos hc₂pos
  have hy : 0 < β t₁ / c₂ ^ 2 := div_pos hlo hc₂sq
  have hfinite : ENNReal.ofReal ((c₁ * c₂) ^ 2) * ckkwTail θ (β t₁ / c₂ ^ 2) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hinv.1 _ hy).2
  have htoreal := ENNReal.toReal_mono hfinite hen
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr ht.le), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hden.le] at htoreal
  have htail : (t₁ - t₀) / (c₁ * c₂) ^ 2 ≤ (ckkwTail θ (β t₁ / c₂ ^ 2)).toReal := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hphi := le_of_le_ckkwTail hinv (div_pos (sub_pos.mpr ht) hden) hy htail
  have hres := (div_le_iff₀ hc₂sq).1 hphi
  nlinarith

/-- Comparison with a fixed normalizing mass for a Nash differential inequality. -/
theorem le_phi_of_nash_deriv {c₁ c₂ : ℝ} {θ θstar φ a b b' : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hinv : ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (ht : t₀ < t₁)
    (ha : ∀ u ∈ Icc t₀ t₁, 0 < a u ∧ a u ≤ a t₀)
    (hb : ∀ u ∈ Icc t₀ t₁, 0 < b u)
    (hd : ∀ u ∈ Icc t₀ t₁, HasDerivAt b (b' u) u)
    (hle : ∀ u ∈ Icc t₀ t₁, b' u ≤ -a u * thetaLow c₁ c₂ θstar (b u / a u)) :
    b t₁ ≤ c₂ ^ 2 * φ ((t₁ - t₀) / (c₁ * c₂) ^ 2) * a t₀ := by
  have ha0 : 0 < a t₀ := (ha t₀ ⟨le_rfl, ht.le⟩).1
  have hratio' := thetaLow_ratio_mono hc₁ hc₂ hratio
  have hder : ∀ u ∈ Icc t₀ t₁,
      b' u / a t₀ ≤ -thetaLow c₁ c₂ θstar (b u / a t₀) := by
    intro u hu
    have hau := (ha u hu).1
    have hble := (ha u hu).2
    have hbpos := hb u hu
    have hxpos : 0 < b u / a t₀ := div_pos hbpos ha0
    have hypos : 0 < b u / a u := div_pos hbpos hau
    have hxy : b u / a t₀ ≤ b u / a u :=
      div_le_div_of_nonneg_left hbpos.le hau hble
    have hrat := hratio' hxpos hypos hxy
    have hfactor : a t₀ * thetaLow c₁ c₂ θstar (b u / a t₀) ≤
        a u * thetaLow c₁ c₂ θstar (b u / a u) := by
      have hrat' := mul_le_mul_of_nonneg_left hrat hbpos.le
      field_simp at hrat'
      nlinarith
    apply (div_le_iff₀ ha0).2
    nlinarith [hle u hu]
  have hcomp := le_phi_of_deriv_le hc₁ hc₂ hinv hpos hm hcompare ht
    (β := fun u ↦ b u / a t₀) (β' := fun u ↦ b' u / a t₀)
    (fun u hu ↦ div_pos (hb u hu) ha0)
    (fun u hu ↦ (hd u hu).div_const (a t₀)) hder
  exact (div_le_iff₀ ha0).1 hcomp

end
end LatticeProb.Davies
