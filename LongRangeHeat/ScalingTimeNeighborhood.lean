import LongRangeHeat.ScalingNonvanishing
import LongRangeHeat.FddStep
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A space-time lower bound for the heat derivative

For nonzero compactly supported smooth initial data, the continuum time derivative is bounded
away from zero on a neighborhood of a positive-time point.
-/

namespace LongRangeHeat

open LatticeProb.Heat LatticeProb.WhiteNoise
open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-- The time derivative is uniformly nonzero on a positive-time space-time neighborhood. -/
theorem exists_continuumHeat_deriv_space_time_lower_bound (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T, ∃ y, ∃ c > 0, ∃ r > 0, ∃ δ > 0,
      ∀ s ∈ Set.Ioo (t - δ) (t + δ), ∀ z ∈ Metric.ball y r,
        c ≤ |contOp d (continuumHeat f s) z| := by
  obtain ⟨t, ht, y, c, hc, r, hr, hb⟩ :=
    exists_continuumHeat_deriv_abs_lower_bound_of_ne_zero hd hf hfc hx hT
  let g := contOp d f
  have hg : ContDiff ℝ ∞ g := contDiff_contOp hf
  have hgc : HasCompactSupport g := hasCompactSupport_contOp hf hfc
  obtain ⟨M, hM⟩ := (hasCompactSupport_contOp hg hgc).exists_bound_of_continuous
    (contDiff_contOp hg).continuous
  have hMb : ∀ z, |contOp d g z| ≤ M := fun z => by simpa only [Real.norm_eq_abs] using hM z
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMb 0)
  let δ := min (t / 2) (c / (2 * (M + 1)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos ht.1) (div_pos hc (by positivity))
  refine ⟨t, ht, y, c / 2, by positivity, r, hr, δ, hδ, ?_⟩
  intro s hs z hz
  have hspos : 0 < s := by
    have hδt : δ ≤ t / 2 := min_le_left _ _
    linarith [hs.1]
  have hclose : |s - t| < δ := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hdiff : |continuumHeat g s z - continuumHeat g t z| ≤ M * |s - t| := by
    by_cases hst : t ≤ s
    · have h := abs_continuumHeat_add_sub_le hd hg hgc hMb ht.1 (sub_nonneg.mpr hst) z
      simpa only [add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr hst)] using h
    · have hst' : s ≤ t := le_of_not_ge hst
      have h := abs_continuumHeat_add_sub_le hd hg hgc hMb hspos (sub_nonneg.mpr hst') z
      rw [show s + (t - s) = t by ring, abs_sub_comm] at h
      simpa only [abs_of_nonpos (sub_nonpos.mpr hst'), neg_sub] using h
  have hdiff' : |contOp d (continuumHeat f s) z - contOp d (continuumHeat f t) z| ≤
      M * |s - t| := by
    simpa only [contOp_continuumHeat hd hf hfc hspos.le,
      contOp_continuumHeat hd hf hfc ht.1.le] using hdiff
  have hδc : δ ≤ c / (2 * (M + 1)) := min_le_right _ _
  have hsmall : M * |s - t| ≤ c / 2 := by
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hclose) hM0
    have hdiv := mul_le_mul_of_nonneg_right hδc (show 0 ≤ M + 1 by linarith)
    have hden : 0 < M + 1 := by linarith
    have heq : c / (2 * (M + 1)) * (M + 1) = c / 2 := by field_simp
    rw [heq] at hdiv
    nlinarith [mul_nonneg (show 0 ≤ δ by linarith) (show 0 ≤ (1 : ℝ) by norm_num)]
  have htri : |contOp d (continuumHeat f t) z| ≤
      |contOp d (continuumHeat f s) z| +
        |contOp d (continuumHeat f s) z - contOp d (continuumHeat f t) z| := by
    simpa only [sub_sub_cancel] using
      abs_sub (contOp d (continuumHeat f s) z)
        (contOp d (continuumHeat f s) z - contOp d (continuumHeat f t) z)
  linarith [hb z hz]


/-- A continuum time increment has a uniform lower bound on a spatial ball. -/
theorem exists_continuumHeat_time_increment_lower_bound (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T, ∃ y, ∃ c > 0, ∃ r > 0, ∃ δ > 0,
      ∀ s ∈ Set.Ioo (max 0 (t - δ)) t, ∀ z ∈ Metric.ball y r,
        c * (t - s) ≤ |continuumHeat f t z - continuumHeat f s z| := by
  obtain ⟨t, ht, y, c, hc, r, hr, δ, hδ, hb⟩ :=
    exists_continuumHeat_deriv_space_time_lower_bound hd hf hfc hx hT
  refine ⟨t, ht, y, c, hc, r, hr, δ, hδ, ?_⟩
  intro s hs z hz
  have hs0 : 0 < s := (le_max_left 0 (t - δ)).trans_lt hs.1
  have hcont : ContinuousOn (fun u => continuumHeat f u z) (Set.Icc s t) :=
    (continuousOn_continuumHeat_time hd hf hfc z).mono (fun u hu => hs0.le.trans hu.1)
  obtain ⟨u, hu, he⟩ := exists_hasDerivAt_eq_slope
    (fun u => continuumHeat f u z) (fun u => contOp d (continuumHeat f u) z)
    hs.2 hcont (fun u hu => hasDerivAt_continuumHeat hd hf hfc (hs0.trans hu.1) z)
  have hu' : u ∈ Set.Ioo (t - δ) (t + δ) := by
    constructor
    · exact ((le_max_right 0 (t - δ)).trans_lt hs.1).trans hu.1
    · linarith [hu.2]
  have h := hb u hu' z hz
  rw [he, abs_div, abs_of_pos (sub_pos.mpr hs.2)] at h
  exact (le_div_iff₀ (sub_pos.mpr hs.2)).mp h

end
end LongRangeHeat
