import LongRangeHeat.MainTheorem
import LongRangeHeat.ScalingGaussian

/-!
# Nonvanishing of the heat-flow derivative

A nonzero value of the generator of the initial datum persists for a short positive time.
-/

namespace LongRangeHeat

open Filter LatticeProb.Heat LatticeProb.WhiteNoise
open scoped Topology ContDiff

noncomputable section

variable {d : ℕ}

/-- A nonzero initial generator gives a nonzero time derivative before any positive time. -/
theorem exists_continuumHeat_deriv_ne_zero (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : contOp d f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => continuumHeat f s x) (contOp d (continuumHeat f t) x) t ∧
        contOp d (continuumHeat f t) x ≠ 0 := by
  have hn := (tendsto_continuumHeat hd (contDiff_contOp hf).continuous
    (hasCompactSupport_contOp hf hfc) x).eventually (eventually_ne_nhds hx)
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioo (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
    exact ⟨ht, htT⟩
  obtain ⟨t, ht, hn⟩ := (ht.and hn).exists
  exact ⟨t, ht, hasDerivAt_continuumHeat hd hf hfc ht.1 x, by
    rwa [contOp_continuumHeat hd hf hfc ht.1.le]⟩


/-- A nonzero initial generator gives a spatial neighborhood where the time derivative is
bounded away from zero at a positive time. -/
theorem exists_continuumHeat_deriv_abs_lower_bound (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : contOp d f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T, ∃ c > 0, ∃ r > 0,
      ∀ y ∈ Metric.ball x r, c ≤ |contOp d (continuumHeat f t) y| := by
  obtain ⟨t, ht, _, hn⟩ := exists_continuumHeat_deriv_ne_zero hd hf hfc hx hT
  let g := contOp d (continuumHeat f t)
  have hg : Continuous g := (contDiff_contOp (contDiff_continuumHeat hd hf hfc ht.1.le)).continuous
  have hp : 0 < |g x| := abs_pos.mpr hn
  have he : ∀ᶠ y in 𝓝 x, |g x| / 2 < |g y| :=
    (hg.abs.continuousAt).eventually (eventually_gt_nhds (half_lt_self hp))
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨t, ht, |g x| / 2, by positivity, r, hr, fun y hy => (hrball hy).le⟩


/-- If the initial generator vanishes, the continuum heat flow is stationary. -/
theorem continuumHeat_eq_of_contOp_eq_zero (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hzero : contOp d f = 0) {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    continuumHeat f t x = f x := by
  have hcont : ContinuousOn (fun s => continuumHeat f s x) (Set.Icc 0 t) :=
    (continuousOn_continuumHeat_time hd hf hfc x).mono (fun _ hs => hs.1)
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun r => continuumHeat f r x) 0 (Set.Ici s) s := by
    intro s hs
    have h := hasDerivWithinAt_continuumHeat hd hf hfc hs.1 x
    rw [contOp_continuumHeat hd hf hfc hs.1, hzero] at h
    simpa [continuumHeat] using h
  simpa only [continuumHeat_zero, Pi.zero_apply] using
    constant_of_has_deriv_right_zero hcont hderiv t ⟨ht, le_rfl⟩


/-- A nonzero compactly supported smooth function has a nonzero generator somewhere. -/
theorem exists_contOp_ne_zero (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) : ∃ y, contOp d f y ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : contOp d f = 0 := funext h
  have he : (fun t : ℝ => continuumHeat f t x) =ᶠ[atTop] fun _ => f x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact continuumHeat_eq_of_contOp_eq_zero hd hf hfc hzero ht x
  have hlim : Tendsto (fun t : ℝ => continuumHeat f t x) atTop (𝓝 (f x)) :=
    tendsto_const_nhds.congr' he.symm
  exact hx (tendsto_nhds_unique hlim (tendsto_continuumHeat_atTop hd hf.continuous hfc x))

/-- Before any positive time, the time derivative is bounded away from zero on a spatial ball. -/
theorem exists_continuumHeat_deriv_abs_lower_bound_of_ne_zero (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T, ∃ y, ∃ c > 0, ∃ r > 0,
      ∀ z ∈ Metric.ball y r, c ≤ |contOp d (continuumHeat f t) z| := by
  obtain ⟨y, hy⟩ := exists_contOp_ne_zero hd hf hfc hx
  obtain ⟨t, ht, c, hc, r, hr, hbound⟩ :=
    exists_continuumHeat_deriv_abs_lower_bound hd hf hfc hy hT
  exact ⟨t, ht, y, c, hc, r, hr, hbound⟩

end
end LongRangeHeat
