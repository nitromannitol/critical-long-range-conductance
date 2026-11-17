import LongRangeHeat.Scaling

/-!
# Normalization for the unscaled invariance principle

The logarithmic asymptotic of the normalization has the sphere-area coefficient.
-/

namespace LongRangeHeat

open Filter Topology LongRange

/-- The normalization divided by the logarithm converges to the sphere-area coefficient. -/
theorem tendsto_kappa_div_abs_log {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun ε : ℝ => kappa d ε / |Real.log ε|) (𝓝[>] 0)
      (𝓝 ((d : ℝ) * (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)))) := by
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  have hL : Tendsto (fun ε : ℝ => |Real.log ε|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  obtain ⟨K, _, hK⟩ := kappa_asymptotic hd
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with ε hε hε'
    exact ⟨hε, hε'.le⟩
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      -K ≤ kappa d ε - A * |Real.log ε| ∧ kappa d ε - A * |Real.log ε| ≤ K := by
    filter_upwards [hsmall] with ε hε
    exact abs_le.mp (hK ε hε)
  have hz : Tendsto (fun ε : ℝ => (kappa d ε - A * |Real.log ε|) / |Real.log ε|)
      (𝓝[>] 0) (𝓝 0) := tendsto_bdd_div_atTop_nhds_zero (hb.mono fun _ h => h.1)
        (hb.mono fun _ h => h.2) hL
  have hLpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < |Real.log ε| := hL.eventually_gt_atTop 0
  have h := hz.add (tendsto_const_nhds (x := A))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hLpos] with ε hε
  field_simp
  ring

/-- The iterated logarithm is negligible relative to the logarithm. -/
theorem tendsto_log_log_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h.comp Real.tendsto_log_atTop

/-- The lattice spacing used to recover the unscaled walk. -/
noncomputable def unscaledSpacing (A x : ℝ) : ℝ :=
  (Real.sqrt (A / 2 * x * Real.log x))⁻¹

/-- The spacing tends to zero from above. -/
theorem tendsto_unscaledSpacing {A : ℝ} (hA : 0 < A) :
    Tendsto (unscaledSpacing A) atTop (𝓝[>] 0) := by
  have hR : Tendsto (fun x : ℝ => A / 2 * x * Real.log x) atTop atTop :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < A / 2)).atTop_mul_atTop₀
      Real.tendsto_log_atTop
  have hs := (Real.tendsto_sqrt_atTop.comp hR).inv_tendsto_atTop
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hs, ?_⟩
  filter_upwards [hR.eventually_gt_atTop 0] with x hx
  exact inv_pos.mpr (Real.sqrt_pos.mpr hx)

/-- The logarithm of the spacing is asymptotic to half the logarithm of time. -/
theorem tendsto_abs_log_unscaledSpacing_div_log {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => |Real.log (unscaledSpacing A x)| / Real.log x)
      atTop (𝓝 (1 / 2)) := by
  have hR : Tendsto (fun x : ℝ => A / 2 * x * Real.log x) atTop atTop :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < A / 2)).atTop_mul_atTop₀
      Real.tendsto_log_atTop
  have hc : Tendsto (fun x : ℝ => Real.log (A / 2) / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := ((hc.add (tendsto_const_nhds (x := (1 : ℝ)))).add
    tendsto_log_log_div_log).div_const 2
  have h' : Tendsto (fun x : ℝ =>
      (Real.log (A / 2) / Real.log x + 1 + Real.log (Real.log x) / Real.log x) / 2)
      atTop (𝓝 (1 / 2)) := by
    simpa only [zero_add, add_zero] using h
  apply h'.congr'
  filter_upwards [hR.eventually_gt_atTop 1, eventually_gt_atTop (1 : ℝ)] with x hx hx'
  have hlog : 0 < Real.log x := Real.log_pos hx'
  have hnonneg : 0 ≤ Real.log (Real.sqrt (A / 2 * x * Real.log x)) :=
    Real.log_nonneg (Real.one_le_sqrt.mpr hx.le)
  rw [unscaledSpacing, Real.log_inv, abs_neg, abs_of_nonneg hnonneg,
    Real.log_sqrt (le_of_lt (zero_lt_one.trans hx)),
    Real.log_mul (mul_ne_zero (div_ne_zero hA.ne' (by norm_num)) (ne_of_gt (zero_lt_one.trans hx')))
      hlog.ne', Real.log_mul (div_ne_zero hA.ne' (by norm_num))
      (ne_of_gt (zero_lt_one.trans hx'))]
  field_simp

/-- The time factor for the unscaled walk tends to one. -/
theorem tendsto_kappa_unscaledSpacing {d : ℕ} (hd : 1 ≤ d) :
    let A : ℝ := (d : ℝ) *
      (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
    Tendsto (fun x : ℝ => kappa d (unscaledSpacing A x) * unscaledSpacing A x ^ 2 * x)
      atTop (𝓝 1) := by
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  change Tendsto (fun x : ℝ => kappa d (unscaledSpacing A x) *
    unscaledSpacing A x ^ 2 * x) atTop (𝓝 1)
  have hA : 0 < A := by
    dsimp [A]
    rw [← LatticeProb.Euclidean.Shell.unitBallVolume_eq_pi_div_gamma]
    exact mul_pos (Nat.cast_pos.mpr (by omega))
      (LatticeProb.Euclidean.Shell.unitBallVolume_pos d)
  have hk : Tendsto (fun x : ℝ => kappa d (unscaledSpacing A x) /
      |Real.log (unscaledSpacing A x)|) atTop (𝓝 A) :=
    (tendsto_kappa_div_abs_log hd).comp (tendsto_unscaledSpacing hA)
  have hl := tendsto_abs_log_unscaledSpacing_div_log hA
  have h := (hk.mul hl).mul_const (2 / A)
  have hlim : A * (1 / 2) * (2 / A) = 1 := by field_simp
  rw [hlim] at h
  apply h.congr'
  have hR : Tendsto (fun x : ℝ => A / 2 * x * Real.log x) atTop atTop :=
    (tendsto_id.const_mul_atTop (by positivity : 0 < A / 2)).atTop_mul_atTop₀
      Real.tendsto_log_atTop
  filter_upwards [hR.eventually_gt_atTop 1, eventually_gt_atTop (1 : ℝ)] with x hx hx'
  have hlog : 0 < Real.log x := Real.log_pos hx'
  have heps : 0 < unscaledSpacing A x :=
    inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hx))
  have hsqrt : Real.sqrt (A / 2 * x * Real.log x) ^ 2 = A / 2 * x * Real.log x :=
    Real.sq_sqrt (le_of_lt (zero_lt_one.trans hx))
  have hlogeps : |Real.log (unscaledSpacing A x)| ≠ 0 := by
    have : unscaledSpacing A x < 1 := by
      dsimp [unscaledSpacing]
      apply inv_lt_one_of_one_lt₀
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hx
    exact ne_of_gt (abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one heps (ne_of_lt this)))
  have heqsq : unscaledSpacing A x ^ 2 = (A / 2 * x * Real.log x)⁻¹ := by
    rw [unscaledSpacing, inv_pow, hsqrt]
  rw [heqsq]
  field_simp [hlogeps, hlog.ne', hA.ne', ne_of_gt (zero_lt_one.trans hx')]

end LongRangeHeat
