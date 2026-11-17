import LongRangeHeat.ScalingLowerBound
import LongRangeHeat.ScalingSupremum

/-!
# The heat scaling obstruction

The logarithmic normalization creates a time shift whose size is asymptotically proportional to
`|log ε|⁻¹`.
-/

namespace LongRangeHeat

open Filter LatticeProb LatticeProb.Euclidean.Lattice LongRange
open scoped Topology ContDiff

noncomputable section

/-- The relative change in the normalization under halving tends to zero. -/
theorem kappa_half_defect_tendsto_zero {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun ε : ℝ => (kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2))
      (𝓝[>] 0) (𝓝 0) := by
  have hL : Tendsto (fun ε : ℝ => |Real.log ε|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := (kappa_half_ratio_tendsto hd).div_atTop hL
  apply h.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with ε hε
  field_simp


/-- At sufficiently small spacing the rescaled time lies just below the original time. -/
theorem eventually_kappa_scaled_time_mem {d : ℕ} (hd : 1 ≤ d)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (kappa d ε / kappa d (ε / 2)) * t ∈ Set.Ioo (max 0 (t - δ)) t := by
  have hL : Tendsto (fun ε : ℝ => |Real.log ε|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < (kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2) := by
    filter_upwards [hL.eventually_gt_atTop 0,
      (kappa_half_ratio_tendsto hd).eventually (eventually_gt_nhds hlog)] with ε hLε hε
    exact (mul_pos_iff_of_pos_right hLε).mp hε
  have hsmall := (kappa_half_defect_tendsto_zero hd).eventually
    (eventually_lt_nhds (div_pos hδ ht))
  have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε'
    exact ⟨hε, hε'⟩
  filter_upwards [hp, hsmall, hεsmall] with ε hpε hsmallε hε
  have hk : 0 < kappa d ε := LongRange.kappa_pos hd ⟨hε.1, by linarith [hε.2]⟩
  have hkh : 0 < kappa d (ε / 2) :=
    LongRange.kappa_pos hd ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hlt : (kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2) < 1 :=
    (div_lt_one hkh).2 (by linarith)
  have hrat : kappa d ε / kappa d (ε / 2) =
      1 - (kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2) := by
    field_simp
    ring
  rw [hrat]
  have hδt := (lt_div_iff₀ ht).mp hsmallε
  rw [Set.mem_Ioo, max_lt_iff]
  constructor
  · constructor <;> nlinarith
  · nlinarith


/-- The continuum mismatch at the scaled time has a positive inverse-logarithmic lower bound. -/
theorem eventually_scaled_heat_mismatch_lower_bound {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T, ∃ C > 0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      MemL2 (fun q => continuumHeat f t (physical ε q) -
        continuumHeat f ((kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) ∧
      C ≤ |Real.log ε| * latticeNorm ε (fun q => continuumHeat f t (physical ε q) -
        continuumHeat f ((kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) := by
  obtain ⟨t, ht, C, hC, δ, hδ, hN⟩ :=
    eventually_latticeNorm_continuumHeat_increment_lower_bound hd hf hfc hx hT
  have hL : Tendsto (fun ε : ℝ => |Real.log ε|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hθ := (kappa_half_ratio_tendsto hd).eventually (eventually_gt_nhds (half_lt_self hlog))
  have hs := eventually_kappa_scaled_time_mem hd ht.1 hδ
  have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε'
    exact ⟨hε, hε'⟩
  refine ⟨t, ht, (C * t) * (Real.log 2 / 2),
    mul_pos (mul_pos hC ht.1) (half_pos hlog), ?_⟩
  filter_upwards [hN, hs, hθ, hL.eventually_gt_atTop 0, hεsmall]
    with ε hNε hsε hθε hLε hε
  obtain ⟨hmem, hnorm⟩ := hNε _ hsε
  refine ⟨hmem, ?_⟩
  have hkh : 0 < kappa d (ε / 2) :=
    LongRange.kappa_pos hd ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have htime : t - (kappa d ε / kappa d (ε / 2)) * t =
      t * ((kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2)) := by
    field_simp
  calc
    (C * t) * (Real.log 2 / 2) ≤
        (C * t) * (((kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2)) * |Real.log ε|) :=
      mul_le_mul_of_nonneg_left hθε.le (mul_nonneg hC.le ht.1.le)
    _ = |Real.log ε| * (C * (t - (kappa d ε / kappa d (ε / 2)) * t)) := by rw [htime]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hLε.le

/-- The supremum of the lattice heat error on a bounded time interval. -/
def latticeHeatErrorSup {d : ℕ} (ε : ℝ) (a : Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (T : ℝ) : ℝ :=
  sSup ((fun s => latticeNorm ε (fun q => latticeHeat ε a f s q -
    continuumHeat f s (physical ε q))) '' Set.Icc 0 T)

/-- The two heat errors have a positive inverse-logarithmic combined lower bound. -/
theorem eventually_scaling_error_lower_bound {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ C > 0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      C ≤ |Real.log ε| * (latticeHeatErrorSup (ε / 2) a (fun x => f ((2 : ℝ) • x)) T +
        Real.sqrt ((2 : ℝ)⁻¹ ^ d) * latticeHeatErrorSup ε a f T) := by
  obtain ⟨t, ht, C, hC, hN⟩ := eventually_scaled_heat_mismatch_lower_bound hd hf hfc hx hT
  let A : ℝ := Real.sqrt ((2 : ℝ)⁻¹ ^ d)
  have hA : 0 < A := Real.sqrt_pos.2 (pow_pos (by norm_num) d)
  have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with ε hε hε'
    exact ⟨hε, hε'⟩
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  filter_upwards [hN, hεsmall] with ε hNε hε
  have hcomp := heat_scaling_error_le_sup_of_smooth hd hε hlam ha hf hfc
    (T := T) (t := t / 4) (by linarith [ht.1]) (by linarith [ht.2])
  rw [show 4 * (t / 4) = t by ring,
    show (4 * kappa d ε / kappa d (ε / 2)) * (t / 4) =
      (kappa d ε / kappa d (ε / 2)) * t by ring] at hcomp
  change A * latticeNorm ε (fun q => continuumHeat f t (physical ε q) -
      continuumHeat f ((kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) ≤
    latticeHeatErrorSup (ε / 2) a (fun x => f ((2 : ℝ) • x)) T +
      A * latticeHeatErrorSup ε a f T at hcomp
  calc
    A * C ≤ A * (|Real.log ε| * latticeNorm ε (fun q => continuumHeat f t (physical ε q) -
        continuumHeat f ((kappa d ε / kappa d (ε / 2)) * t) (physical ε q))) :=
      mul_le_mul_of_nonneg_left hNε.2 hA.le
    _ = |Real.log ε| * (A * latticeNorm ε (fun q => continuumHeat f t (physical ε q) -
        continuumHeat f ((kappa d ε / kappa d (ε / 2)) * t) (physical ε q))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (abs_nonneg _)

/-- The two heat errors cannot both have a rate smaller than the inverse logarithm. -/
theorem scaling_obstruction {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ¬ (Tendsto (fun ε : ℝ => |Real.log ε| * latticeHeatErrorSup ε a f T)
          (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ => |Real.log ε| *
        latticeHeatErrorSup (ε / 2) a (fun x => f ((2 : ℝ) • x)) T) (𝓝[>] 0) (𝓝 0)) := by
  rintro ⟨h1, h2⟩
  obtain ⟨C, hC, hbound⟩ := eventually_scaling_error_lower_bound hd hlam ha hf hfc hx hT
  let A : ℝ := Real.sqrt ((2 : ℝ)⁻¹ ^ d)
  have hlim : Tendsto (fun ε : ℝ => |Real.log ε| *
      (latticeHeatErrorSup (ε / 2) a (fun x => f ((2 : ℝ) • x)) T +
        A * latticeHeatErrorSup ε a f T)) (𝓝[>] 0) (𝓝 0) := by
    have h := h2.add (h1.const_mul A)
    simp only [mul_zero, zero_add] at h
    convert h using 1
    funext ε
    ring
  have hsmall := hlim.eventually (eventually_lt_nhds hC)
  have hbad : ∀ᶠ ε : ℝ in 𝓝[>] 0, False := by
    filter_upwards [hbound, hsmall] with ε hboundε hsmallε
    exact (not_lt_of_ge hboundε) hsmallε
  obtain ⟨_, h⟩ := hbad.exists
  exact h

end
end LongRangeHeat
