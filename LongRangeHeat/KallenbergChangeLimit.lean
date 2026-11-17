import LongRangeHeat.KallenbergChangeSequence

/-!
# Limits of time changes

Locally uniform limits of time changes with uniformly bounded logarithmic
distortion retain their secant bounds.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Uniform distortion bounds pass to the secants of a pointwise limit. -/
theorem secant_bounds_of_tendsto (l : ℕ → Lambda) (L : Time → Time) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ n, gamma (l n).1 ≤ ENNReal.ofReal C)
    (hlim : ∀ t, Tendsto (fun n => (l n).1 t) atTop (𝓝 (L t)))
    {t s : Time} (hts : t < s) :
    Real.exp (-C) ≤ ((L s : ℝ) - L t) / ((s : ℝ) - t) ∧
      ((L s : ℝ) - L t) / ((s : ℝ) - t) ≤ Real.exp C := by
  have hg (n : ℕ) : (gamma (l n).1).toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound n)
  have hconv : Tendsto (fun n => (((l n).1 s : ℝ) - (l n).1 t) /
      ((s : ℝ) - t)) atTop (𝓝 (((L s : ℝ) - L t) / ((s : ℝ) - t))) := by
    exact (((continuous_subtype_val.tendsto (L s)).comp (hlim s)).sub
      ((continuous_subtype_val.tendsto (L t)).comp (hlim t))).div_const _
  constructor
  · apply ge_of_tendsto hconv
    filter_upwards [] with n
    exact (Real.exp_le_exp.mpr (neg_le_neg (hg n))).trans
      (secant_bounds (l n).1 (ne_of_lt (l n).2.2) hts).1
  · apply le_of_tendsto hconv
    filter_upwards [] with n
    exact (secant_bounds (l n).1 (ne_of_lt (l n).2.2) hts).2 |>.trans
      (Real.exp_le_exp.mpr (hg n))

/-- A half-line map with bounded positive secants is an admissible time change. -/
theorem exists_lambda_of_secant_bounds (L : Time → Time) {C : ℝ} (hC : 0 ≤ C)
    (hzero : L 0 = 0)
    (hsec : ∀ t s : Time, t < s →
      Real.exp (-C) ≤ ((L s : ℝ) - L t) / ((s : ℝ) - t) ∧
        ((L s : ℝ) - L t) / ((s : ℝ) - t) ≤ Real.exp C) :
    ∃ l : Lambda, ∀ t, l.1 t = L t := by
  have hmono : StrictMono L := by
    intro t s hts
    have hd : 0 < (s : ℝ) - t := sub_pos.mpr hts
    have hs := (le_div_iff₀ hd).mp (hsec t s hts).1
    have hp := mul_pos (Real.exp_pos (-C)) hd
    have hr : (L t : ℝ) < L s := sub_pos.mp (lt_of_lt_of_le hp hs)
    exact hr
  have hlip : LipschitzWith ⟨Real.exp C, (Real.exp_pos C).le⟩ L := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change |(L s : ℝ) - L t| ≤ Real.exp C * |(s : ℝ) - t|
    wlog hst : t ≤ s generalizing s t
    · simpa only [abs_sub_comm] using this t s (le_of_not_ge hst)
    rcases hst.eq_or_lt with he | hts
    · subst s
      simp only [sub_self, abs_zero, mul_zero, le_refl]
    have hd : 0 < (s : ℝ) - t := sub_pos.mpr hts
    have hs := (div_le_iff₀ hd).mp (hsec t s hts).2
    have ht : (t : ℝ) ≤ s := hst
    have hL : (L t : ℝ) ≤ L s := (hmono hts).le
    simpa only [abs_of_nonneg (sub_nonneg.mpr ht),
      abs_of_nonneg (sub_nonneg.mpr hL)] using hs
  have hsurj : Function.Surjective L := by
    intro y
    let x : Time := y / ⟨Real.exp (-C), (Real.exp_pos (-C)).le⟩ + 1
    have hx : y ≤ L x := by
      have hxpos : (0 : Time) < x := by dsimp [x]; positivity
      have hxreal : (0 : ℝ) < (x : ℝ) - (0 : Time) := by
        simpa only [NNReal.coe_zero, sub_zero] using (show (0 : ℝ) < (x : ℝ) from hxpos)
      have hs := (le_div_iff₀ hxreal).mp (hsec 0 x hxpos).1
      simp only [hzero, NNReal.coe_zero, sub_zero] at hs
      have he : Real.exp (-C) ≠ 0 := (Real.exp_pos _).ne'
      change Real.exp (-C) * ((y : ℝ) / Real.exp (-C) + 1) ≤ (L x : ℝ) at hs
      have heq : Real.exp (-C) * ((y : ℝ) / Real.exp (-C) + 1) =
          y + Real.exp (-C) := by field_simp
      rw [heq] at hs
      have hr : (y : ℝ) ≤ (L x : ℝ) :=
        le_trans (le_add_of_nonneg_right (Real.exp_pos _).le) hs
      exact hr
    have hy : y ∈ Icc (L 0) (L x) := ⟨by simp only [hzero, zero_le], hx⟩
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc (show (0 : Time) ≤ x from zero_le)
      hlip.continuous.continuousOn hy
    exact ⟨z, hz⟩
  let e : LambdaPrime := hmono.orderIsoOfSurjective L hsurj
  have he : ∀ t, e t = L t := by
    intro t
    exact congrFun (StrictMono.coe_orderIsoOfSurjective L hmono hsurj) t
  have hgamma : gamma e ≤ ENNReal.ofReal C := by
    apply gamma_le_of_secant e hC
    intro t s hts
    simpa only [he] using hsec t s hts
  refine ⟨⟨e, ⟨⟨⟨Real.exp C, (Real.exp_pos C).le⟩, ?_⟩, hgamma.trans_lt ENNReal.ofReal_lt_top⟩⟩, he⟩
  simpa only [show (e : Time → Time) = L from funext he] using hlip

/-- Summable distortion yields an admissible locally uniform limit of the
successive time-change compositions. -/
theorem exists_lambda_tendstoUniformlyOn_changePrefix (l : ℕ → Lambda)
    (hs : (∑' n, gamma (l n).1) ≠ ∞) :
    ∃ L : Lambda, ∀ T : Time,
      TendstoUniformlyOn (fun n => (changePrefix l n).1) L.1 atTop (Iic T) := by
  obtain ⟨L, hL⟩ := exists_tendstoUniformlyOn_changePrefix_of_tsum_ne_top l hs
  let C : ℝ := (∑' n, gamma (l n).1).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hbound (n : ℕ) : gamma (changePrefix l n).1 ≤ ENNReal.ofReal C := by
    rw [show ENNReal.ofReal C = ∑' n, gamma (l n).1 from ENNReal.ofReal_toReal hs]
    exact (gamma_changePrefix_le l n).trans (ENNReal.sum_le_tsum _)
  have hlim (t : Time) : Tendsto (fun n => (changePrefix l n).1 t) atTop (𝓝 (L t)) :=
    (hL t).tendsto_at (Set.mem_Iic.mpr le_rfl)
  have hzero : L 0 = 0 := by
    apply tendsto_nhds_unique (hlim 0)
    simpa only [LambdaPrime.map_zero] using tendsto_const_nhds (x := (0 : Time))
  obtain ⟨Λ, hΛ⟩ := exists_lambda_of_secant_bounds L hC hzero
    (fun _ _ hts => secant_bounds_of_tendsto (changePrefix l) L hC hbound hlim hts)
  refine ⟨Λ, fun T => ?_⟩
  simpa only [show (Λ.1 : Time → Time) = L from funext hΛ] using hL T

end

end LatticeProb.Cadlag.HalfLine
