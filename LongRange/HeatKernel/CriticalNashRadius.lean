import LongRange.HeatKernel.CriticalNashPreparation

/-!
# Balancing radius for the critical Nash estimate

The explicit critical scale attains every value above its value at one.
-/

open LatticeProb

namespace LatticeProb.Graph.LongRangeKernel

/-- The product of the critical pseudo-Poincaré scale and lattice volume. -/
noncomputable def criticalNashRadiusScale (d : ℕ) (r : ℝ) : ℝ :=
  (r ^ 2 / Real.log (1 + r)) * latticeVolumeProfile d r

/-- The radius scale dominates the radius on the positive unit ray. -/
theorem le_criticalNashRadiusScale (d : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    r ≤ criticalNashRadiusScale d r := by
  have hlog : 0 < Real.log (1 + r) := Real.log_pos (by linarith)
  have hlog_le : Real.log (1 + r) ≤ r := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + r by linarith)]
  have hvolume : (1 : ℝ) ≤ latticeVolumeProfile d r := by
    unfold latticeVolumeProfile
    exact one_le_pow₀ (by linarith)
  have hrscale : r ≤ r ^ 2 / Real.log (1 + r) := by
    apply (le_div_iff₀ hlog).2
    nlinarith
  unfold criticalNashRadiusScale
  have hmul := mul_nonneg (show (0 : ℝ) ≤ r ^ 2 / Real.log (1 + r) by positivity)
    (sub_nonneg.mpr hvolume)
  exact hrscale.trans (by nlinarith)

/-- Every value above the unit-radius scale has a balancing radius. -/
theorem exists_criticalNashRadiusScale_eq (d : ℕ) {t : ℝ}
    (ht : criticalNashRadiusScale d 1 ≤ t) :
    ∃ r : ℝ, 1 ≤ r ∧ criticalNashRadiusScale d r = t := by
  let b := max 1 t
  have hb : (1 : ℝ) ≤ b := le_max_left _ _
  have htb : t ≤ criticalNashRadiusScale d b :=
    (le_max_right 1 t).trans (le_criticalNashRadiusScale d hb)
  have hc : ContinuousOn (criticalNashRadiusScale d) (Set.Icc 1 b) := by
    unfold criticalNashRadiusScale latticeVolumeProfile
    apply ((continuousOn_id.pow 2).div ?_ ?_).mul
      ((continuousOn_const.add continuousOn_id).pow d)
    · exact (continuousOn_const.add continuousOn_id).log (by
        intro x hx; simp only [Pi.add_apply, id_eq]; linarith [hx.1])
    · intro x hx
      exact (Real.log_pos (by linarith [hx.1])).ne'
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hb hc ⟨ht, htb⟩
  exact ⟨r, hr.1, heq⟩

/-- A positive energy bounded by twice the squared absolute sum admits a
balancing radius for the two terms of the critical estimate. -/
theorem exists_criticalNash_balancing_radius (d : ℕ) {L E : ℝ}
    (hE : 0 < E) (hbound : E ≤ 2 * L ^ 2) :
    ∃ r : ℝ, 1 ≤ r ∧
      criticalNashRadiusScale d r * E = 2 * criticalNashRadiusScale d 1 * L ^ 2 := by
  have hF : 0 < criticalNashRadiusScale d 1 :=
    lt_of_lt_of_le (by norm_num) (le_criticalNashRadiusScale d (le_refl 1))
  let t := 2 * criticalNashRadiusScale d 1 * L ^ 2 / E
  have ht : criticalNashRadiusScale d 1 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hE).2
    nlinarith [mul_nonneg hF.le (sub_nonneg.mpr hbound)]
  obtain ⟨r, hr, heq⟩ := exists_criticalNashRadiusScale_eq d ht
  refine ⟨r, hr, ?_⟩
  rw [heq]
  dsimp [t]
  exact div_mul_cancel₀ _ hE.ne'

end LatticeProb.Graph.LongRangeKernel
