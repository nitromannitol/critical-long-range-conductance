import LongRange.HeatKernel.CriticalSubordinateUpper
import LongRange.HeatKernel.CriticalSubordinateVolume

/-!
# Subordinate kernel upper bound and lattice ball volume

The critical subordinate kernel is bounded by the inverse graph-ball volume
and quadratic scale.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- Polynomial lattice volume comparison from above includes radius zero. -/
theorem weightedLattice_volume_upper_nonneg {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 1 < C ∧ ∀ (x : Site d) (r : ℝ), 0 ≤ r →
      (weightedLattice d hd).volume x r ≤ ENNReal.ofReal (C * latticeVolumeProfile d r) := by
  obtain ⟨C, hC, hvol⟩ := weightedLattice_volume_comparable hd
  refine ⟨C, hC, ?_⟩
  intro x r hr
  by_cases hz : r = 0
  · subst r
    rw [weightedLattice_volume_small hd x (by norm_num) (by norm_num)]
    simpa [latticeVolumeProfile] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ C by linarith)
  · exact (hvol x r (lt_of_le_of_ne hr (Ne.symm hz))).2

/-- The subordinate kernel is bounded above by the inverse ball volume and quadratic scale. -/
theorem weightedLattice_criticalSubordinate_ball_volume_upper {d : ℕ} (hd : 0 < d) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x y,
      criticalSubordinateDensity (weightedLattice d hd).mass
        (averagedDensity (weightedLattice d hd).mass
          (weightedLattice d hd).referenceDensity) x y ≤
        B / ((weightedLattice d hd).volume x
          ((weightedLattice d hd).graph.dist x y : ℝ) *
          ENNReal.ofReal (quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) := by
  obtain ⟨B, hB, hupper⟩ := weightedLattice_criticalSubordinate_volume_profile_upper hd
  obtain ⟨C, hC, hvol⟩ := weightedLattice_volume_upper_nonneg hd
  let c : ℝ≥0∞ := ENNReal.ofReal C
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (by linarith)
  have hcfin : c ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨B * c, ENNReal.mul_lt_top hB (lt_top_iff_ne_top.mpr hcfin), ?_⟩
  intro x y
  let r : ℝ := ((weightedLattice d hd).graph.dist x y : ℝ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hp : 0 < latticeVolumeProfile d r := by unfold latticeVolumeProfile; positivity
  have hs : 0 < quadraticScale r := by unfold quadraticScale; positivity
  have hv : (weightedLattice d hd).volume x r ≤ c * ENNReal.ofReal (latticeVolumeProfile d r) := by
    simpa [c, ENNReal.ofReal_mul (show 0 ≤ C by linarith)] using hvol x r hr
  have hi := ENNReal.inv_le_inv.mpr hv
  have hprof : (ENNReal.ofReal (latticeVolumeProfile d r))⁻¹ ≤
      c * ((weightedLattice d hd).volume x r)⁻¹ := by
    have h := mul_le_mul_left hi c
    rw [ENNReal.mul_inv (Or.inl hc.ne') (Or.inl hcfin)] at h
    calc
      _ = c * (c⁻¹ * (ENNReal.ofReal (latticeVolumeProfile d r))⁻¹) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc.ne' hcfin, one_mul]
      _ ≤ _ := by
        convert h using 1 <;> ac_rfl
  have hscale0 : ENNReal.ofReal (quadraticScale r) ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hscaleTop : ENNReal.ofReal (quadraticScale r) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    _ ≤ B * ENNReal.ofReal (1 / (quadraticScale r * latticeVolumeProfile d r)) := hupper x y
    _ = B * ((ENNReal.ofReal (latticeVolumeProfile d r))⁻¹ *
        (ENNReal.ofReal (quadraticScale r))⁻¹) := by
      rw [ENNReal.ofReal_div_of_pos (mul_pos hs hp), ENNReal.ofReal_one, one_div,
        ENNReal.ofReal_mul hs.le, ENNReal.mul_inv (Or.inr (ENNReal.ofReal_ne_top))
          (Or.inr (ENNReal.ofReal_pos.mpr hp).ne')]
      ac_rfl
    _ ≤ B * (c * ((weightedLattice d hd).volume x r)⁻¹ *
        (ENNReal.ofReal (quadraticScale r))⁻¹) := by gcongr
    _ = _ := by
      change _ = B * c / ((weightedLattice d hd).volume x r * ENNReal.ofReal (quadraticScale r))
      rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr hscaleTop) (Or.inr hscale0)]
      simp only [mul_assoc]

end LatticeProb.Graph.LongRangeKernel
