import LongRange.HeatKernel.CriticalSubordinateProfile
import LongRange.Support.Graph.LongRangeKernel.LatticeVolume

/-!
# Subordinate kernel and lattice ball volume

The critical subordinate kernel has a lower bound in terms of the actual graph-ball volume.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The lattice ball of radius zero agrees with every ball of radius less than one. -/
theorem weightedLattice_volume_zero_eq_half {d : ℕ} (hd : 0 < d) (x : Site d) :
    (weightedLattice d hd).volume x 0 = (weightedLattice d hd).volume x (1 / 2) := by
  rw [weightedLattice_volume_eq_tsum hd, weightedLattice_volume_eq_tsum hd]
  congr 1
  funext y
  have h : ((graphNorm y : ℝ) ≤ 0) ↔ ((graphNorm y : ℝ) ≤ 1 / 2) := by
    constructor
    · intro hy; linarith
    · intro hy
      have hn : graphNorm y = 0 := by
        by_contra hn
        have hn1 : 1 ≤ graphNorm y := Nat.one_le_iff_ne_zero.mpr hn
        have hn1r : (1 : ℝ) ≤ graphNorm y := by exact_mod_cast hn1
        linarith
      simp [hn]
  simp only [h]

/-- Polynomial lattice volume comparison includes radius zero. -/
theorem weightedLattice_volume_lower_nonneg {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 1 < C ∧ ∀ (x : Site d) (r : ℝ), 0 ≤ r →
      ENNReal.ofReal (C⁻¹ * latticeVolumeProfile d r) ≤
        (weightedLattice d hd).volume x r := by
  obtain ⟨C, hC, hvol⟩ := weightedLattice_volume_comparable hd
  refine ⟨C, hC, ?_⟩
  intro x r hr
  by_cases hz : r = 0
  · subst r
    rw [weightedLattice_volume_zero_eq_half hd x]
    apply le_trans _ (hvol x (1 / 2) (by norm_num)).1
    apply ENNReal.ofReal_le_ofReal
    gcongr
    simp only [latticeVolumeProfile, add_zero, one_pow]
    exact one_le_pow₀ (by norm_num)
  · exact (hvol x r (lt_of_le_of_ne hr (Ne.symm hz))).1

/-- The subordinate kernel dominates the inverse ball-volume and quadratic-scale profile. -/
theorem weightedLattice_criticalSubordinate_ball_volume_lower {d : ℕ} (hd : 0 < d) :
    ∃ A : ℝ≥0∞, 0 < A ∧ ∀ x y,
      A / ((weightedLattice d hd).volume x
          ((weightedLattice d hd).graph.dist x y : ℝ) *
        ENNReal.ofReal (quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤
        criticalSubordinateDensity (weightedLattice d hd).mass
          (averagedDensity (weightedLattice d hd).mass
            (weightedLattice d hd).referenceDensity) x y := by
  obtain ⟨A, hA, hlower⟩ := weightedLattice_criticalSubordinate_volume_profile_lower hd
  obtain ⟨C, hC, hvol⟩ := weightedLattice_volume_lower_nonneg hd
  let c : ℝ≥0∞ := ENNReal.ofReal C
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (by linarith)
  have hcfin : c ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨A / c, ENNReal.div_pos hA.ne' hcfin, ?_⟩
  intro x y
  let r : ℝ := ((weightedLattice d hd).graph.dist x y : ℝ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hv := hvol x r hr
  have hp : 0 ≤ latticeVolumeProfile d r := by unfold latticeVolumeProfile; positivity
  have hcv : ENNReal.ofReal (latticeVolumeProfile d r) ≤
      c * (weightedLattice d hd).volume x r := by
    have h := mul_le_mul_left hv c
    have heq : c * ENNReal.ofReal (C⁻¹ * latticeVolumeProfile d r) =
        ENNReal.ofReal (latticeVolumeProfile d r) := by
      dsimp [c]
      rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ C)]
      congr 1
      field_simp
    rw [mul_comm _ c, heq, mul_comm _ c] at h
    exact h
  have hi := ENNReal.inv_le_inv.mpr hcv
  have hs : 0 < quadraticScale r := by unfold quadraticScale; positivity
  have hpp : 0 < latticeVolumeProfile d r := by unfold latticeVolumeProfile; positivity
  have hscale0 : ENNReal.ofReal (quadraticScale r) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have hscaleTop : ENNReal.ofReal (quadraticScale r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hprof0 : ENNReal.ofReal (latticeVolumeProfile d r) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpp).ne'
  have hinv1 := ENNReal.mul_inv (a := c) (b := (weightedLattice d hd).volume x r)
    (Or.inl hc.ne') (Or.inl hcfin)
  have hinv2 := ENNReal.mul_inv (a := (weightedLattice d hd).volume x r)
    (b := ENNReal.ofReal (quadraticScale r)) (Or.inr hscaleTop) (Or.inr hscale0)
  have hinv3 := ENNReal.mul_inv (a := ENNReal.ofReal (latticeVolumeProfile d r))
    (b := ENNReal.ofReal (quadraticScale r)) (Or.inl hprof0) (Or.inr hscale0)
  calc
    _ = A * ((c * (weightedLattice d hd).volume x r)⁻¹ *
        (ENNReal.ofReal (quadraticScale r))⁻¹) := by
      change A / c / ((weightedLattice d hd).volume x r *
        ENNReal.ofReal (quadraticScale r)) = _
      rw [div_eq_mul_inv, div_eq_mul_inv, hinv1, hinv2]
      simp only [mul_assoc]
    _ ≤ A * ((ENNReal.ofReal (latticeVolumeProfile d r))⁻¹ *
        (ENNReal.ofReal (quadraticScale r))⁻¹) := by gcongr
    _ = A * ENNReal.ofReal (1 / (latticeVolumeProfile d r * quadraticScale r)) := by
      rw [ENNReal.ofReal_div_of_pos (mul_pos hpp hs),
        ENNReal.ofReal_one, one_div, ENNReal.ofReal_mul hp, hinv3]
    _ ≤ _ := hlower x y

end LatticeProb.Graph.LongRangeKernel
