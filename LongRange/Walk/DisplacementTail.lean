import LongRange.Walk.Displacement
import LongRange.HeatKernel.Bounds

/-!
# The displacement tail of the rescaled walk

Proposition B.2 discharges the off-diagonal hypothesis of the conditional displacement bound,
giving the estimate (e.displacement.tail) of Proposition 6.1, Step 1, from the cited inputs.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open MeasureTheory
open scoped NNReal

variable {d : ℕ}

/-- The displacement tail (e.displacement.tail): uniformly in `ε ∈ (0,1)` and the start,
`P_x(|X^ε_t − x| > η) ≤ C t (1 + log(2+η)) / η²`, with a constant depending on the
configuration. -/
theorem walk_displacement_tail (hMSC : LatticeProb.External.MuruganSaloffCoste)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (t : ℝ≥0) (x : Site d) (η : ℝ), 0 < η →
      ((walkRates hd hε.1 hlam a ha).transitionKernel t x)
          {y | η < radius (physical ε y - physical ε x)} ≤
        ENNReal.ofReal (C * t * (1 + Real.log (2 + η)) / η ^ 2) := by
  obtain ⟨C₀, hC₀, hoff⟩ := unitHeat_offDiagonal_of_cited hMSC hNash hDavies hd hlam a ha
  refine displacement_tail_of_offDiagonal hd hlam a ha (C₀ := C₀) ?_
  intro t x y hxy
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    have hzero : ((unitRates hd hlam a ha).transitionKernel 0 x).real {y} = 0 := by
      rw [JumpChain.BoundedRates.transitionKernel_zero, measureReal_def,
        ProbabilityTheory.Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton y),
        Set.indicator_of_notMem (by simpa using hxy), ENNReal.toReal_zero]
    rw [hzero]
    simp
  · calc ((unitRates hd hlam a ha).transitionKernel t x).real {y}
        ≤ C₀ * min ((1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
            (t * Real.log (2 + radius (physical 1 (y - x))) /
              radius (physical 1 (y - x)) ^ (d + 2)) := hoff t (pos_iff_ne_zero.mpr ht) x y hxy
      _ ≤ C₀ * (t * Real.log (2 + radius (physical 1 (y - x))) /
              radius (physical 1 (y - x)) ^ (d + 2)) := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) hC₀.le
      _ = C₀ * t * Real.log (2 + radius (physical 1 (y - x))) /
              radius (physical 1 (y - x)) ^ (d + 2) := by ring

end LongRange
