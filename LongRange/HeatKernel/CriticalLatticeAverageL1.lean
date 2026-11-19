import LongRange.HeatKernel.CriticalAverageL1
import LongRange.HeatKernel.CriticalLatticePseudoPoincare

/-!
# Absolute-sum bounds for lattice averages

The polynomial growth of lattice balls controls the square sum of their averages.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The reciprocal lattice-ball size is bounded by the reciprocal volume profile. -/
theorem latticeRealGraphBall_card_inv_le {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ((latticeRealGraphBall d R).card : ℝ)⁻¹ ≤ C / latticeVolumeProfile d R := by
  obtain ⟨A, hA, hvol⟩ := latticeVolumeProfile_le_card_latticeGraphBall hd
  refine ⟨(2 : ℝ) ^ d * A, by positivity, ?_⟩
  intro R hR
  let r := ⌊R⌋₊
  have hr : 1 ≤ r := (Nat.le_floor_iff (by linarith : 0 ≤ R)).2 (by simpa using hR)
  have hrR : R < (r : ℝ) + 1 := Nat.lt_floor_add_one R
  have hprofile : latticeVolumeProfile d R ≤
      (2 : ℝ) ^ d * latticeVolumeProfile d r := by
    unfold latticeVolumeProfile
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) r]) d
  have hcard : (0 : ℝ) < (latticeRealGraphBall d R).card := by
    change (0 : ℝ) < (latticeGraphBall d r).card
    exact_mod_cast (latticeGraphBall_nonempty d r).card_pos
  have hv : 0 < latticeVolumeProfile d R := by unfold latticeVolumeProfile; positivity
  have hvol' : latticeVolumeProfile d R ≤ (2 : ℝ) ^ d * A *
      (latticeRealGraphBall d R).card := by
    calc
      _ ≤ (2 : ℝ) ^ d * latticeVolumeProfile d r := hprofile
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (hvol r hr)
          (show (0 : ℝ) ≤ (2 : ℝ) ^ d by positivity)
        simpa only [latticeRealGraphBall, ← mul_assoc] using h
  rw [← one_div, div_le_div_iff₀ hcard hv]
  simpa only [one_mul] using hvol'

/-- The square sum of a lattice ball average is controlled by the volume profile. -/
theorem latticeRealGraphBall_average_sq_le {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ f : Site d → ℝ,
      Summable (fun x => |f x|) →
      Summable (fun x => (finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
      (∑' x, (finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
        C * (∑' x, |f x|) ^ 2 / latticeVolumeProfile d R := by
  obtain ⟨C, hC, hcard⟩ := latticeRealGraphBall_card_inv_le hd
  refine ⟨C, hC, ?_⟩
  intro R hR f hf
  have hs : (latticeRealGraphBall d R).Nonempty := latticeGraphBall_nonempty d ⌊R⌋₊
  have h := finsetTranslateAverage_sq_tsum_le_abs_tsum (latticeRealGraphBall d R) hs f hf
  refine ⟨h.1, h.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (hcard R hR) (sq_nonneg (∑' x, |f x|))
  convert hh using 1 <;> ring

end LatticeProb.Graph.LongRangeKernel
