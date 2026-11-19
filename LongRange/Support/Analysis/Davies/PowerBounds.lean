import LongRange.Support.Analysis.Davies.PowerStep
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Coordinate and level bounds for finite power sums

Finite-dimensional estimates used in the Davies iteration.
-/

namespace LatticeProb.Davies.FiniteJumpForm

open Set

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A nonnegative coordinate is bounded by every positive-power sum. -/
theorem coordinate_le_powSum [DecidableEq ι] (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (p : ℕ) (hp : 0 < p)
    (i : ι) : u i ≤ Real.rpow (∑ j, u j ^ p) ((p : ℝ)⁻¹) := by
  have hsum : 0 ≤ ∑ j, u j ^ p := Finset.sum_nonneg fun j _ ↦ pow_nonneg (hu j) p
  apply (Real.le_rpow_inv_iff_of_pos (hu i) hsum (Nat.cast_pos.mpr hp)).2
  rw [Real.rpow_natCast]
  exact Finset.single_le_sum (fun j _ ↦ pow_nonneg (hu j) p) (Finset.mem_univ i)

variable [DecidableEq ι] (F : FiniteJumpForm ι)

/-- An even power sum grows at most at its compensated exponential rate. -/
theorem twist_powSum_le {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℕ) (hp : 1 ≤ p)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∑ i, (F.twist ψ f t i) ^ (2 * p)) ≤
      Real.exp ((2 * (p : ℝ) * levelRate Λsq p) * (t - s)) *
        ∑ i, (F.twist ψ f s i) ^ (2 * p) := by
  let a : ℝ := 2 * (p : ℝ) * levelRate Λsq p
  let N : ℝ → ℝ := fun u ↦ ∑ i, (F.twist ψ f u i) ^ (2 * p)
  have ha := F.antitoneOn_level hΛ f hf p hp hs (le_trans hs hst) hst
  change Real.exp (-a * t) * N t ≤ Real.exp (-a * s) * N s at ha
  have hm := mul_le_mul_of_nonneg_left ha (Real.exp_pos (a * t)).le
  have h1 : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (a * t) * Real.exp (-a * s) = Real.exp (a * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change N t ≤ Real.exp (a * (t - s)) * N s
  calc
    N t = Real.exp (a * t) * (Real.exp (-a * t) * N t) := by rw [← mul_assoc, h1, one_mul]
    _ ≤ Real.exp (a * t) * (Real.exp (-a * s) * N s) := hm
    _ = Real.exp (a * (t - s)) * N s := by rw [← mul_assoc, h2]

end
end LatticeProb.Davies.FiniteJumpForm
