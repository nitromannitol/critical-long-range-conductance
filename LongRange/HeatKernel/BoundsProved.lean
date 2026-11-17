import LongRange.HeatKernel.Bounds
import LongRange.HeatKernel.UniformOffDiagonal

/-!
# Unit-walk heat-kernel bounds

The uniform estimates specialize to every admissible conductance field.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

variable {d : ℕ}

/-- Proposition B.1: the unit walk has the on-diagonal heat bound. -/
theorem unitHeat_onDiagonal_of_msc_proved
    (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x y : Site d),
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) := by
  obtain ⟨C, hC, h⟩ := unitHeat_onDiagonal_uniform_proved d hd hlam
  exact ⟨C, hC, h a ha⟩

/-- Proposition B.2: the unit walk has the off-diagonal minimum bound. -/
theorem unitHeat_offDiagonal_of_cited_proved
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x y : Site d, x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * min ((1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
          (t * Real.log (2 + radius (physical 1 (y - x))) /
            radius (physical 1 (y - x)) ^ (d + 2)) := by
  obtain ⟨C, hC, h⟩ := unitHeat_offDiagonal_uniform_proved hNash hDavies d hd hlam
  exact ⟨C, hC, h a ha⟩

end LongRange
