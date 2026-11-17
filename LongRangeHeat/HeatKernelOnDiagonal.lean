import LongRangeHeat.HeatKernelBounds
import LongRange.Statements.HeatKernelOnDiagonal

/-!
# Rescaled on-diagonal heat-kernel estimate

The unit-walk estimate gives Proposition 4.1(i) uniformly over admissible fields.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice Set
open scoped NNReal
open MeasureTheory
open LongRange (kappa kappa_le Edge unitRates)

noncomputable section

variable {d : ℕ}

/-- The on-diagonal bound (i): `ε^{-d} P_x[X_h = y] ≤ C h^{-d/2}` for `h ≥ ε`. -/
theorem heat_kernel_on_diagonal_proved (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ x y : Site d, ∀ h : ℝ≥0, ε ≤ h →
      (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε.1 hlam a ha).transitionKernel h x).real {y} ≤
        C / (h : ℝ) ^ ((d : ℝ) / 2) := by
  obtain ⟨C₁, hC₁, hdiag⟩ := LongRange.Statements.heatkernel_onDiagonal_proved d hd hlam
  obtain ⟨Ck, hCk, hlogk⟩ := exists_kappa_le_mul_log hd
  refine ⟨C₁ * Ck ^ ((d : ℝ) / 2), by positivity, fun ε hε a ha x y h hεh => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hεmem : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, by linarith [hε.2]⟩
  have hκ : 0 < kappa d ε := LongRange.kappa_pos hd hεmem
  have hh0 : 0 < (h : ℝ) := lt_of_lt_of_le hε0 hεh
  have heq := LongRange.rescaledDensity_eq_unit hd hεmem hlam a ha h x y
  change (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε.1 hlam a ha).transitionKernel h x).real {y} = _
    at heq
  rw [heq]
  set t' : ℝ≥0 := NNReal.mk (1 / (kappa d ε * ε ^ 2)) (by positivity [LongRange.kappa_pos hd hεmem])
    * h with ht'
  have ht'val : (t' : ℝ) = h / (kappa d ε * ε ^ 2) := by
    rw [ht', NNReal.coe_mul, NNReal.coe_mk]; ring
  have ht'pos : 0 < (t' : ℝ) := by rw [ht'val]; positivity
  have hlog : kappa d ε ≤ Ck * Real.log (2 + (t' : ℝ)) := by
    rw [ht'val]; exact hlogk ε hε h hεh
  have hu : (h : ℝ) / (Ck * ε ^ 2) ≤ (t' : ℝ) * Real.log (2 + (t' : ℝ)) := by
    have hlog' : kappa d ε / Ck ≤ Real.log (2 + (t' : ℝ)) := by
      rw [div_le_iff₀ hCk]; linarith
    calc (h : ℝ) / (Ck * ε ^ 2) = (t' : ℝ) * (kappa d ε / Ck) := by
          rw [ht'val]; field_simp
      _ ≤ (t' : ℝ) * Real.log (2 + (t' : ℝ)) := mul_le_mul_of_nonneg_left hlog' ht'pos.le
  have hbase : 0 < (h : ℝ) / (Ck * ε ^ 2) := by positivity
  have h1 := hdiag a ha t' x y
  have h2 : (1 + (t' : ℝ) * Real.log (2 + (t' : ℝ))) ^ (-((d : ℝ) / 2)) ≤
      ((h : ℝ) / (Ck * ε ^ 2)) ^ (-((d : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by
      have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
      linarith)
  have hε2 : (ε ^ 2) ^ ((d : ℝ) / 2) = ε ^ d := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε0.le]
    rw [show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3 : ((h : ℝ) / (Ck * ε ^ 2)) ^ (-((d : ℝ) / 2)) =
      Ck ^ ((d : ℝ) / 2) * ε ^ d / (h : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.rpow_neg hbase.le, ← Real.inv_rpow hbase.le, inv_div,
      Real.div_rpow (by positivity) hh0.le, Real.mul_rpow hCk.le (by positivity), hε2]
  have hεd : 0 < ε ^ d := pow_pos hε0 d
  calc (ε ^ d)⁻¹ * ((unitRates hd hlam a ha).transitionKernel t' x).real {y}
      ≤ (ε ^ d)⁻¹ * (C₁ * (1 + (t' : ℝ) * Real.log (2 + (t' : ℝ))) ^ (-((d : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hεd.le)
    _ ≤ (ε ^ d)⁻¹ * (C₁ * (Ck ^ ((d : ℝ) / 2) * ε ^ d / (h : ℝ) ^ ((d : ℝ) / 2))) := by
        rw [← h3]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC₁.le)
          (inv_nonneg.mpr hεd.le)
    _ = C₁ * Ck ^ ((d : ℝ) / 2) / (h : ℝ) ^ ((d : ℝ) / 2) := by
        field_simp

end

end LongRangeHeat
