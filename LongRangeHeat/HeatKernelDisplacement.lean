import LongRangeHeat.HeatKernelBounds
import LongRange.HeatKernel.Rescaled

/-!
# Displacement bound for the rescaled walk

The uniform spatial kernel estimate implies the displacement bound of Proposition 4.1.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice Set
open scoped NNReal
open MeasureTheory
open LongRange (kappa kappa_le Edge unitRates)

noncomputable section

variable {d : ℕ}

/-- The displacement bound (ii): `P_x[|X_h - x| > R] ≤ C h (1 + log (1 + R)) / R²` for `R ≥ ε`. -/
theorem heat_kernel_displacement_proved
    (hNash : External.ChenKimKumagaiWangNash) (hDavies : External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ x : Site d, ∀ h : ℝ≥0, 0 < h → ∀ R : ℝ, ε ≤ R →
      ((LongRange.walkRates hd hε.1 hlam a ha).transitionKernel h x).real
          {y | R < radius (physical ε (y - x))} ≤
        C * h * (1 + Real.log (1 + R)) / R ^ 2 := by
  obtain ⟨C₀, hC₀, hker⟩ := LongRange.rescaledDensity_offDiagonal_uniform_proved hNash hDavies d hd hlam
  obtain ⟨Ct, hCt, htail⟩ := exists_tail_sum_le hd
  obtain ⟨Cl, hCl, hlogb⟩ := exists_log_two_add_div_le hd
  refine ⟨C₀ * Ct * Cl, by positivity, fun ε hε a ha x h hh R hεR => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hεmem : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, by linarith [hε.2]⟩
  have hR0 : 0 < R := lt_of_lt_of_le hε0 hεR
  have hκ : 0 < kappa d ε := LongRange.kappa_pos hd hεmem
  have hhR : (0 : ℝ) < h := hh
  obtain ⟨hsumT, hT⟩ := htail ε hεmem R hεR
  set μ := (LongRange.walkRates hd hε.1 hlam a ha).transitionKernel h x with hμ
  set S : Set (Site d) := {y | R < radius (physical ε (y - x))} with hS
  set g : Site d → ℝ := fun w => if R < radius (physical ε w) then
    Real.log (2 + radius (physical ε w) / ε) / radius (physical ε w) ^ (d + 2) else 0 with hg
  set K : ℝ := ε ^ d * C₀ * ((h : ℝ) / kappa d ε) with hK
  have hSmeas : MeasurableSet S := (Set.to_countable S).measurableSet
  have hsing : ∀ y, S.indicator (fun y => μ.real {y}) y ≤ K * g (y - x) := fun y => by
    by_cases hy : y ∈ S
    · have hyR : R < radius (physical ε (y - x)) := hy
      have hxy : x ≠ y := by
        rintro rfl
        have : radius (physical ε (x - x)) = 0 := by simp [radius, physical]
        rw [this] at hyR
        linarith
      have hb := hker ε hεmem a ha h hh x y hxy
      change (ε ^ d)⁻¹ * μ.real {y} ≤ _ at hb
      have hb' : (ε ^ d)⁻¹ * μ.real {y} ≤ C₀ *
          ((h : ℝ) / kappa d ε * Real.log (2 + radius (physical ε (y - x)) / ε) /
            radius (physical ε (y - x)) ^ (d + 2)) :=
        hb.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC₀.le)
      rw [Set.indicator_of_mem hy]
      simp only [hK, hg, hyR, ↓reduceIte]
      have hεd : 0 < ε ^ d := pow_pos hε0 d
      have := (inv_mul_le_iff₀ hεd).mp hb'
      calc μ.real {y} ≤ ε ^ d * (C₀ * ((h : ℝ) / kappa d ε *
            Real.log (2 + radius (physical ε (y - x)) / ε) /
            radius (physical ε (y - x)) ^ (d + 2))) := this
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hy]
      have hyR : ¬ R < radius (physical ε (y - x)) := hy
      simp [hg, hyR]
  have hnn : ∀ y, 0 ≤ S.indicator (fun y => μ.real {y}) y := fun y => by
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]; exact measureReal_nonneg
    · rw [Set.indicator_of_notMem hy]
  have hsum : Summable (fun y : Site d => K * g (y - x)) :=
    (((Equiv.subRight x).summable_iff (f := g)).mpr hsumT).mul_left K
  have hμS : μ.real S = ∑' y, S.indicator (fun y => μ.real {y}) y := by
    rw [measureReal_def, ← Measure.tsum_indicator_apply_singleton μ S hSmeas,
      ENNReal.tsum_toReal_eq (fun y => ?_)]
    · refine tsum_congr (fun y => ?_)
      by_cases hy : y ∈ S
      · simp [Set.indicator_of_mem hy, measureReal_def]
      · simp [Set.indicator_of_notMem hy]
    · by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]; exact measure_ne_top μ _
      · rw [Set.indicator_of_notMem hy]; exact ENNReal.zero_ne_top
  have hlog := hlogb ε hε R hR0
  calc μ.real S = ∑' y, S.indicator (fun y => μ.real {y}) y := hμS
    _ ≤ ∑' y, K * g (y - x) :=
        (Summable.of_nonneg_of_le hnn hsing hsum).tsum_le_tsum hsing hsum
    _ = K * ∑' w, g w := by
        have := (Equiv.subRight x).tsum_eq g
        simp only [Equiv.subRight_apply] at this
        rw [tsum_mul_left, this]
    _ = C₀ * ((h : ℝ) / kappa d ε) * (ε ^ d * ∑' w, g w) := by rw [hK]; ring
    _ ≤ C₀ * ((h : ℝ) / kappa d ε) * (Ct * Real.log (2 + R / ε) / R ^ 2) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = C₀ * Ct * h * (Real.log (2 + R / ε) / kappa d ε) / R ^ 2 := by field_simp
    _ ≤ C₀ * Ct * h * (Cl * (1 + Real.log (1 + R))) / R ^ 2 := by gcongr
    _ = C₀ * Ct * Cl * h * (1 + Real.log (1 + R)) / R ^ 2 := by ring

end

end LongRangeHeat
