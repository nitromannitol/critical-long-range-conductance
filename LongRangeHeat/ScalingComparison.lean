import LongRangeHeat.ScalingNorm
import LongRangeHeat.Scaling
import LongRangeHeat.Forcing
import LongRangeHeat.Sampling

/-!
# Comparison of heat errors under scaling

The continuum time mismatch is bounded by the errors at the original and halved lattice scales.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LongRange

noncomputable section

variable {d : ℕ}

/-- Reversing a difference does not change its lattice norm. -/
theorem latticeNorm_sub_comm (ε : ℝ) (v w : Site d → ℝ) :
    latticeNorm ε (fun q => v q - w q) = latticeNorm ε (fun q => w q - v q) := by
  unfold latticeNorm latticeNormSq
  congr 2
  apply tsum_congr
  intro q
  dsimp only
  rw [← neg_sub (w q) (v q), neg_sq]

/-- A triangle inequality for the difference of two continuum profiles and a common lattice field. -/
theorem latticeNorm_sub_le (ε : ℝ) (hε : 0 ≤ ε) (u v w : Site d → ℝ)
    (huv : MemL2 (fun q => u q - v q)) (huw : MemL2 (fun q => u q - w q)) :
    latticeNorm ε (fun q => v q - w q) ≤
      latticeNorm ε (fun q => u q - v q) + latticeNorm ε (fun q => u q - w q) := by
  have hvu : MemL2 (fun q => v q - u q) := by
    unfold MemL2 at *
    convert huv using 1
    ext q
    dsimp only
    rw [← neg_sub (u q) (v q), neg_sq]
  have h := latticeNorm_add_le hε hvu huw
  have heq : (fun q => (v q - u q) + (u q - w q)) = (fun q => v q - w q) := by
    funext q
    ring
  rw [heq, latticeNorm_sub_comm ε v u] at h
  exact h

/-- Halving the spacing does not decrease the normalization. -/
theorem kappa_le_kappa_half {ε : ℝ} (hε : 0 < ε) :
    kappa d ε ≤ kappa d (ε / 2) := by
  have h := kappa_half_sub_eq_annulus_sum (d := d) hε
  have hs : 0 ≤ ∑ w ∈ LatticeProb.Euclidean.LatticeAnnulusRiemann.annulusIndices d (1 / ε),
      Real.rpow (radius (physical 1 w)) (-(d : ℝ)) := by
    apply Finset.sum_nonneg
    intro w hw
    exact Real.rpow_nonneg (radius_nonneg _) _
  linarith

/-- The time in the original lattice equation lies in the same interval as the scaled time. -/
theorem scaled_heat_time_mem (hd : 1 ≤ d) {ε t T : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (ht : 0 ≤ t) (hT : 4 * t ≤ T) :
    (4 * kappa d ε / kappa d (ε / 2)) * t ∈ Set.Icc (0 : ℝ) T := by
  have hk : 0 < kappa d ε := LongRange.kappa_pos hd ⟨hε.1, by linarith [hε.2]⟩
  have kh : 0 < kappa d (ε / 2) :=
    LongRange.kappa_pos hd ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hratio : kappa d ε / kappa d (ε / 2) ≤ 1 :=
    (div_le_one kh).2 (kappa_le_kappa_half hε.1)
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_right hratio (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht)
    calc
      (4 * kappa d ε / kappa d (ε / 2)) * t =
          (kappa d ε / kappa d (ε / 2)) * (4 * t) := by ring
      _ ≤ 4 * t := by simpa only [one_mul] using hmul
      _ ≤ T := hT

/-- Under halving, the continuum time mismatch is controlled by the two heat errors. -/
theorem heat_scaling_error_comparison (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (a : Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (h₁ : MemL2 (fun q => latticeHeat ε a f
        ((4 * kappa d ε / kappa d (ε / 2)) * t) q -
      continuumHeat f (4 * t) (physical ε q)))
    (h₂ : MemL2 (fun q => latticeHeat ε a f
        ((4 * kappa d ε / kappa d (ε / 2)) * t) q -
      continuumHeat f ((4 * kappa d ε / kappa d (ε / 2)) * t) (physical ε q))) :
    Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
        latticeNorm ε (fun q => continuumHeat f (4 * t) (physical ε q) -
          continuumHeat f ((4 * kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) ≤
      latticeNorm (ε / 2) (fun q => latticeHeat (ε / 2) a (fun x => f (2 • x)) t q -
        continuumHeat (fun x => f (2 • x)) t (physical (ε / 2) q)) +
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * latticeNorm ε (fun q => latticeHeat ε a f
        ((4 * kappa d ε / kappa d (ε / 2)) * t) q -
        continuumHeat f ((4 * kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) := by
  have h := latticeNorm_sub_le ε hε.1.le _ _ _ h₁ h₂
  have hscale := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg ((2 : ℝ)⁻¹ ^ d))
  rw [mul_add] at hscale
  have heq : (fun q => latticeHeat (ε / 2) a (fun x => f (2 • x)) t q -
        continuumHeat (fun x => f (2 • x)) t (physical (ε / 2) q)) =
      (fun q => latticeHeat ε a f ((4 * kappa d ε / kappa d (ε / 2)) * t) q -
        continuumHeat f (4 * t) (physical ε q)) := by
    funext q
    rw [latticeHeat_half hd ⟨hε.1, by linarith [hε.2]⟩ a f t q]
    have hp : physical (ε / 2) q = (1 / 2 : ℝ) • physical ε q := by
      ext i
      simp only [physical, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hp, continuumHeat_half hd f ht]
  rw [heq, latticeNorm_half]
  exact hscale

/-- The scaling comparison for compactly supported continuous initial data and bounded
conductances. -/
theorem heat_scaling_error_comparison_of_compact_support (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
        latticeNorm ε (fun q => continuumHeat f (4 * t) (physical ε q) -
          continuumHeat f ((4 * kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) ≤
      latticeNorm (ε / 2) (fun q => latticeHeat (ε / 2) a (fun x => f (2 • x)) t q -
        continuumHeat (fun x => f (2 • x)) t (physical (ε / 2) q)) +
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * latticeNorm ε (fun q => latticeHeat ε a f
        ((4 * kappa d ε / kappa d (ε / 2)) * t) q -
        continuumHeat f ((4 * kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) := by
  have hε1 : ε ≤ 1 := by linarith [hε.2]
  have hk : 0 ≤ (4 * kappa d ε / kappa d (ε / 2)) * t := by
    have hkp : 0 < kappa d ε := LongRange.kappa_pos hd ⟨hε.1, by linarith [hε.2]⟩
    have hkhalf : 0 < kappa d (ε / 2) :=
      LongRange.kappa_pos hd ⟨by linarith [hε.1], by linarith [hε.2]⟩
    positivity
  obtain ⟨C, hC⟩ := exists_sum_sq_continuumHeat_le hd hf hfc
  have hc (s : ℝ) (hs : 0 ≤ s) :
      MemL2 (fun q => continuumHeat f s (physical ε q)) := by
    simpa only [MemL2, add_zero] using (hC ε hε.1 hε1 s hs 0).1
  have hu := memL2_latticeHeat hd hε.1 hlam ha hfc
    ((4 * kappa d ε / kappa d (ε / 2)) * t)
  exact heat_scaling_error_comparison hd hε a f ht
    (memL2_sub hu (hc (4 * t) (by positivity))) (memL2_sub hu (hc _ hk))

end
end LongRangeHeat
