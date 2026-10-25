import LongRange.HeatKernel.UnitWalk
import LatticeProb.External.MuruganSaloffCoste
import LatticeProb.Graph.LongRangeKernel.LatticeDistance
import LatticeProb.Graph.LongRangeKernel.CriticalVolume
import LatticeProb.Analysis.KernelPowerBridge
import LatticeProb.Analysis.PoissonProfile

/-!
# The unit-scale on-diagonal estimate

The cited discrete-time estimate gives the even diagonal bound. Cauchy–Schwarz and
Poisson averaging transfer it to the continuous-time Euclidean unit-rate walk.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Graph.LongRangeKernel
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- Taking an integer half changes the logarithmic profile base by a bounded factor. -/
private theorem logarithmic_base_half (n m : ℕ) (hn : n ≤ 2 * m + 1) :
    1 + (n : ℝ) * Real.log (2 + n) ≤
      6 * (1 + (m : ℝ) * Real.log (2 + m)) := by
  have hnR : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hm0 : m = 0
  · subst m
    have hn1 : (n : ℝ) ≤ 1 := by simpa using hnR
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < (2 : ℝ) + n)
    have hp := mul_le_mul_of_nonneg_left hl hn0
    norm_num only [Nat.cast_zero, add_zero, zero_mul] at *
    nlinarith
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    have hl0 : 0 ≤ Real.log (2 + (m : ℝ)) := Real.log_nonneg (by linarith)
    have hsq : 2 + (n : ℝ) ≤ (2 + (m : ℝ)) ^ 2 := by nlinarith
    have hl : Real.log (2 + (n : ℝ)) ≤ 2 * Real.log (2 + (m : ℝ)) := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using
        Real.log_le_log (by positivity : 0 < (2 : ℝ) + n) hsq
    have hn3 : (n : ℝ) ≤ 3 * m := by linarith
    have hp := mul_le_mul hn3 hl (Real.log_nonneg (by linarith)) (by positivity)
    nlinarith

/-- A bounded ratio of logarithmic bases gives the corresponding decay bound. -/
private theorem logarithmic_profile_half (n m : ℕ) (hn : n ≤ 2 * m + 1) :
    (1 + (m : ℝ) * Real.log (2 + m)) ^ (-((d : ℝ) / 2)) ≤
      (6 : ℝ) ^ ((d : ℝ) / 2) *
        (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
  have hm : 0 ≤ (m : ℝ) * Real.log (2 + m) :=
    mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  have hn0 : 0 ≤ (n : ℝ) * Real.log (2 + n) :=
    mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have h := Real.rpow_le_rpow_of_nonpos (by linarith :
    0 < 1 + (n : ℝ) * Real.log (2 + n)) (logarithmic_base_half n m hn)
    (neg_nonpos.mpr (by positivity) : -((d : ℝ) / 2) ≤ 0)
  have hh := mul_le_mul_of_nonneg_left h
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) ((d : ℝ) / 2))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by linarith),
    ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6),
    add_neg_cancel, Real.rpow_zero, one_mul] at hh
  exact hh

/-- The cited MSC estimate and the lattice lower Gaussian bound give unit heat decay. -/
theorem unitHeat_onDiagonal (hMSC : LatticeProb.External.MuruganSaloffCoste) (hd : 1 ≤ d)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
        Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
          (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x y : Site d),
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) := by
  let rates := unitRates hd hlam a ha
  have hR : 0 < rates.R := rates.R_pos
  have hmass : (weightedLattice d hd).mass = fun _ => 1 :=
    funext (weightedLattice_mass hd)
  have hmark : IsMarkovDensity (weightedLattice d hd).mass
      (fun x y => ENNReal.ofReal (rates.p x y)) := by
    rw [hmass]
    exact unitRates_isMarkovDensity hd hlam a ha
  have hprofile : ∃ C : ℝ, 0 < C ∧ ∀ x y,
    ENNReal.ofReal (C⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
      quadraticScale ((lattice d).dist x y))) ≤ ENNReal.ofReal (rates.p x y) ∧
    ENNReal.ofReal (rates.p x y) ≤ ENNReal.ofReal
      (C / (latticeVolumeProfile d ((lattice d).dist x y) *
        quadraticScale ((lattice d).dist x y))) := by
    simpa only [lattice_dist_eq_graphNorm hd] using unitRates_density_profile hd hlam a ha
  obtain ⟨C, hC, hbound⟩ := hMSC (Site d) (weightedLattice d hd)
    (weightedLattice_infinite hd) (weightedLattice_connected hd)
    (latticeVolumeProfile d) quadraticScale 2 (fun x y => ENNReal.ofReal (rates.p x y))
    (weightedLattice_counting hd) (latticeVolumeProfile_isVolumeProfile hd)
    (weightedLattice_volume_comparable hd) (weightedLattice_edge_lower hd) (by norm_num)
    (weightedLattice_gaussian_upper hd) hlow quadraticScale_isJumpScale hmark
    (unitRates_density_symm hd hlam a ha) hprofile criticalInverse
    criticalInverse_isInverseScale
  obtain ⟨c, _, hc, _, hv⟩ := latticeVolume_criticalInverse_comparison d
  have heven (n : ℕ) (x : Site d) : kernelPow rates.p (2 * n) x x ≤
      (C / c) * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
    have hb := (le_iSup (fun z => densityPower (weightedLattice d hd).mass
      (fun u v => ENNReal.ofReal (rates.p u v)) (2 * n) z z) x).trans (hbound n).2
    rw [hmass, densityPower_one_eq _ _ rates.p_nonneg rates.hasSum_p] at hb
    have hvn := (hv n (Nat.cast_nonneg n)).1
    have hlog : 0 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hp : 0 < (1 + (n : ℝ) * Real.log (2 + n)) ^ ((d : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hV : 0 < latticeVolumeProfile d (criticalInverse n) :=
      (mul_pos hc hp).trans_le hvn
    have hr := (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC.le hV.le)).mp hb
    calc
      _ ≤ C / latticeVolumeProfile d (criticalInverse n) := hr
      _ ≤ C / (c * (1 + (n : ℝ) * Real.log (2 + n)) ^ ((d : ℝ) / 2)) :=
        div_le_div_of_nonneg_left hC.le (mul_pos hc hp) hvn
      _ = _ := by rw [Real.rpow_neg (by positivity)]; ring
  let D := C / c * (6 : ℝ) ^ ((d : ℝ) / 2)
  have hD : 0 < D := mul_pos (div_pos hC hc) (Real.rpow_pos_of_pos (by norm_num) _)
  have hall (n : ℕ) (x y : Site d) : kernelPow rates.p n x y ≤
      D * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
    have hhalf (m : ℕ) (hm : n ≤ 2 * m + 1) (z : Site d) :
        kernelPow rates.p (2 * m) z z ≤
          D * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
      exact (heven m z).trans (by
        simpa only [D, mul_assoc] using mul_le_mul_of_nonneg_left
          (logarithmic_profile_half (d := d) n m hm) (div_pos hC hc).le)
    have hb := kernelPow_le_sqrt_diag_half rates.p_nonneg rates.hasSum_p
      (unitRates_p_symm hd hlam a ha) n x y
    have hlog : 0 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have h0 : 0 ≤ D *
        (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) :=
      mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
    calc
      _ ≤ _ := hb
      _ ≤ Real.sqrt (D * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2))) *
          Real.sqrt (D * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2))) :=
        mul_le_mul (Real.sqrt_le_sqrt (hhalf (n / 2) (by omega) x))
          (Real.sqrt_le_sqrt (hhalf ((n + 1) / 2) (by omega) y))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt h0
  obtain ⟨B, hB, hpoisson⟩ := poisson_average_profile_le d rates.R rates.R_pos
  refine ⟨D * B, mul_pos hD hB, ?_⟩
  intro t x y
  rw [rates.transitionKernel_real_singleton_eq_kernelPow]
  have hs := (poisson_profile_summable d (rates.R * t) (by positivity)).mul_left D
  have hs' : Summable (fun n : ℕ =>
      Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial *
        kernelPow rates.p n x y) := by
    apply hs.of_nonneg_of_le
    · intro n
      exact mul_nonneg (by positivity) (kernelPow_nonneg rates.p_nonneg n x y)
    · intro n
      simpa only [mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hall n x y)
          (by positivity : 0 ≤ Real.exp (-(rates.R * t)) *
            (rates.R * t) ^ n / n.factorial)
  calc
    _ ≤ ∑' n : ℕ, D * (Real.exp (-(rates.R * t)) *
        (rates.R * t) ^ n / n.factorial *
          (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2))) := by
      apply hs'.tsum_le_tsum _ hs
      intro n
      simpa only [mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hall n x y)
          (by positivity : 0 ≤ Real.exp (-(rates.R * t)) *
            (rates.R * t) ^ n / n.factorial)
    _ = D * ∑' n : ℕ, Real.exp (-(rates.R * t)) *
        (rates.R * t) ^ n / n.factorial *
          (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := tsum_mul_left
    _ ≤ D * (B * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left (hpoisson t t.coe_nonneg) hD.le
    _ = _ := by ring
end

end LongRange
