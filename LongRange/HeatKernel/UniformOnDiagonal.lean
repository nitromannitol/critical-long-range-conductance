import LongRange.HeatKernel.UnitWalk
import LatticeProb.External.MuruganSaloffCosteUniform
import LatticeProb.Graph.LongRangeKernel.CriticalVolume
import LatticeProb.Analysis.KernelPowerBridge
import LatticeProb.Analysis.PoissonProfile

/-!
# A field-uniform on-diagonal heat-kernel bound

The unit clock and jump comparison depend only on dimension and ellipticity.
The uniform cited estimate, Cauchy–Schwarz and Poisson averaging therefore give
one continuous-time bound for every admissible conductance field.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Graph.LongRangeKernel
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- One polynomial jump comparison constant works for every admissible field. -/
theorem unitRates_density_profile_uniform (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ x y,
      ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d (graphNorm (y - x)) * quadraticScale (graphNorm (y - x)))) ≤
        ENNReal.ofReal ((unitRates hd hlam a ha).p x y) ∧
      ENNReal.ofReal ((unitRates hd hlam a ha).p x y) ≤
        ENNReal.ofReal (C /
          (latticeVolumeProfile d (graphNorm (y - x)) *
            quadraticScale (graphNorm (y - x)))) := by
  classical
  let R := 2 * (lam⁻¹ * ∑' w : Site d, jumpKernel (physical 1 w))
  let B := (2 * (d : ℝ)) ^ (d + 2)
  let C := max 2 (max (R / lam) (lam⁻¹ * B / R))
  have hR : 0 < R :=
    mul_pos (by norm_num) (mul_pos (inv_pos.mpr hlam) (unitKernel_tsum_pos hd))
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCl : R / lam ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCu : lam⁻¹ * B / R ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hlow : C⁻¹ ≤ lam / R := by
    rw [← one_div, div_le_div_iff₀ hC hR]
    have ht := (div_le_iff₀ hlam).mp hCl
    nlinarith only [ht]
  refine ⟨C, hC, ?_⟩
  intro a ha x y
  apply And.intro <;> apply ENNReal.ofReal_le_ofReal
  · by_cases h : y = x
    · subst y
      simp only [sub_self, graphNorm_zero, Nat.cast_zero, latticeVolumeProfile,
        quadraticScale, add_zero, one_pow, mul_one, div_one]
      have hi : C⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hC (by norm_num)).mpr hC2
      exact hi.trans (by simpa only [inv_eq_one_div] using
        unitRates_p_self_ge_half hd hlam a ha x)
    · have hw : y - x ≠ 0 := sub_ne_zero.mpr h
      have hk := (unitKernel_profile_bound hd hw).1
      have hD : 0 ≤ latticeVolumeProfile d (graphNorm (y - x)) *
          quadraticScale (graphNorm (y - x)) := by
        unfold latticeVolumeProfile quadraticScale
        positivity
      rw [JumpChain.BoundedRates.p, if_neg h]
      change _ ≤ unitRate a x y / R
      rw [unitRate, dif_neg hw]
      calc
        _ ≤ (lam / R) / _ := div_le_div_of_nonneg_right hlow hD
        _ = lam * (1 / (latticeVolumeProfile d (graphNorm (y - x)) *
            quadraticScale (graphNorm (y - x)))) / R := by ring
        _ ≤ a (edgeAdd x (y - x) hw) * jumpKernel (physical 1 (y - x)) / R := by
          apply div_le_div_of_nonneg_right _ hR.le
          exact mul_le_mul (ha _).1 hk (by positivity) (hlam.le.trans (ha _).1)
  · by_cases h : y = x
    · subst y
      simp only [sub_self, graphNorm_zero, Nat.cast_zero, latticeVolumeProfile,
        quadraticScale, add_zero, one_pow, mul_one, div_one]
      rw [JumpChain.BoundedRates.p, if_pos rfl]
      have ht : 0 ≤ (∑' k, (unitRates hd hlam a ha).q x k) /
          (unitRates hd hlam a ha).R :=
        div_nonneg (tsum_nonneg ((unitRates hd hlam a ha).q_nonneg x)) hR.le
      linarith only [ht, hC2]
    · have hw : y - x ≠ 0 := sub_ne_zero.mpr h
      have hk := (unitKernel_profile_bound hd hw).2
      have hD : 0 ≤ latticeVolumeProfile d (graphNorm (y - x)) *
          quadraticScale (graphNorm (y - x)) := by
        unfold latticeVolumeProfile quadraticScale
        positivity
      rw [JumpChain.BoundedRates.p, if_neg h]
      change unitRate a x y / R ≤ _
      rw [unitRate, dif_neg hw]
      calc
        _ ≤ (lam⁻¹ * (B / (latticeVolumeProfile d (graphNorm (y - x)) *
            quadraticScale (graphNorm (y - x))))) / R := by
          apply div_le_div_of_nonneg_right _ hR.le
          exact mul_le_mul (ha _).2 hk (jumpKernel_nonneg _) (inv_nonneg.mpr hlam.le)
        _ = (lam⁻¹ * B / R) / _ := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hCu hD

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

/-- The unit-scale heat bound has one constant for all admissible conductance fields. -/
theorem unitHeat_onDiagonal_uniform
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (d : ℕ) (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
      ∀ (t : ℝ≥0) (x y : Site d),
        ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
          C * (1 + t * Real.log (2+t)) ^ (-((d:ℝ)/2)) := by
  let R := 2 * (lam⁻¹ * ∑' w : Site d, jumpKernel (physical 1 w))
  have hR : 0 < R :=
    mul_pos (by norm_num) (mul_pos (inv_pos.mpr hlam) (unitKernel_tsum_pos hd))
  obtain ⟨Cφ, hCφ, hprofile⟩ := unitRates_density_profile_uniform hd hlam
  obtain ⟨C, hC, hbound⟩ :=
    External.lattice_uniform_estimate hMSC hd Cφ hCφ
  obtain ⟨c, _, hc, _, hv⟩ := latticeVolume_criticalInverse_comparison d
  let D := C / c * (6 : ℝ) ^ ((d : ℝ) / 2)
  have hD : 0 < D := mul_pos (div_pos hC hc) (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨B, hB, hpoisson⟩ := poisson_average_profile_le d R hR
  refine ⟨D * B, mul_pos hD hB, ?_⟩
  intro a ha
  let rates := unitRates hd hlam a ha
  have hmass : (weightedLattice d hd).mass = fun _ => 1 :=
    funext (weightedLattice_mass hd)
  have hmark : IsMarkovDensity (weightedLattice d hd).mass
      (fun x y => ENNReal.ofReal (rates.p x y)) := by
    rw [hmass]
    exact unitRates_isMarkovDensity hd hlam a ha
  have hprofile' : ∀ x y,
      ENNReal.ofReal (Cφ⁻¹ / (latticeVolumeProfile d ((lattice d).dist x y) *
        quadraticScale ((lattice d).dist x y))) ≤ ENNReal.ofReal (rates.p x y) ∧
      ENNReal.ofReal (rates.p x y) ≤ ENNReal.ofReal
        (Cφ / (latticeVolumeProfile d ((lattice d).dist x y) *
          quadraticScale ((lattice d).dist x y))) := by
    simpa only [lattice_dist_eq_graphNorm hd] using hprofile a ha
  have hbound' := hbound (fun x y => ENNReal.ofReal (rates.p x y)) hmark
    (unitRates_density_symm hd hlam a ha) hprofile'
  have heven (n : ℕ) (x : Site d) : kernelPow rates.p (2 * n) x x ≤
      (C / c) * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
    have hb := (le_iSup (fun z => densityPower (weightedLattice d hd).mass
      (fun u v => ENNReal.ofReal (rates.p u v)) (2 * n) z z) x).trans (hbound' n).2
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

/-- The constant-one conductances in dimension one satisfy the uniform heat bound. -/
theorem unitHeat_onDiagonal_one
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x y : Site 1),
      ((unitRates (by norm_num : 1 ≤ 1) (by norm_num : (0 : ℝ) < 1)
        (fun _ : Edge 1 => (1 : ℝ)) (by intro _; norm_num)).transitionKernel t x).real {y} ≤
          C * (1 + t * Real.log (2 + t)) ^ (-(1 / (2 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := unitHeat_onDiagonal_uniform hMSC 1 (by norm_num)
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, hC, ?_⟩
  intro t x y
  simpa only [Nat.cast_one] using
    hbound (fun _ : Edge 1 => (1 : ℝ)) (by intro _; norm_num) t x y

end

end LongRange
