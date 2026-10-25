import LongRange.HeatKernel.UnitWalk
import LatticeProb.Prob.JumpChain.TimeScale
import LatticeProb.Prob.JumpChain.PositionLaw
import LongRange.Appendix.Kappa

/-!
# Displacement tails from the off-diagonal heat kernel

Euclidean exterior sums control the logarithmically weighted unit kernel. Time scaling
then transfers estimates for the unit walk to the critically normalized walk.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open MeasureTheory
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- Scaling all rates identifies the physical walk with the unit walk at a faster clock. -/
theorem walk_transitionKernel_eq_timeScale (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (t : ℝ≥0) :
    (walkRates hd hε.1 hlam a ha).transitionKernel t =
      (unitRates hd hlam a ha).transitionKernel
        (⟨1 / (kappa d ε * ε ^ 2),
          (one_div_pos.mpr (mul_pos (kappa_pos hd hε) (pow_pos hε.1 _))).le⟩ * t) := by
  have hk := kappa_pos hd hε
  apply JumpChain.BoundedRates.transitionKernel_eq_timeScale
  · exact one_div_pos.mpr (mul_pos hk (pow_pos hε.1 _))
  · intro x y
    change walkRate ε a x y = _ * unitRate a x y
    rw [walkRate_eq_smul_unitRate hε.1, pow_add]
    congr 1
    field_simp [hε.1.ne', hk.ne']

/-- The exterior Euclidean power sum has the expected inverse-power decay. -/
theorem exterior_power_finset_le (hd : 1 ≤ d) {n : ℕ} (hn : 0 < n)
    {R : ℝ} (hR : 1 ≤ R) (u : Finset (Site d))
    (hu : ∀ w ∈ u, R ≤ radius (physical 1 w)) :
    ∑ w ∈ u, 1 / radius (physical 1 w) ^ (d + n) ≤
      (Euclidean.Shell.shellConstant d * ((1 + 1 / (n : ℝ)) * (4 : ℝ) ^ n)) /
        R ^ n := by
  classical
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hε : 0 < 1 / R := one_div_pos.mpr hR0
  have hα : (d : ℝ) < ((d + n : ℕ) : ℝ) := by exact_mod_cast Nat.lt_add_of_pos_right hn
  have hb := Euclidean.Estimates.exterior_finset_le hd hα hε
    (by simpa only [one_div_one_div] using hR) u
  have he : ((d + n : ℕ) : ℝ) - d = n := by push_cast; ring
  rw [he] at hb
  have hterm (w : Site d) (hw : w ∈ u) :
      (if 1 ≤ radius (physical (1 / R) w) then
        radius (physical (1 / R) w) ^ (-((d + n : ℕ) : ℝ)) else 0) =
        R ^ (d + n) * (1 / radius (physical 1 w) ^ (d + n)) := by
    have hr : 1 ≤ radius (physical (1 / R) w) := by
      rw [radius_physical_eq_mul hε.le]
      exact (one_le_div hR0).mpr (hu w hw) |>.trans_eq (by ring)
    rw [if_pos hr, radius_physical_eq_mul hε.le,
      Real.mul_rpow hε.le (radius_nonneg _), Real.rpow_neg hε.le,
      Real.rpow_natCast, Real.rpow_neg (radius_nonneg _), Real.rpow_natCast]
    simp only [one_div, inv_pow, inv_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hb
  rw [Real.rpow_neg hε.le, Real.rpow_natCast] at hb
  simp only [one_div, inv_pow, inv_inv, Real.rpow_natCast] at hb
  rw [Real.rpow_neg hR0.le, Real.rpow_natCast] at hb
  have hp : 0 < R ^ (d + n) := pow_pos hR0 _
  apply (mul_le_mul_iff_right₀ hp).mp
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hb

/-- Above a positive cutoff, the logarithm grows at most linearly in the radius ratio. -/
theorem log_radius_le_log_cutoff {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    Real.log (2 + r) ≤ Real.log (2 + R) + r / R := by
  have hr0 : 0 < r := hR.trans_le hr
  have hratio : 1 ≤ r / R := (one_le_div hR).mpr hr
  have hcomp : 2 + r ≤ (2 + R) * (r / R) := by
    have heq : R * (r / R) = r := mul_div_cancel₀ _ hR.ne'
    nlinarith only [hratio, heq]
  calc
    Real.log (2 + r) ≤ Real.log ((2 + R) * (r / R)) :=
      Real.log_le_log (by linarith) hcomp
    _ = Real.log (2 + R) + Real.log (r / R) :=
      Real.log_mul (by positivity) (div_pos hr0 hR).ne'
    _ ≤ Real.log (2 + R) + r / R :=
      add_le_add_right (Real.log_le_self (div_nonneg hr0.le hR.le)) _

/-- Finite logarithmically weighted exterior sums have inverse-square decay. -/
theorem exterior_log_finset_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ u : Finset (Site d),
      (∀ w ∈ u, R ≤ radius (physical 1 w)) →
      ∑ w ∈ u, Real.log (2 + radius (physical 1 w)) /
          radius (physical 1 w) ^ (d + 2) ≤ C * (1 + Real.log (2 + R)) / R ^ 2 := by
  let A := Euclidean.Shell.shellConstant d * 24
  let B := Euclidean.Shell.shellConstant d * 8
  have hA : 0 < A := mul_pos (Euclidean.Shell.shellConstant_pos hd) (by norm_num)
  have hB : 0 < B := mul_pos (Euclidean.Shell.shellConstant_pos hd) (by norm_num)
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro R hR u hu
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have ha := exterior_power_finset_le hd (n := 2) (by omega) hR u hu
  have hb := exterior_power_finset_le hd (n := 1) (by omega) hR u hu
  norm_num at ha hb
  change _ ≤ A / R ^ 2 at ha
  change _ ≤ B / R at hb
  replace ha : (∑ w ∈ u, 1 / radius (physical 1 w) ^ (d + 2)) ≤ A / R ^ 2 := by
    simpa only [one_div] using ha
  replace hb : (∑ w ∈ u, 1 / radius (physical 1 w) ^ (d + 1)) ≤ B / R := by
    simpa only [one_div] using hb
  have hterm (w : Site d) (hw : w ∈ u) :
      Real.log (2 + radius (physical 1 w)) / radius (physical 1 w) ^ (d + 2) ≤
      Real.log (2 + R) * (1 / radius (physical 1 w) ^ (d + 2)) +
        (1 / R) * (1 / radius (physical 1 w) ^ (d + 1)) := by
    have hr := hR0.trans_le (hu w hw)
    have hl := log_radius_le_log_cutoff hR0 (hu w hw)
    calc
      _ ≤ (Real.log (2 + R) + radius (physical 1 w) / R) /
          radius (physical 1 w) ^ (d + 2) :=
        div_le_div_of_nonneg_right hl (pow_nonneg hr.le _)
      _ = _ := by
        rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
        field_simp [hr.ne', hR0.ne']
  calc
    _ ≤ ∑ w ∈ u, (Real.log (2 + R) * (1 / radius (physical 1 w) ^ (d + 2)) +
        (1 / R) * (1 / radius (physical 1 w) ^ (d + 1))) := Finset.sum_le_sum hterm
    _ = Real.log (2 + R) * (∑ w ∈ u, 1 / radius (physical 1 w) ^ (d + 2)) +
        (1 / R) * (∑ w ∈ u, 1 / radius (physical 1 w) ^ (d + 1)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ Real.log (2 + R) * (A / R ^ 2) + (1 / R) * (B / R) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hlog)
        (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = (Real.log (2 + R) * A + B) / R ^ 2 := by
      field_simp [hR0.ne']
    _ ≤ (A + B) * (1 + Real.log (2 + R)) / R ^ 2 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hR0.le _)
      have hh := mul_nonneg hB.le hlog
      nlinarith only [hA, hB, hh]

/-- An off-diagonal estimate sums over any set separated from its initial site. -/
theorem unit_transition_tail_of_offDiagonal (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hB2 : ∀ (t : ℝ≥0) (x y : Site d), x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C₀ * t * Real.log (2 + radius (physical 1 (y - x))) /
          radius (physical 1 (y - x)) ^ (d + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Site d) (R : ℝ), 1 ≤ R →
      ∀ S : Set (Site d), (∀ y ∈ S, R ≤ radius (physical 1 (y - x))) →
      (unitRates hd hlam a ha).transitionKernel t x S ≤
        ENNReal.ofReal (C * t * (1 + Real.log (2 + R)) / R ^ 2) := by
  classical
  obtain ⟨A, hA, hbound⟩ := exterior_log_finset_le hd
  refine ⟨(C₀ + 1) * A, mul_pos (by linarith) hA, ?_⟩
  intro t x R hR S hS
  let μ := (unitRates hd hlam a ha).transitionKernel t x
  rw [← Measure.tsum_indicator_apply_singleton μ S S.to_countable.measurableSet]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro u
  let v := u.filter (fun y => y ∈ S)
  have hv (y : Site d) (hy : y ∈ v) : R ≤ radius (physical 1 (y - x)) :=
    hS y (Finset.mem_filter.mp hy).2
  have hne (y : Site d) (hy : y ∈ v) : x ≠ y := by
    intro h
    have hr := hv y hy
    rw [← h, sub_self] at hr
    norm_num [physical, radius] at hr
    linarith
  have hs : (∑ y ∈ u, S.indicator (fun y => μ {y}) y) =
      ∑ y ∈ v, ENNReal.ofReal (μ.real {y}) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, if_pos hy, MeasureTheory.ofReal_measureReal]
    · rw [Set.indicator_of_notMem hy, if_neg hy]
  rw [hs, ← ENNReal.ofReal_sum_of_nonneg
    (fun y _ => measureReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  have hsum := Finset.sum_le_sum (fun y hy => hB2 t x y (hne y hy))
  change (∑ y ∈ v, μ.real {y}) ≤ _ at hsum
  have himage : (∑ y ∈ v, Real.log (2 + radius (physical 1 (y - x))) /
      radius (physical 1 (y - x)) ^ (d + 2)) =
      ∑ w ∈ v.image (fun y => y - x), Real.log (2 + radius (physical 1 w)) /
        radius (physical 1 w) ^ (d + 2) := by
    rw [Finset.sum_image (fun y _ z _ h => sub_left_injective h)]
  have hlog := hbound R hR (v.image (fun y => y - x)) (by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact hv y hy)
  have hnon : 0 ≤ (t : ℝ) * (1 + Real.log (2 + R)) / R ^ 2 := by
    have hl := Real.log_nonneg (show 1 ≤ 2 + R by linarith)
    positivity
  calc
    _ ≤ ∑ y ∈ v, C₀ * t * Real.log (2 + radius (physical 1 (y - x))) /
        radius (physical 1 (y - x)) ^ (d + 2) := hsum
    _ = (C₀ * t) * (∑ y ∈ v, Real.log (2 + radius (physical 1 (y - x))) /
        radius (physical 1 (y - x)) ^ (d + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ (C₀ * t) * (A * (1 + Real.log (2 + R)) / R ^ 2) := by
      rw [himage]
      exact mul_le_mul_of_nonneg_left hlog (mul_nonneg hC₀ t.coe_nonneg)
    _ ≤ (C₀ + 1) * A * t * (1 + Real.log (2 + R)) / R ^ 2 := by
      have h := mul_nonneg hA.le hnon
      calc
        _ = C₀ * (A * ((t : ℝ) * (1 + Real.log (2 + R)) / R ^ 2)) := by ring
        _ ≤ (C₀ + 1) * (A * ((t : ℝ) * (1 + Real.log (2 + R)) / R ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) h
        _ = _ := by ring

/-- The logarithm at the integer cutoff is controlled by the normalization logarithm. -/
theorem log_max_cutoff_le {ε η : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 < η) :
    1 + Real.log (2 + max 1 (η / ε)) ≤
      4 * (1 + Real.log (2 + η)) * (1 + |Real.log ε|) := by
  have hηlog : 0 ≤ Real.log (2 + η) := Real.log_nonneg (by linarith)
  have hεlog : Real.log ε ≤ 0 := Real.log_nonpos hε.1.le hε.2.le
  have hmax : max 1 (η / ε) ≤ (2 + η) / ε := by
    apply max_le
    · exact (le_div_iff₀ hε.1).mpr (by linarith [hε.2])
    · exact div_le_div_of_nonneg_right (by linarith) hε.1.le
  have hbase : 2 + max 1 (η / ε) ≤ 3 * (2 + η) / ε := by
    have hlarge : 1 ≤ (2 + η) / ε :=
      (le_div_iff₀ hε.1).mpr (by linarith [hε.2])
    calc
      _ ≤ 2 + (2 + η) / ε := add_le_add_right hmax 2
      _ ≤ 3 * ((2 + η) / ε) := by linarith only [hlarge]
      _ = _ := by ring
  have hlog := Real.log_le_log (show 0 < 2 + max 1 (η / ε) by
    have := le_max_left (1 : ℝ) (η / ε)
    linarith) hbase
  rw [Real.log_div (by positivity : 3 * (2 + η) ≠ 0) hε.1.ne',
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by linarith : 2 + η ≠ 0)] at hlog
  have hthree : Real.log 3 ≤ 3 := Real.log_le_self (by norm_num)
  rw [abs_of_nonpos hεlog]
  have hprod := mul_nonneg hηlog (neg_nonneg.mpr hεlog)
  nlinarith only [hlog, hthree, hηlog, hεlog, hprod]

/-- The off-diagonal unit bound gives the physical displacement tail uniformly in the scale. -/
theorem displacement_tail_of_offDiagonal (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C₀ : ℝ}
    (hB2 : ∀ (t : ℝ≥0) (x y : Site d), x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C₀ * t * Real.log (2 + radius (physical 1 (y - x))) /
          radius (physical 1 (y - x)) ^ (d + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (t : ℝ≥0) (x : Site d) (η : ℝ), 0 < η →
      ((walkRates hd hε.1 hlam a ha).transitionKernel t x)
          {y | η < radius (physical ε y - physical ε x)} ≤
        ENNReal.ofReal (C * t * (1 + Real.log (2 + η)) / η ^ 2) := by
  have hB2' (t : ℝ≥0) (x y : Site d) (hxy : x ≠ y) :
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        max C₀ 0 * t * Real.log (2 + radius (physical 1 (y - x))) /
          radius (physical 1 (y - x)) ^ (d + 2) := by
    apply (hB2 t x y hxy).trans
    have hl : 0 ≤ Real.log (2 + radius (physical 1 (y - x))) :=
      Real.log_nonneg (by linarith [radius_nonneg (physical 1 (y - x))])
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) t.coe_nonneg) hl)
      (pow_nonneg (radius_nonneg _) _)
  obtain ⟨A, hA, hb⟩ := unit_transition_tail_of_offDiagonal hd hlam a ha
    (le_max_right C₀ 0) hB2'
  obtain ⟨c, hc, hk⟩ := le_kappa hd
  refine ⟨4 * A / c, div_pos (mul_pos (by norm_num) hA) hc, ?_⟩
  intro ε hε t x η hη
  let R := max 1 (η / ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hk0 := kappa_pos hd hε
  let clock : ℝ≥0 := ⟨1 / (kappa d ε * ε ^ 2),
    (one_div_pos.mpr (mul_pos hk0 (pow_pos hε.1 _))).le⟩
  rw [walk_transitionKernel_eq_timeScale hd hε hlam a ha t]
  have hsep (y : Site d)
      (hy : η < radius (physical ε y - physical ε x)) :
      R ≤ radius (physical 1 (y - x)) := by
    have hphys : physical ε y - physical ε x = physical ε (y - x) := by
      ext i
      simp only [physical, Pi.sub_apply, Int.cast_sub]
      ring
    rw [hphys, radius_physical_eq_mul hε.1.le] at hy
    have hxy : y - x ≠ 0 := by
      intro hz
      rw [hz] at hy
      norm_num [physical, radius] at hy
      linarith
    exact max_le (lattice_radius_ge_one hxy)
      ((div_lt_iff₀ hε.1).mpr (by simpa only [mul_comm] using hy)).le
  apply (hb (clock * t) x R hR _ hsep).trans
  apply ENNReal.ofReal_le_ofReal
  have hlog := log_max_cutoff_le hε hη
  change 1 + Real.log (2 + R) ≤ _ at hlog
  have hnorm := hk ε hε
  have hL : 0 ≤ 1 + Real.log (2 + η) := by
    have := Real.log_nonneg (show 1 ≤ 2 + η by linarith)
    linarith
  have hscale : η ^ 2 ≤ ε ^ 2 * R ^ 2 := by
    have h := (div_le_iff₀ hε.1).mp (le_max_right (1 : ℝ) (η / ε))
    have hs := pow_le_pow_left₀ hη.le h 2
    simpa only [mul_pow, mul_comm] using hs
  change A * ((1 / (kappa d ε * ε ^ 2)) * (t : ℝ)) *
      (1 + Real.log (2 + R)) / R ^ 2 ≤ _
  have hquot : (1 + Real.log (2 + R)) / kappa d ε ≤
      4 * (1 + Real.log (2 + η)) / c := by
    apply (div_le_div_iff₀ hk0 hc).mpr
    calc
      (1 + Real.log (2 + R)) * c ≤
          (4 * (1 + Real.log (2 + η)) * (1 + |Real.log ε|)) * c :=
        mul_le_mul_of_nonneg_right hlog hc.le
      _ = 4 * (1 + Real.log (2 + η)) * (c * (1 + |Real.log ε|)) := by ring
      _ ≤ 4 * (1 + Real.log (2 + η)) * kappa d ε :=
        mul_le_mul_of_nonneg_left hnorm (mul_nonneg (by norm_num) hL)
  calc
    _ = A * t * ((1 + Real.log (2 + R)) / kappa d ε) / (ε ^ 2 * R ^ 2) := by ring
    _ ≤ A * t * (4 * (1 + Real.log (2 + η)) / c) / (ε ^ 2 * R ^ 2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquot (mul_nonneg hA.le t.coe_nonneg))
        (by positivity)
    _ ≤ A * t * (4 * (1 + Real.log (2 + η)) / c) / η ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hη 2) hscale
    _ = _ := by ring

end

end LongRange
