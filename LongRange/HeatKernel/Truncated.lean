import LongRange.HeatKernel.Tent
import LongRange.HeatKernel.OnDiagonal
import LatticeProb.Prob.JumpChain.Truncation
import LatticeProb.Prob.JumpChain.Duhamel

/-!
# Bounds for the truncated unit walk

Euclidean tail estimates control the intensity removed by truncation. Uniformization
then gives additive and exponential comparisons with the unit walk.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Graph.LongRangeKernel
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- Each removed rate is bounded by the kernel at the larger of one and the cutoff. -/
theorem removed_rate_le (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ : ℝ} (_hρ : 0 < ρ) (x y : Site d) :
    unitRate a x y - (truncRates hd hlam a ha ρ).q x y ≤
      lam⁻¹ * max 1 ρ ^ (-((d : ℝ) + 2)) := by
  classical
  change unitRate a x y -
    (if radius (physical 1 (y - x)) ≤ ρ then unitRate a x y else 0) ≤ _
  split_ifs with ht
  · rw [sub_self]
    positivity
  · rw [sub_zero]
    by_cases hn : y - x = 0
    · simp only [unitRate, hn, dite_true]
      positivity
    have hr := lattice_radius_ge_one hn
    have hp : 0 < radius (physical 1 (y - x)) := zero_lt_one.trans_le hr
    have hb := unitRate_le hlam ha x y
    rw [jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one _).not.mpr hn)] at hb
    have he : (radius (physical 1 (y - x)) ^ (d + 2))⁻¹ =
        radius (physical 1 (y - x)) ^ (-((d : ℝ) + 2)) := by
      rw [Real.rpow_neg hp.le,
        show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_natCast]
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left 1 ρ))
        (max_le hr (le_of_not_ge ht))
        (by linarith [Nat.cast_nonneg (α := ℝ) d])) (inv_nonneg.mpr hlam.le))

/-- The Euclidean exterior kernel has a quadratic tail, uniformly in the cutoff. -/
lemma exterior_unit_kernel_le (hd : 1 ≤ d) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∑' z : Site d, (if ρ < radius (physical 1 z) then
      jumpKernel (physical 1 z) else 0) ≤
        (Euclidean.Shell.shellConstant d * 24) * ρ ^ (-(2 : ℝ)) := by
  classical
  have hp : 0 < ρ := zero_lt_one.trans_le hρ
  let f := fun z : Site d => if ρ < radius (physical 1 z) then
    jumpKernel (physical 1 z) else 0
  have hn : ∀ z, 0 ≤ f z := by
    intro z
    exact ite_nonneg (jumpKernel_nonneg _) le_rfl
  have hb (u : Finset (Site d)) :
      ∑ z ∈ u, f z ≤ (Euclidean.Shell.shellConstant d * 24) *
        ρ ^ (-(2 : ℝ)) := by
    have h := Euclidean.Estimates.exterior_finset_le hd
      (α := (d : ℝ) + 2) (by linarith) (inv_pos.mpr hp)
      (by simpa only [one_div, inv_inv] using hρ) u
    have hsub : (d : ℝ) + 2 - d = 2 := by ring
    rw [hsub] at h
    have ht (z : Site d) : f z ≤ (ρ ^ (d + 2))⁻¹ *
        (if 1 ≤ radius (physical ρ⁻¹ z) then
          radius (physical ρ⁻¹ z) ^ (-((d : ℝ) + 2)) else 0) := by
      dsimp [f]
      split_ifs with hz hs hs
      · have hr : 0 < radius (physical 1 z) := hp.trans hz
        rw [jumpKernel_of_ne_zero (ne_of_apply_ne radius (by
          simpa only [radius, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero] using hr.ne')),
          radius_physical_eq_mul (inv_nonneg.mpr hp.le),
          Real.mul_rpow (inv_nonneg.mpr hp.le) (radius_nonneg _),
          Real.rpow_neg (inv_nonneg.mpr hp.le), Real.inv_rpow hp.le,
          inv_inv, show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl,
          Real.rpow_natCast, Real.rpow_neg hr.le, Real.rpow_natCast]
        field_simp
        rfl
      · exfalso
        apply hs
        rw [radius_physical_eq_mul (inv_nonneg.mpr hp.le)]
        exact (one_le_inv_mul₀ hp).mpr hz.le
      · positivity
      · simp only [mul_zero, le_refl]
    calc
      _ ≤ (ρ ^ (d + 2))⁻¹ * ∑ z ∈ u,
          (if 1 ≤ radius (physical ρ⁻¹ z) then
            radius (physical ρ⁻¹ z) ^ (-((d : ℝ) + 2)) else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun z _ => ht z)
      _ ≤ (ρ ^ (d + 2))⁻¹ * (ρ⁻¹ ^ (-((d : ℝ) + 2)) *
          (Euclidean.Shell.shellConstant d * ((1 + 1 / (2 : ℝ)) *
            ((4 : ℝ) ^ (2 : ℝ) * (1 / ρ⁻¹) ^ (-(2 : ℝ)))))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by
        rw [Real.rpow_neg (inv_nonneg.mpr hp.le), Real.inv_rpow hp.le, inv_inv,
          show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl,
          Real.rpow_natCast]
        norm_num only [one_div, inv_inv, Real.rpow_two]
        field_simp [hp.ne']
        ring
  exact (summable_of_sum_le hn hb).tsum_le_of_sum_le hb

/-- The total removed intensity is bounded by a dimension and ellipticity constant. -/
theorem removed_intensity_le (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a : Edge d → ℝ)
      (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (ρ : ℝ), 1 ≤ ρ → ∀ x : Site d,
      (∑' y, (unitRates hd hlam a ha).q x y) -
        (∑' y, (truncRates hd hlam a ha ρ).q x y) ≤ B * ρ ^ (-(2 : ℝ)) := by
  classical
  refine ⟨lam⁻¹ * (Euclidean.Shell.shellConstant d * 24),
    mul_pos (inv_pos.mpr hlam)
      (mul_pos (Euclidean.Shell.shellConstant_pos hd) (by norm_num)), ?_⟩
  intro a ha ρ hρ x
  let f := fun z : Site d => if ρ < radius (physical 1 z) then
    jumpKernel (physical 1 z) else 0
  have hf : Summable f := (summable_jumpKernel hd zero_lt_one).of_nonneg_of_le
    (fun z => ite_nonneg (jumpKernel_nonneg _) le_rfl)
    (fun z => by dsimp [f]; split_ifs <;> simp only [le_refl, jumpKernel_nonneg])
  have hs : Summable (fun y => f (y - x)) := by
    exact (Equiv.subRight x).summable_iff.mpr hf
  rw [← (unitRates hd hlam a ha).summable x |>.tsum_sub
    ((truncRates hd hlam a ha ρ).summable x)]
  calc
    _ ≤ ∑' y, lam⁻¹ * f (y - x) := by
      apply ((unitRates hd hlam a ha).summable x |>.sub
        ((truncRates hd hlam a ha ρ).summable x)).tsum_le_tsum _ (hs.mul_left _)
      intro y
      change unitRate a x y -
        (if radius (physical 1 (y - x)) ≤ ρ then unitRate a x y else 0) ≤ _
      dsimp [f]
      by_cases ht : radius (physical 1 (y - x)) ≤ ρ
      · rw [if_pos ht, if_neg (not_lt.mpr ht), sub_self, mul_zero]
      · rw [if_neg ht, if_pos (lt_of_not_ge ht), sub_zero]
        exact unitRate_le hlam ha x y
    _ = lam⁻¹ * ∑' z, f z := by
      rw [tsum_mul_left]
      congr 1
      have he' := (Equiv.addLeft x).tsum_eq (fun y => f (y - x))
      simpa only [Equiv.coe_addLeft, add_sub_cancel_left] using he'.symm
    _ ≤ lam⁻¹ * ((Euclidean.Shell.shellConstant d * 24) * ρ ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (exterior_unit_kernel_le hd hρ) (inv_nonneg.mpr hlam.le)
    _ = _ := by ring

/-- Duhamel comparison loses at most the largest removed rate times elapsed time. -/
theorem unitHeat_le_trunc_add (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ≥0) (x y : Site d) :
    ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
      ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y} +
        lam⁻¹ * max 1 ρ ^ (-((d : ℝ) + 2)) * t := by
  have h := (unitRates hd hlam a ha).transitionKernel_singleton_le_add
    (truncRates hd hlam a ha ρ) rfl (truncRates_q_le hd hlam a ha ρ)
    (unitRate_symm a) (by positivity) (removed_rate_le hd hlam a ha hρ) t x y
  have ht := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top] at ht
  simpa only [MeasureTheory.measureReal_def,
    ENNReal.toReal_ofReal (by positivity :
      0 ≤ lam⁻¹ * max 1 ρ ^ (-((d : ℝ) + 2)) * (t : ℝ))] using ht

/-- Below lattice spacing all truncated rates vanish. -/
theorem truncRates_q_eq_zero_of_lt_one (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ : ℝ} (hρ : ρ < 1) (x y : Site d) :
    (truncRates hd hlam a ha ρ).q x y = 0 := by
  classical
  change (if radius (physical 1 (y - x)) ≤ ρ then unitRate a x y else 0) = 0
  by_cases hn : y - x = 0
  · simp only [unitRate, hn, dite_true, ite_self]
  · exact if_neg (not_le.mpr (hρ.trans_le (lattice_radius_ge_one hn)))

/-- Below lattice spacing the uniformized matrix is the identity. -/
theorem truncRates_p_of_lt_one (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ : ℝ} (hρ : ρ < 1) (x y : Site d) :
    (truncRates hd hlam a ha ρ).p x y = if y = x then 1 else 0 := by
  classical
  simp only [JumpChain.BoundedRates.p,
    truncRates_q_eq_zero_of_lt_one hd hlam a ha hρ, tsum_zero,
    zero_div, sub_zero]

/-- A truncated walk with cutoff below one cannot move between distinct sites. -/
theorem truncHeat_zero_of_lt_one (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ : ℝ} (_hρ : 0 < ρ) (hρ1 : ρ < 1) (t : ℝ≥0)
    (x y : Site d) (hxy : x ≠ y) :
    ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y} = 0 := by
  classical
  have hp (n : ℕ) (i j : Site d) :
      kernelPow (truncRates hd hlam a ha ρ).p n i j = if i = j then 1 else 0 := by
    induction n generalizing i j with
    | zero =>
      by_cases hij : i = j
      · simp only [kernelPow, if_pos hij]
      · simp only [kernelPow, if_neg hij]
    | succ n ih =>
      simp only [kernelPow, kernelComp, ih,
        truncRates_p_of_lt_one hd hlam a ha hρ1, ite_mul, one_mul, zero_mul,
        tsum_ite_eq', eq_comm]
  rw [JumpChain.BoundedRates.transitionKernel_real_singleton_eq_kernelPow]
  simp only [hp, if_neg hxy, mul_zero, tsum_zero]

/-- Positivity comparison transfers unit heat decay to the truncated walk. -/
theorem truncHeat_onDiagonal (hMSC : LatticeProb.External.MuruganSaloffCoste) (hd : 1 ≤ d)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
        Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
          (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ (t : ℝ≥0) (x y : Site d),
        ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y} ≤
          C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) *
            Real.exp (B * ρ ^ (-(2 : ℝ)) * t) := by
  obtain ⟨C, hC, hc⟩ := unitHeat_onDiagonal hMSC hd hlow hlam a ha
  obtain ⟨B, hB, hb⟩ := removed_intensity_le hd hlam
  refine ⟨C, B, hC, hB, ?_⟩
  intro ρ hρ t x y
  have h := (unitRates hd hlam a ha).transitionKernel_le_of_truncation
    (truncRates hd hlam a ha ρ) rfl (truncRates_q_le hd hlam a ha ρ)
    (mul_nonneg hB.le (Real.rpow_nonneg (zero_lt_one.trans_le hρ).le _))
    (hb a ha ρ hρ) t x y
  have ht := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht
  calc
    _ ≤ Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        ((unitRates hd hlam a ha).transitionKernel t x).real {y} := ht
    _ ≤ Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        (C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left (hc t x y) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- The truncated decay bound in the counting-density notation of CKKW. -/
theorem truncHeat_ckkw_onDiagonal (hMSC : LatticeProb.External.MuruganSaloffCoste) (hd : 1 ≤ d)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
        Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
          (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ (t : ℝ≥0) (x y : Site d),
        External.ckkwKernel (truncRates hd hlam a ha ρ) t x y ≤
          C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) *
            Real.exp (B * ρ ^ (-(2 : ℝ)) * t) :=
  truncHeat_onDiagonal hMSC hd hlow hlam a ha

/-- Unit conductances give a genuinely removed nearest-neighbor jump below radius one. -/
theorem removed_rate_one_dim :
    unitRate (fun _ : Edge 1 => (1 : ℝ)) 0 (fun _ => 1) -
      (truncRates (d := 1) (by norm_num) (lam := 1) (by norm_num)
        (fun _ => 1) (by intro _; norm_num) (1 / 2)).q 0 (fun _ => 1) = 1 := by
  have hn : (fun _ : Fin 1 => (1 : ℤ)) ≠ 0 := by
    intro h
    have hi := congrFun h 0
    norm_num at hi
  have hp := (physical_eq_zero_iff (d := 1) zero_lt_one _).not.mpr hn
  norm_num [truncRates, unitRate, jumpKernel, hn, hp, physical, radius,
    Fin.sum_univ_one]

/-- The small-cutoff vanishing result applies to distinct sites with unit conductances. -/
theorem truncHeat_one_dim_zero (t : ℝ≥0) :
    ((truncRates (d := 1) (by norm_num) (lam := 1) (by norm_num)
      (fun _ => 1) (by intro _; norm_num) (1 / 2)).transitionKernel t 0).real
        {fun _ => 1} = 0 := by
  apply truncHeat_zero_of_lt_one (d := 1) (by norm_num) (lam := 1) (by norm_num)
    (fun _ => 1) (by intro _; norm_num) (by norm_num) (by norm_num) t
  intro h
  have hi := congrFun h 0
  norm_num at hi

end

end LongRange
