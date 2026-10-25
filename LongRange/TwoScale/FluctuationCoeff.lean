import LongRange.TwoScale.ResidualDefs
import LongRange.Dirichlet.Weights
import LongRange.Calculus.Summability
import LatticeProb.Analysis.TaylorHolder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Coefficients of the smooth fluctuation

The bounded Hessian controls the smooth remainder in the Euclidean radius.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A bounded Hessian bounds the first-order remainder quadratically in Euclidean radius. -/
theorem smoothRemainder_abs_le_sq {v : (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ 2 v)
    {B₂ : ℝ} (hB₂ : ∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B₂)
    (x z : Fin d → ℝ) :
    |smoothRemainder v x z| ≤ B₂ / 2 * radius z ^ 2 := by
  have hB : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ x)
  have heval (y : Fin d → ℝ) :
      |iteratedFDeriv ℝ 2 v y ![z, z]| ≤ B₂ * radius z ^ 2 := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 v y‖ * (‖z‖ * ‖z‖) := by
        simpa only [Real.norm_eq_abs, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one] using (iteratedFDeriv ℝ 2 v y).le_opNorm ![z, z]
      _ ≤ B₂ * radius z ^ 2 := by
        rw [← pow_two]
        exact mul_le_mul (hB₂ y)
          (pow_le_pow_left₀ (norm_nonneg z) (TaylorHolder.norm_le_radius z) 2)
          (sq_nonneg _) hB
  rw [smoothRemainder, TaylorHolder.remainder_eq_integral hv]
  have hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖(1 - t) * iteratedFDeriv ℝ 2 v (x + t • z) ![z, z]‖ ≤
        (1 - t) * (B₂ * radius z ^ 2) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact mul_le_mul_of_nonneg_left (heval _) (sub_nonneg.mpr ht.2)
  have hi : IntervalIntegrable (fun t : ℝ => (1 - t) * (B₂ * radius z ^ 2))
      MeasureTheory.volume 0 1 :=
    ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (MeasureTheory.ae_of_all _ hb) hi
  rw [Real.norm_eq_abs] at h
  have hint : (∫ t in (0 : ℝ)..1, (1 - t) * (B₂ * radius z ^ 2)) =
      B₂ / 2 * radius z ^ 2 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
        (g := fun t : ℝ => t) (continuous_const.intervalIntegrable 0 1)
        (continuous_id.intervalIntegrable 0 1)]
    norm_num [integral_id]
    ring
  exact h.trans_eq hint


/-- Smooth fluctuation coefficients are summable and have a scale-uniform square bound. -/
theorem fluctuation_coeff_sq_sum_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (v : (Fin d → ℝ) → ℝ) (B : ℝ),
      ContDiff ℝ 2 v → (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → ∀ q : Site d,
        Summable (fun w : Site d => if w = 0 then 0 else
          ε ^ d / kappa d ε * jumpKernel (physical ε w) *
            smoothRemainder v (physical ε q) (physical ε w)) ∧
        ∑' w : Site d, (if w = 0 then 0 else
          ε ^ d / kappa d ε * jumpKernel (physical ε w) *
            smoothRemainder v (physical ε q) (physical ε w)) ^ 2 ≤
              C * B ^ 2 / kappa d ε ^ 2 := by
  classical
  obtain ⟨A, hA, ha⟩ := punctured_radial_sum_bound hd (2 * d) (by omega)
  obtain ⟨D, _, hdSum⟩ := punctured_radial_sum_bound hd (d + 1) (by omega)
  refine ⟨A, hA, ?_⟩
  intro ε hε v B hv hv0 hv1 hv2 q
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hk := kappa_pos hd hε
  let c := fun w : Site d => if w = 0 then (0 : ℝ) else
    ε ^ d / kappa d ε * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)
  let g := fun n : ℕ => fun w : Site d => if w = 0 then (0 : ℝ) else
    (radius (physical 1 w) ^ n)⁻¹
  have hg : Summable (g (2 * d)) := (ha 1 zero_lt_one).1
  have hgs : ∑' w, g (2 * d) w ≤ A := by
    simpa only [one_pow, one_mul] using (ha 1 zero_lt_one).2
  have hlin (w : Site d) : ‖c w‖ ≤
      (ε ^ d / kappa d ε * (2 * B) *
        ((ε ^ (d + 2))⁻¹ * (1 + ε))) * g (d + 1) w := by
    by_cases hw : w = 0
    · simp only [c, g, hw, if_true, norm_zero, mul_zero, le_refl]
    simp only [c, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (div_nonneg (pow_nonneg hε.1.le _) hk.le),
      abs_of_nonneg (jumpKernel_nonneg _), g, if_neg hw]
    calc
      _ ≤ ε ^ d / kappa d ε * jumpKernel (physical ε w) *
          (2 * B * (1 + radius (physical ε w))) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) hk.le)
            (jumpKernel_nonneg _))
        exact (TaylorHolder.remainder_le_linear hv0 hv1 _ _).trans (by
          have hr := radius_nonneg (physical ε w)
          nlinarith only [mul_nonneg hB hr])
      _ = (ε ^ d / kappa d ε * (2 * B)) *
          (jumpKernel (physical ε w) * (1 + radius (physical ε w))) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (jumpKernel_weight_le hε.1 hw)
          (mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) hk.le)
            (mul_nonneg (by norm_num) hB))
  have hc : Summable c :=
    ((hdSum 1 zero_lt_one).1.mul_left _).of_norm_bounded hlin
  have hquad (w : Site d) : |c w| ≤ B / kappa d ε * g d w := by
    by_cases hw : w = 0
    · simp only [c, g, hw, if_true, abs_zero, mul_zero, le_refl]
    have hr := lt_of_lt_of_le zero_lt_one (lattice_radius_ge_one hw)
    have hrem := smoothRemainder_abs_le_sq hv hv2 (physical ε q) (physical ε w)
    have hrem' : |smoothRemainder v (physical ε q) (physical ε w)| ≤
        B * radius (physical ε w) ^ 2 :=
      hrem.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
    simp only [c, abs_mul,
      abs_of_nonneg (div_nonneg (pow_nonneg hε.1.le _) hk.le),
      abs_of_nonneg (jumpKernel_nonneg _), g, if_neg hw]
    calc
      _ ≤ ε ^ d / kappa d ε * jumpKernel (physical ε w) *
          (B * radius (physical ε w) ^ 2) :=
        mul_le_mul_of_nonneg_left hrem'
          (mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) hk.le)
            (jumpKernel_nonneg _))
      _ = _ := by
        rw [jumpKernel_physical hε.1 hw, radius_physical_eq_mul hε.1.le,
          mul_pow]
        simp only [pow_add, pow_two]
        field_simp [hε.1.ne', hk.ne', hr.ne']
  have hsq (w : Site d) : c w ^ 2 ≤
      (B / kappa d ε) ^ 2 * g (2 * d) w := by
    calc
      c w ^ 2 = |c w| ^ 2 := (sq_abs _).symm
      _ ≤ (B / kappa d ε * g d w) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hquad w) 2
      _ = _ := by
        dsimp [g]
        split_ifs <;> simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), mul_pow,
          inv_pow, show 2 * d = d * 2 by omega, pow_mul]
  have hs : Summable (fun w => c w ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsq (hg.mul_left _)
  refine ⟨hc, ?_⟩
  change ∑' w, c w ^ 2 ≤ _
  calc
    _ ≤ ∑' w, (B / kappa d ε) ^ 2 * g (2 * d) w :=
      hs.tsum_le_tsum hsq (hg.mul_left _)
    _ = (B / kappa d ε) ^ 2 * ∑' w, g (2 * d) w := tsum_mul_left
    _ ≤ (B / kappa d ε) ^ 2 * A :=
      mul_le_mul_of_nonneg_left hgs (sq_nonneg _)
    _ = A * B ^ 2 / kappa d ε ^ 2 := by ring

end
end LongRange
