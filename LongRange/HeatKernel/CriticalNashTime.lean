import LongRange.HeatKernel.CriticalNashIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time bound for the critical Nash recurrence

The integral comparison is controlled by the explicit logarithmic time scale.
-/

open LatticeProb MeasureTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The reciprocal Nash integrand is bounded by the derivative of the time scale. -/
theorem criticalNash_integrand_le_time_deriv {d : ℕ} (hd : 1 ≤ d)
    {D N s : ℝ} (hD : 0 < D) (hN : 0 < N) (hs : 0 < s) :
    N * (nashScale ((D / s) ^ (2 / (d : ℝ))) / s) ≤
      (N * (d : ℝ) / D) * (nashRate d (s / D))⁻¹ := by
  have hr : 0 < s / D := div_pos hs hD
  have ht := nashTime_pos d hr
  have hrate := (nashRate_comparison hd hr).2
  rw [nashRateStar_eq_div d hr] at hrate
  have heq : nashTime d (s / D) = nashScale ((D / s) ^ (2 / (d : ℝ))) := by
    unfold nashTime
    rw [Real.rpow_neg hr.le, ← Real.inv_rpow hr.le]
    congr 1
    field_simp
  have hratepos := nashRate_pos hd hr
  have hcomp : nashTime d (s / D) * nashRate d (s / D) ≤
      (d : ℝ) * (s / D) := by
    have := mul_le_mul_of_nonneg_left hrate ht.le
    calc
      nashTime d (s / D) * nashRate d (s / D) ≤
          nashTime d (s / D) * ((d : ℝ) * ((s / D) / nashTime d (s / D))) := this
      _ = (d : ℝ) * (s / D) := by field_simp
  rw [← heq]
  apply (le_mul_inv_iff₀ hratepos).2
  have h := mul_le_mul_of_nonneg_left hcomp (div_nonneg hN.le hs.le)
  calc
    N * (nashTime d (s / D) / s) * nashRate d (s / D) =
        (N / s) * (nashTime d (s / D) * nashRate d (s / D)) := by ring
    _ ≤ (N / s) * ((d : ℝ) * (s / D)) := h
    _ = N * (d : ℝ) / D := by field_simp

/-- The integral in the critical Nash comparison is bounded by the Nash time. -/
theorem criticalNash_integral_le_time {d : ℕ} (hd : 1 ≤ d)
    {D N a b : ℝ} (hD : 0 < D) (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, N * (nashScale ((D / s) ^ (2 / (d : ℝ))) / s)) ≤
      N * (d : ℝ) * nashTime d (a / D) := by
  have hb : 0 < b := ha.trans_le hab
  have hq : 0 ≤ 2 / (d : ℝ) := by positivity
  have hint := (criticalNash_integrand_intervalIntegrable D (2 / (d : ℝ)) hD hq ha hb).const_mul N
  have hderiv : ∀ s ∈ Icc a b, HasDerivAt
      (fun s : ℝ => -(N * (d : ℝ)) * nashTime d (s / D))
      ((N * (d : ℝ) / D) * (nashRate d (s / D))⁻¹) s := by
    intro s hs
    have hspos : 0 < s := ha.trans_le hs.1
    have h := (hasDerivAt_nashTime hd (div_pos hspos hD)).comp s
      ((hasDerivAt_id s).div_const D)
    convert h.const_mul (-(N * (d : ℝ))) using 1
    · ext x; simp only [Function.comp_def, id_eq]
    · ring
  have hcont : ContinuousOn (fun s : ℝ => -(N * (d : ℝ)) * nashTime d (s / D))
      (Icc a b) := fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun s : ℝ => N * (nashScale ((D / s) ^ (2 / (d : ℝ))) / s))
      (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint.1
  have hbound := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hcont
    (fun s hs => (hderiv s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt) hi
    (fun s hs => criticalNash_integrand_le_time_deriv hd hD hN (ha.trans hs.1))
  have hnonneg : 0 ≤ N * (d : ℝ) * nashTime d (b / D) := by
    exact mul_nonneg (mul_nonneg hN.le (Nat.cast_nonneg _)) (nashTime_pos d (div_pos hb hD)).le
  nlinarith

/-- A positive-time Nash integral bound implies an inverse-profile bound. -/
theorem nash_integral_to_profile {d : ℕ} (hd : 1 ≤ d)
    {D N a b t : ℝ} (hD : 0 < D) (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b)
    (ht : 0 < t)
    (hbound : t ≤ ∫ s in a..b, N * (nashScale ((D / s) ^ (2 / (d : ℝ))) / s)) :
    a ≤ D * nashProfile d (t / (N * (d : ℝ))) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hND : 0 < N * (d : ℝ) := mul_pos hN hdpos
  have ht' : 0 < t / (N * (d : ℝ)) := div_pos ht hND
  have htime : t / (N * (d : ℝ)) ≤ nashTime d (a / D) := by
    apply (div_le_iff₀ hND).2
    have h := hbound.trans (criticalNash_integral_le_time hd hD hN ha hab)
    nlinarith
  have hprofile : a / D ≤ nashProfile d (t / (N * (d : ℝ))) := by
    apply le_of_not_gt
    intro hlt
    have hs := nashTime_strictAntiOn hd (nashProfile_pos hd ht') (div_pos ha hD) hlt
    rw [nashTime_nashProfile hd ht'] at hs
    linarith
  simpa only [mul_comm] using (div_le_iff₀ hD).1 hprofile

/-- Critical-kernel iterates satisfy the explicit inverse Nash profile bound. -/
theorem weightedLattice_critical_nash_profile {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      ∀ (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x),
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (f : lp (fun _ : Site d => ℝ) 2), Summable (fun x => |f x|) →
        (∑' x, |f x|) ≤ 1 → ∀ n : ℕ, 0 < n →
          ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 ≤
            D * nashProfile d ((n : ℝ) / (N * (d : ℝ))) := by
  obtain ⟨D, N, hD, hN, hi⟩ := weightedLattice_critical_nash_integral hd C hC
  refine ⟨D, N, hD, hN, ?_⟩
  intro k hk hsym hlower f hf hf1 n hn
  have hd' : 1 ≤ d := hd
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht : 0 < (n : ℝ) / (N * (d : ℝ)) := by positivity
  by_cases hz : ‖(markovOperatorCLM k hk hsym ^ n) f‖ = 0
  · rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact (mul_pos hD (nashProfile_pos hd' ht)).le
  · have ha : 0 < ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 :=
      sq_pos_of_ne_zero hz
    have hab : ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      have h := antitone_norm_markovOperatorCLM_pow k hk hsym f (Nat.zero_le n)
      simpa using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 h)
    exact nash_integral_to_profile hd' hD hN ha hab (by exact_mod_cast hn)
      (hi k hk hsym hlower f hf hf1 n ha)

end LatticeProb.Graph.LongRangeKernel
