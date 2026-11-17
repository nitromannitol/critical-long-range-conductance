import LongRangeHeat.Continuum
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian vectors and the heat flow

A vector `Z` of `d` independent centered real Gaussians of variance `s`, scaled by `d^{-1/2}`, has
the density `heatKernel d s`: for a bounded continuous `ψ` on `ℝ^d`,
`E[ψ(x + d^{-1/2} Z)] = P̄_s ψ(x)` (`integral_pi_gaussian_eq_continuumHeat`).
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb.Heat Set
open scoped NNReal ENNReal

noncomputable section

variable {d : ℕ}

/-- The variance of the coordinates of `d^{-1/2} Z`. -/
def scaledVar (d : ℕ) (s : ℝ≥0) : ℝ≥0 :=
  ⟨((d : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2, sq_nonneg _⟩ * s

theorem coe_scaledVar (hd : 1 ≤ d) (s : ℝ≥0) : (scaledVar d s : ℝ) = s / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 := by norm_num
  have this : ((d : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (d : ℝ)⁻¹ := by
    calc ((d : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (d : ℝ) ^ ((-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ)) := by
          rw [Real.rpow_mul hd0.le, Real.rpow_natCast]
      _ = (d : ℝ)⁻¹ := by rw [h2, Real.rpow_neg_one]
  have h : (scaledVar d s : ℝ) = ((d : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 * s := rfl
  rw [h, this]
  ring

theorem heatKernel1_eq_gaussianPDFReal (hd : 1 ≤ d) {s : ℝ≥0} (hs : 0 < s) (y : ℝ) :
    heatKernel1 d s y = gaussianPDFReal 0 (scaledVar d s) y := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  rw [gaussianPDFReal, heatKernel1, coe_scaledVar hd]
  have hb : 2 * Real.pi * ((s : ℝ) / d) = 2 * Real.pi * s / d := by ring
  have e1 : (2 * Real.pi * (s : ℝ) / d) ^ (-(1 : ℝ) / 2) =
      (Real.sqrt (2 * Real.pi * ((s : ℝ) / d)))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity), hb]
    congr 1
    norm_num
  have e2 : Real.exp (-(d : ℝ) * y ^ 2 / (2 * s)) =
      Real.exp (-(y - 0) ^ 2 / (2 * ((s : ℝ) / d))) := by
    congr 1
    field_simp
    ring
  rw [e1, e2]

theorem heatKernel_neg (d : ℕ) (τ : ℝ) (x : Fin d → ℝ) : heatKernel d τ (-x) = heatKernel d τ x := by
  unfold heatKernel
  simp

theorem scaledVar_ne_zero (hd : 1 ≤ d) {s : ℝ≥0} (hs : 0 < s) : scaledVar d s ≠ 0 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  intro h
  have : (scaledVar d s : ℝ) = 0 := by rw [h]; rfl
  rw [coe_scaledVar hd] at this
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  exact (div_pos hs0 hd0).ne' this

/-- The product of `d` centered Gaussians of variance `v` has the product density. -/
theorem measure_pi_gaussian_eq_withDensity {v : ℝ≥0} (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 v) =
      volume.withDensity (fun y : Fin d → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 v (y i))) := by
  refine Measure.pi_eq fun A hA => ?_
  have hbox : MeasurableSet (Set.pi univ A) := MeasurableSet.univ_pi hA
  rw [withDensity_apply _ hbox]
  have hnn : ∀ x, 0 ≤ gaussianPDFReal 0 v x := fun x => gaussianPDFReal_nonneg 0 v x
  have hint : Integrable (fun y : Fin d → ℝ => ∏ i, gaussianPDFReal 0 v (y i)) volume :=
    Integrable.fintype_prod fun _ => integrable_gaussianPDFReal 0 v
  have hind : (Set.pi univ A).indicator (fun y : Fin d → ℝ => ∏ i, gaussianPDFReal 0 v (y i)) =
      fun y => ∏ i, (A i).indicator (gaussianPDFReal 0 v) (y i) := by
    funext y
    by_cases hy : y ∈ Set.pi univ A
    · rw [Set.indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (Set.mem_univ_pi.1 hy i) _).symm
    · rw [Set.indicator_of_notMem hy]
      rw [Set.mem_univ_pi, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  have hR : ∫ y in Set.pi univ A, ∏ i, gaussianPDFReal 0 v (y i) =
      ∏ i, ∫ x in A i, gaussianPDFReal 0 v x := by
    rw [← integral_indicator hbox, hind, integral_fintype_prod_volume_eq_prod]
    exact Finset.prod_congr rfl fun i _ => integral_indicator (hA i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (Filter.Eventually.of_forall fun y => Finset.prod_nonneg fun i _ => hnn _), hR,
    ENNReal.ofReal_prod_of_nonneg fun i _ => setIntegral_nonneg (hA i) fun x _ => hnn x]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 hv]

theorem pi_dirac_zero : Measure.pi (fun _ : Fin d => Measure.dirac (0 : ℝ)) =
    Measure.dirac 0 := by
  refine Measure.pi_eq fun A hA => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hA)]
  simp only [Measure.dirac_apply' _ (hA _)]
  by_cases h : ∀ i, (0 : ℝ) ∈ A i
  · simp [Set.indicator_of_mem, h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [Set.indicator_of_notMem (by simpa [Set.mem_univ_pi] using ⟨i, hi⟩)]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- The law of `d^{-1/2} Z` for a vector `Z` of independent centered Gaussians of variance `s` has
the density `heatKernel d s`. -/
theorem map_pi_gaussian (hd : 1 ≤ d) {s : ℝ≥0} (hs : 0 < s) :
    (Measure.pi fun _ : Fin d => gaussianReal 0 s).map
        (fun z : Fin d → ℝ => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z) =
      volume.withDensity (fun y => ENNReal.ofReal (heatKernel d s y)) := by
  have hv := scaledVar_ne_zero hd hs
  have h1 : (Measure.pi fun _ : Fin d => gaussianReal 0 s).map
      (fun z : Fin d → ℝ => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z) =
      Measure.pi fun _ : Fin d => gaussianReal 0 (scaledVar d s) := by
    have hfun : (fun z : Fin d → ℝ => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z) =
        fun z i => ((d : ℝ) ^ (-(1 : ℝ) / 2)) * z i := by
      funext z i
      simp [smul_eq_mul]
    rw [hfun, Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal 0 s)
      (f := fun _ x => ((d : ℝ) ^ (-(1 : ℝ) / 2)) * x)
      (fun _ => (measurable_const_mul _).aemeasurable)]
    simp only [gaussianReal_map_const_mul, mul_zero]
    rfl
  rw [h1, measure_pi_gaussian_eq_withDensity hv]
  congr 1
  funext y
  rw [heatKernel_of_pos (by exact_mod_cast hs)]
  simp only [heatKernel1_eq_gaussianPDFReal hd hs]

/-- **Gaussian steps of Brownian motion.** `E[ψ(x + d^{-1/2} Z)] = P̄_s ψ(x)`. -/
theorem integral_pi_gaussian_eq_continuumHeat (hd : 1 ≤ d) {s : ℝ≥0} {ψ : (Fin d → ℝ) → ℝ}
    (hψ : Continuous ψ) (x : Fin d → ℝ) :
    ∫ z, ψ (x + ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 s) =
      continuumHeat ψ s x := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [gaussianReal_zero_var, pi_dirac_zero, integral_dirac]
    simp [continuumHeat_zero]
  · have hmap : Measurable fun z : Fin d → ℝ => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z :=
      measurable_const_smul _
    have h1 : ∫ z, ψ (x + ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z)
        ∂(Measure.pi fun _ : Fin d => gaussianReal 0 s) =
        ∫ w, ψ (x + w) ∂((Measure.pi fun _ : Fin d => gaussianReal 0 s).map
          (fun z : Fin d → ℝ => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • z)) := by
      rw [integral_map hmap.aemeasurable]
      exact (hψ.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    rw [h1, map_pi_gaussian hd hs, integral_withDensity_eq_integral_toReal_smul]
    · have hK : ∀ w, (ENNReal.ofReal (heatKernel d s w)).toReal = heatKernel d s w := fun w =>
        ENNReal.toReal_ofReal (by
          rw [heatKernel_of_pos (by exact_mod_cast hs)]
          exact Finset.prod_nonneg fun i _ => by
            rw [heatKernel1_eq_gaussianPDFReal hd hs]
            exact gaussianPDFReal_nonneg _ _ _)
      simp_rw [hK, smul_eq_mul]
      rw [continuumHeat_eq_integral ψ (by exact_mod_cast hs) x,
        ← integral_neg_eq_self (fun w => heatKernel d s w * ψ (x + w)) volume]
      simp [heatKernel_neg, sub_eq_add_neg]
    · have hs' : (0 : ℝ) < s := by exact_mod_cast hs
      have : (fun y : Fin d → ℝ => heatKernel d s y) = fun y => ∏ i, heatKernel1 d s (y i) :=
        funext fun y => heatKernel_of_pos hs' y
      have hm : Measurable fun y : Fin d → ℝ => heatKernel d s y := by
        rw [this]
        refine Finset.measurable_prod _ fun i _ => ?_
        exact (by unfold heatKernel1; fun_prop : Measurable fun t : ℝ => heatKernel1 d s t).comp
          (measurable_pi_apply i)
      exact ENNReal.measurable_ofReal.comp hm
    · exact Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top

end

end LongRangeHeat
