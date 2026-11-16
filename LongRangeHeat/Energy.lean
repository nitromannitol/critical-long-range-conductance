import LongRangeHeat.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bounds for the energy estimate

These inequalities close the supremum estimate obtained by integrating the energy inequality.
-/

namespace LongRangeHeat
open scoped InnerProductSpace Interval

/-- A quadratic estimate gives the bound used at the end of the energy argument. -/
theorem le_add_sqrt_of_sq_le_mul_add {S A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : S ^ 2 ≤ A * S + B) : S ≤ A + Real.sqrt B := by
  have hr : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hrsq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
  by_contra hn
  have hS : A + Real.sqrt B < S := lt_of_not_ge hn
  have hprod : 0 ≤ A * Real.sqrt B := mul_nonneg hA hr
  nlinarith

/-- The integrated quadratic bound controls the supremum of a nonnegative error. -/
theorem sSup_le_add_sqrt_of_sq_le {ι : Type*} (s : Set ι) (v : ι → ℝ)
    {A B : ℝ} (hs : s.Nonempty) (hb : BddAbove (v '' s))
    (hv : ∀ t ∈ s, 0 ≤ v t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t ∈ s, (v t) ^ 2 ≤ A * sSup (v '' s) + B) :
    sSup (v '' s) ≤ A + Real.sqrt B := by
  have hne : (v '' s).Nonempty := hs.image v
  have hsup : 0 ≤ sSup (v '' s) := by
    obtain ⟨t, ht⟩ := hs
    exact (hv t ht).trans (le_csSup hb ⟨t, ht, rfl⟩)
  have hsquare : (sSup (v '' s)) ^ 2 ≤ A * sSup (v '' s) + B := by
    have hbound : sSup (v '' s) ≤ Real.sqrt (A * sSup (v '' s) + B) := by
      apply csSup_le hne
      rintro _ ⟨t, ht, rfl⟩
      exact Real.le_sqrt_of_sq_le (h t ht)
    have hnonneg : 0 ≤ A * sSup (v '' s) + B := add_nonneg (mul_nonneg hA hsup) hB
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (A * sSup (v '' s) + B)]
  exact le_add_sqrt_of_sq_le_mul_add hA hB hsquare

/-- The integrated derivative of the squared norm along a Hilbert-space path. -/
theorem norm_sq_sub_eq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w w' : ℝ → E) (a b : ℝ)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt w (w' t) t)
    (hi : IntervalIntegrable (fun t => 2 * ⟪w t, w' t⟫_ℝ) MeasureTheory.volume a b) :
    ‖w b‖ ^ 2 - ‖w a‖ ^ 2 = ∫ t in a..b, 2 * ⟪w t, w' t⟫_ℝ := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hd t ht).norm_sq) hi

/-- Coercivity absorbs the gradient forcing term in the energy estimate. -/
theorem forcing_le_coercive_add {c κ D G B : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hB : c / κ * D ^ 2 ≤ B) :
    G * D / κ ≤ B + G ^ 2 / (4 * c * κ) := by
  have hBmul : c * D ^ 2 ≤ κ * B := by
    have hB' : c * D ^ 2 / κ ≤ B := by
      simpa [div_mul_eq_mul_div] using hB
    simpa [mul_comm] using (div_le_iff₀ hκ).mp hB'
  have hprod : 0 ≤ 4 * c * (κ * B - c * D ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hBmul)
  have hsq := sq_nonneg (2 * c * D - G)
  have hmain : 4 * c * G * D ≤ 4 * c * κ * B + G ^ 2 := by nlinarith
  apply (div_le_iff₀ hκ).2
  have haux : G * D ≤ κ * B + G ^ 2 / (4 * c) := by
    have hmul : (G * D - κ * B) * (4 * c) ≤ G ^ 2 := by nlinarith [hmain]
    have hdiv := (le_div_iff₀ (show 0 < 4 * c by positivity)).2 hmul
    linarith
  have heq : (B + G ^ 2 / (4 * c * κ)) * κ = κ * B + G ^ 2 / (4 * c) := by
    field_simp [hc.ne', hκ.ne']
  rw [heq]
  exact haux

/-- An integrated energy inequality controls the maximum norm of a Hilbert-space path. -/
theorem sSup_norm_le_of_energy_inequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w w' : ℝ → E) (g : ℝ → ℝ) {T A B Q : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hw0 : w 0 = 0) (hb : BddAbove ((fun t => ‖w t‖) '' Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Icc 0 T, HasDerivAt w (w' t) t)
    (hdi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => 2 * ⟪w s, w' s⟫_ℝ) MeasureTheory.volume 0 t)
    (hgi : ∀ t ∈ Set.Icc 0 T, IntervalIntegrable g MeasureTheory.volume 0 t)
    (hg : ∀ t ∈ Set.Icc 0 T, (∫ s in (0 : ℝ)..t, g s) ≤ Q)
    (he : ∀ t ∈ Set.Icc 0 T,
      ⟪w t, w' t⟫_ℝ ≤ A * sSup ((fun t => ‖w t‖) '' Set.Icc 0 T) + B * g t) :
    sSup ((fun t => ‖w t‖) '' Set.Icc 0 T) ≤ 2 * A * T + Real.sqrt (2 * B * Q) := by
  let S := sSup ((fun t => ‖w t‖) '' Set.Icc 0 T)
  have hS : 0 ≤ S := by
    exact (norm_nonneg (w 0)).trans (le_csSup hb ⟨0, ⟨le_rfl, hT⟩, rfl⟩)
  apply sSup_le_add_sqrt_of_sq_le (Set.Icc 0 T) (fun t => ‖w t‖)
    ⟨0, ⟨le_rfl, hT⟩⟩ hb (fun t _ => norm_nonneg (w t)) (by positivity) (by positivity)
  intro t ht
  have hsub : Set.Icc 0 t ⊆ Set.Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hdt : ∀ s ∈ Set.uIcc 0 t, HasDerivAt w (w' s) s := by
    rw [Set.uIcc_of_le ht.1]
    exact fun s hs => hd s (hsub hs)
  have hi : IntervalIntegrable (fun s => 2 * (A * S + B * g s))
      MeasureTheory.volume 0 t := by
    exact (intervalIntegrable_const.add ((hgi t ht).const_mul B)).const_mul 2
  have hm := intervalIntegral.integral_mono_on ht.1 (hdi t ht) hi (fun s hs => by
    have := he s (hsub hs)
    dsimp [S] at *
    linarith)
  rw [← norm_sq_sub_eq_integral w w' 0 t hdt (hdi t ht)] at hm
  simp only [hw0, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hm
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    intervalIntegrable_const ((hgi t ht).const_mul B), intervalIntegral.integral_const_mul] at hm
  rw [intervalIntegral.integral_const_mul] at hm
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
  have htime : A * S * t ≤ A * S * T := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hA hS)
  have hforce : B * (∫ s in (0 : ℝ)..t, g s) ≤ B * Q := mul_le_mul_of_nonneg_left (hg t ht) hB
  dsimp [S] at *
  nlinarith

end LongRangeHeat
