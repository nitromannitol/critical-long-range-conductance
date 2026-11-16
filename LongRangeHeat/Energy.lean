import LongRangeHeat.Dirichlet
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bounds for the energy estimate

These inequalities close the supremum estimate obtained by integrating the energy inequality.
-/

namespace LongRangeHeat

open LatticeProb LongRange
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

/-- The integrated squared-norm derivative with one-sided endpoint regularity. -/
theorem norm_sq_sub_eq_integral_of_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w w' : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn w (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt w (w' t) t)
    (hi : IntervalIntegrable (fun t => 2 * ⟪w t, w' t⟫_ℝ) MeasureTheory.volume a b) :
    ‖w b‖ ^ 2 - ‖w a‖ ^ 2 = ∫ t in a..b, 2 * ⟪w t, w' t⟫_ℝ := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hc.norm.pow 2)
    (fun t ht => (hd t ht).norm_sq) hi

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
    (hcont : ContinuousOn w (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w (w' t) t)
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
  have hct : ContinuousOn w (Set.Icc 0 t) := hcont.mono hsub
  have hdt : ∀ s ∈ Set.Ioo 0 t, HasDerivAt w (w' s) s :=
    fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩
  have hi : IntervalIntegrable (fun s => 2 * (A * S + B * g s))
      MeasureTheory.volume 0 t := by
    exact (intervalIntegrable_const.add ((hgi t ht).const_mul B)).const_mul 2
  have hm := intervalIntegral.integral_mono_on ht.1 (hdi t ht) hi (fun s hs => by
    have := he s (hsub hs)
    dsimp [S] at *
    linarith)
  rw [← norm_sq_sub_eq_integral_of_le w w' ht.1 hct hdt (hdi t ht)] at hm
  simp only [hw0, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hm
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    intervalIntegrable_const ((hgi t ht).const_mul B), intervalIntegral.integral_const_mul] at hm
  rw [intervalIntegral.integral_const_mul] at hm
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
  have htime : A * S * t ≤ A * S * T := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hA hS)
  have hforce : B * (∫ s in (0 : ℝ)..t, g s) ≤ B * Q := mul_le_mul_of_nonneg_left (hg t ht) hB
  dsimp [S] at *
  nlinarith

/-- Coercivity and the forcing bound yield the integrated supremum estimate. -/
theorem sSup_norm_le_of_coercive_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w w' : ℝ → E) (G D B : ℝ → ℝ)
    {T A c κ : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hc : 0 < c) (hκ : 0 < κ)
    (hw0 : w 0 = 0)
    (hb : BddAbove ((fun t => ‖w t‖) '' Set.Icc 0 T))
    (hcont : ContinuousOn w (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w (w' t) t)
    (hdi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => 2 * ⟪w s, w' s⟫_ℝ) MeasureTheory.volume 0 t)
    (hGi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => G s ^ 2) MeasureTheory.volume 0 t)
    (hcoercive : ∀ t ∈ Set.Icc 0 T, c / κ * D t ^ 2 ≤ B t)
    (henergy : ∀ t ∈ Set.Icc 0 T,
      ⟪w t, w' t⟫_ℝ + B t ≤ A / κ * ‖w t‖ + G t * D t / κ) :
    sSup ((fun t => ‖w t‖) '' Set.Icc 0 T) ≤
      2 * (A / κ) * T +
        Real.sqrt (2 * (1 / (4 * c * κ)) * ∫ s in (0 : ℝ)..T, G s ^ 2) := by
  have hQ : 0 ≤ ∫ s in (0 : ℝ)..T, G s ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  have hG : ∀ t ∈ Set.Icc 0 T,
      (∫ s in (0 : ℝ)..t, G s ^ 2) ≤ ∫ s in (0 : ℝ)..T, G s ^ 2 := by
    intro t ht
    exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hGi T ⟨hT, le_rfl⟩)
  apply sSup_norm_le_of_energy_inequality w w' (fun t => G t ^ 2)
    hT (div_nonneg hA hκ.le) (by positivity) hQ hw0 hb hcont hd hdi hGi hG
  intro t ht
  have hsup : ‖w t‖ ≤ sSup ((fun t => ‖w t‖) '' Set.Icc 0 T) :=
    le_csSup hb ⟨t, ht, rfl⟩
  have hmul := mul_le_mul_of_nonneg_left hsup (div_nonneg hA hκ.le)
  have hforce := forcing_le_coercive_add (G := G t) hc hκ (hcoercive t ht)
  have he := henergy t ht
  have heq : 1 / (4 * c * κ) * G t ^ 2 = G t ^ 2 / (4 * c * κ) := by ring
  rw [heq]
  linarith

private theorem lp_norm_sq_eq {d : ℕ} (f : lp (fun _ : Site d => ℝ) 2) :
    ‖f‖ ^ 2 = ∑' q, f q ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
  simpa [Real.norm_eq_abs, Real.rpow_two] using h

private theorem latticeNorm_scale {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (v : lp (fun _ : Site d => ℝ) 2) :
    ‖Real.sqrt (ε ^ d) • v‖ = latticeNorm ε v := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  unfold latticeNorm latticeNormSq
  rw [Real.sqrt_mul (pow_nonneg hε _), ← lp_norm_sq_eq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

private theorem latticeInner_scale {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (v w : lp (fun _ : Site d => ℝ) 2) :
    ⟪Real.sqrt (ε ^ d) • v, Real.sqrt (ε ^ d) • w⟫_ℝ = latticeInner ε v w := by
  rw [real_inner_smul_left, real_inner_smul_right, lp.inner_eq_tsum]
  simp only [Real.inner_apply]
  rw [latticeInner]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (pow_nonneg hε d)]

private theorem lattice_energy_bridge {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (w w' : ℝ → lp (fun _ : Site d => ℝ) 2) (G D B : ℝ → ℝ)
    {T A c κ : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hc : 0 < c) (hκ : 0 < κ)
    (hw0 : w 0 = 0)
    (hb : BddAbove ((fun t => latticeNorm ε (w t)) '' Set.Icc 0 T))
    (hcont : ContinuousOn w (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w (w' t) t)
    (hdi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => 2 * latticeInner ε (w s) (w' s)) MeasureTheory.volume 0 t)
    (hGi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => G s ^ 2) MeasureTheory.volume 0 t)
    (hcoercive : ∀ t ∈ Set.Icc 0 T, c / κ * D t ^ 2 ≤ B t)
    (henergy : ∀ t ∈ Set.Icc 0 T,
      latticeInner ε (w t) (w' t) + B t ≤
        A / κ * latticeNorm ε (w t) + G t * D t / κ) :
    sSup ((fun t => latticeNorm ε (w t)) '' Set.Icc 0 T) ≤
      2 * (A / κ) * T +
        Real.sqrt (2 * (1 / (4 * c * κ)) * ∫ s in (0 : ℝ)..T, G s ^ 2) := by
  have hbound := sSup_norm_le_of_coercive_energy
      (fun t => Real.sqrt (ε ^ d) • w t) (fun t => Real.sqrt (ε ^ d) • w' t)
      G D B hT hA hc hκ (by simp [hw0])
      (by simpa only [latticeNorm_scale hε] using hb)
      (hcont.const_smul (Real.sqrt (ε ^ d)))
      (fun t ht => (hd t ht).const_smul (Real.sqrt (ε ^ d)))
      (fun t ht => by simpa only [latticeInner_scale hε] using hdi t ht)
      hGi hcoercive
      (fun t ht => by simpa only [latticeInner_scale hε, latticeNorm_scale hε] using henergy t ht)
  simpa only [latticeNorm_scale hε] using hbound

private theorem lattice_energy_identity {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {w w' p r : Site d → ℝ} (hw : MemL2 w) (hp : MemL2 p) (hr : MemL2 r)
    (hode : ∀ q, w' q = generator ε a w q - p q - r q) :
    latticeInner ε w w' + bilinForm ε a w w =
      -latticeInner ε p w - latticeInner ε r w := by
  have hg := summable_mul_of_memL2 (memL2_generator hd hε hlam ha hw) hw
  have hps := summable_mul_of_memL2 hp hw
  have hrs := summable_mul_of_memL2 hr hw
  have heq : (∑' q, w q * w' q) =
      (∑' q, generator ε a w q * w q) - (∑' q, p q * w q) - (∑' q, r q * w q) := by
    rw [← hg.tsum_sub hps, ← (hg.sub hps).tsum_sub hrs]
    apply tsum_congr
    intro q
    rw [hode q]
    ring
  have h := latticeInner_generator_eq_neg_bilinForm (summable_generatorPair hd hε hlam ha hw hw)
  unfold latticeInner at h ⊢
  rw [heq, mul_sub, mul_sub]
  linarith

/-- The lattice energy estimate from the evolution equation, coercivity and forcing bounds. -/
theorem sSup_latticeNorm_le_of_forcing {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (hκ : 0 < kappa d ε)
    (w w' : ℝ → lp (fun _ : Site d => ℝ) 2) (p r : ℝ → Site d → ℝ)
    (G : ℝ → ℝ) {T A₁ A₂ : ℝ}
    (hT : 0 ≤ T) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hw0 : w 0 = 0)
    (hb : BddAbove ((fun t => latticeNorm ε (w t)) '' Set.Icc 0 T))
    (hcont : ContinuousOn w (Set.Icc 0 T))
    (hdiff : ∀ t ∈ Set.Ioo 0 T, HasDerivAt w (w' t) t)
    (hdi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => 2 * latticeInner ε (w s) (w' s)) MeasureTheory.volume 0 t)
    (hGi : ∀ t ∈ Set.Icc 0 T,
      IntervalIntegrable (fun s => G s ^ 2) MeasureTheory.volume 0 t)
    (hs : ∀ t ∈ Set.Icc 0 T, MemL2 (p t) ∧ MemL2 (r t))
    (hode : ∀ t ∈ Set.Icc 0 T, ∀ q, (w' t) q =
      generator ε a (w t) q - p t q - r t q)
    (hmean : ∀ t ∈ Set.Icc 0 T, |latticeInner ε (p t) (w t)| ≤
      A₁ / kappa d ε * latticeNorm ε (w t))
    (hforce : ∀ t ∈ Set.Icc 0 T, |latticeInner ε (r t) (w t)| ≤
      A₂ / kappa d ε * latticeNorm ε (w t) +
        G t * Real.sqrt (gradNormSq ε (w t)) / kappa d ε) :
    sSup ((fun t => latticeNorm ε (w t)) '' Set.Icc 0 T) ≤
      2 * ((A₁ + A₂) / kappa d ε) * T +
        Real.sqrt (2 * (1 / (4 * (lam / 2) * kappa d ε)) * ∫ s in (0 : ℝ)..T, G s ^ 2) := by
  have hgrad : ∀ t, 0 ≤ gradNormSq ε (w t) := by
    intro t
    unfold gradNormSq latticeNormSq
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg hε.le _) (tsum_nonneg fun q => sq_nonneg _)
  have hcoerc : ∀ t ∈ Set.Icc 0 T,
      (lam / 2) / kappa d ε * Real.sqrt (gradNormSq ε (w t)) ^ 2 ≤
        bilinForm ε a (w t) (w t) := by
    intro t ht
    rw [Real.sq_sqrt (hgrad t)]
    have hw : MemL2 (w t) := by
      have h := (lp.memℓp (w t)).summable (by norm_num)
      simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using h
    exact bilinForm_self_ge hd hε hlam ha hw
  apply lattice_energy_bridge hε.le w w' G (fun t => Real.sqrt (gradNormSq ε (w t)))
    (fun t => bilinForm ε a (w t) (w t)) hT (add_nonneg hA₁ hA₂)
    (by positivity : 0 < lam / 2) hκ hw0 hb hcont hdiff hdi hGi hcoerc
  intro t ht
  have hm := (abs_le.mp (hmean t ht)).1
  have hr := (abs_le.mp (hforce t ht)).1
  have hw : MemL2 (w t) := by
    have h := (lp.memℓp (w t)).summable (by norm_num)
    simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using h
  have hp := lattice_energy_identity hd hε hlam ha hw (hs t ht).1 (hs t ht).2 (hode t ht)
  rw [add_div, add_mul]
  linarith

end LongRangeHeat
