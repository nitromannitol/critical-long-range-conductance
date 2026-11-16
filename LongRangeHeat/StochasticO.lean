import LongRangeHeat.Defs

/-!
# The calculus of the stochastic order `𝒪_q`

This file proves the properties of the relation `X ≤ 𝒪_q(A)` (`LongRangeHeat.IsOq`) collected in
Lemma 2.3 (`lem:O`) of the heat-kernel version: squares, expectation, countable sums, integrals
over a time interval and constants. The sums and integrals follow from Jensen's inequality for the
convex function `r ↦ exp(r^q)` on `[0, ∞)`: a finite weighted average first, then a supremum over
the finite subsets of the index set (respectively an average over `[0, T]` together with Tonelli's
theorem). The statements are proved for every exponent `q ≥ 1`.
-/

namespace LongRangeHeat

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The function `r ↦ exp(r^q)` -/

/-- The function `r ↦ exp(r^q)` is convex on `[0, ∞)`. -/
theorem convexOn_exp_pow (q : ℕ) : ConvexOn ℝ (Ici 0) fun r : ℝ => Real.exp (r ^ q) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := (convexOn_pow q).2 hx hy ha hb hab
  have h2 := convexOn_exp.2 (mem_univ (x ^ q)) (mem_univ (y ^ q)) ha hb hab
  exact (Real.exp_le_exp.mpr h1).trans h2

/-- For `q ≥ 1` and `r ≥ 0`, `r ≤ exp(r^q)`. -/
theorem le_exp_pow {q : ℕ} (hq : q ≠ 0) {r : ℝ} (hr : 0 ≤ r) : r ≤ Real.exp (r ^ q) := by
  rcases le_total r 1 with h | h
  · exact h.trans (Real.one_le_exp (pow_nonneg hr q))
  · calc r ≤ r ^ q := le_self_pow₀ h hq
      _ ≤ r ^ q + 1 := le_add_of_nonneg_right zero_le_one
      _ ≤ Real.exp (r ^ q) := Real.add_one_le_exp _

/-- The integrand `r ↦ exp((max(r, 0) / A)^q)` of `𝒪_q(A)` is continuous. -/
theorem continuous_oqIntegrand (q : ℕ) (A : ℝ) :
    Continuous fun r : ℝ => ENNReal.ofReal (Real.exp ((max r 0 / A) ^ q)) :=
  ENNReal.continuous_ofReal.comp
    (Real.continuous_exp.comp (((continuous_id.max continuous_const).div_const A).pow q))

/-! ### Squares, expectation and constants -/

/-- Squares: for `X ≥ 0` and `A > 0`, `X ≤ 𝒪₂(A)` if and only if `X² ≤ 𝒪₁(A²)`. -/
theorem isOq_two_iff {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) (A : ℝ) :
    IsOq P 2 X A ↔ IsOq P 1 (fun ω => X ω ^ 2) (A ^ 2) := by
  have hint : ∀ ω, (max (X ω) 0 / A) ^ 2 = (max (X ω ^ 2) 0 / A ^ 2) ^ 1 := by
    intro ω
    rw [max_eq_left (hX ω), max_eq_left (sq_nonneg _), pow_one, div_pow]
  simp only [IsOq, hint]
  refine and_congr ⟨fun h => h.pow_const 2, fun h => ?_⟩ Iff.rfl
  have hsq : X = fun ω => Real.sqrt (X ω ^ 2) := funext fun ω => (Real.sqrt_sq (hX ω)).symm
  rw [hsq]
  exact Real.continuous_sqrt.measurable.comp_aemeasurable h

/-- Expectation: if `X ≤ 𝒪₂(A)` with `A > 0`, then `max(X, 0)` is integrable and
`𝔼[max(X, 0)] ≤ 2A`. -/
theorem integrable_and_integral_max_le {X : Ω → ℝ} {A : ℝ} (hA : 0 < A) (h : IsOq P 2 X A) :
    Integrable (fun ω => max (X ω) 0) P ∧ ∫ ω, max (X ω) 0 ∂P ≤ 2 * A := by
  have hm : AEMeasurable (fun ω => max (X ω) 0) P := h.1.max aemeasurable_const
  have hpt : ∀ ω, ENNReal.ofReal (max (X ω) 0) ≤
      ENNReal.ofReal A * ENNReal.ofReal (Real.exp ((max (X ω) 0 / A) ^ 2)) := by
    intro ω
    rw [← ENNReal.ofReal_mul hA.le]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 ≤ max (X ω) 0 / A := div_nonneg (le_max_right _ _) hA.le
    calc max (X ω) 0 = A * (max (X ω) 0 / A) := by field_simp
      _ ≤ A * Real.exp ((max (X ω) 0 / A) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_exp_pow two_ne_zero h0) hA.le
  have hle : ∫⁻ ω, ENNReal.ofReal (max (X ω) 0) ∂P ≤ ENNReal.ofReal (2 * A) := by
    calc ∫⁻ ω, ENNReal.ofReal (max (X ω) 0) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal A * ENNReal.ofReal (Real.exp ((max (X ω) 0 / A) ^ 2)) ∂P :=
          lintegral_mono hpt
      _ = ENNReal.ofReal A * ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / A) ^ 2)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal A * 2 := by gcongr; exact h.2
      _ = ENNReal.ofReal (2 * A) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, mul_comm]
  have hnn : 0 ≤ᵐ[P] fun ω => max (X ω) 0 := Eventually.of_forall fun ω => le_max_right _ _
  have hint : Integrable (fun ω => max (X ω) 0) P :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).mpr
      (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

/-- Constants: for `q ≥ 1` and `A > 0` the constant `A` satisfies `A ≤ 𝒪_q(2A)`. -/
theorem isOq_const [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0) {A : ℝ} (hA : 0 < A) :
    IsOq P q (fun _ => A) (2 * A) := by
  refine ⟨aemeasurable_const, ?_⟩
  rw [lintegral_const, measure_univ, mul_one]
  have h : max A 0 / (2 * A) = 1 / 2 := by
    rw [max_eq_left hA.le]
    field_simp
  rw [h]
  have h1 : (1 / 2 : ℝ) ^ q ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) hq
  have h2 : Real.exp (1 / 2) < 2 := by
    have he : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (1 / 2), Real.exp_one_lt_d9]
  calc ENNReal.ofReal (Real.exp ((1 / 2) ^ q)) ≤ ENNReal.ofReal 2 :=
        ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.mpr h1).trans h2.le)
    _ = 2 := ENNReal.ofReal_ofNat 2

/-! ### Sums -/

/-- Jensen's inequality for a finite family: if `X_k ≥ 0`, `X_k ≤ 𝒪_q(A_k)` and
`∑_{k ∈ s} A_k ≤ A₀`, then `𝔼[exp((∑_{k ∈ s} X_k / A₀)^q)] ≤ 2`. -/
theorem lintegral_finsetSum_le_two [IsProbabilityMeasure P] {ι : Type*} {q : ℕ} (hq : q ≠ 0)
    {X : ι → Ω → ℝ} (hX : ∀ k ω, 0 ≤ X k ω) {A : ι → ℝ} (hA : ∀ k, 0 < A k)
    (h : ∀ k, IsOq P q (X k) (A k)) (s : Finset ι) {A₀ : ℝ} (hsA : ∑ k ∈ s, A k ≤ A₀) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (∑ k ∈ s, X k ω) 0 / A₀) ^ q)) ∂P ≤ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty, max_self, zero_div, zero_pow hq, Real.exp_zero,
      ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
    norm_num
  set B := ∑ k ∈ s, A k with hBdef
  have hB : 0 < B := Finset.sum_pos (fun k _ => hA k) hs
  have hw : ∀ k, 0 ≤ A k / B := fun k => (div_pos (hA k) hB).le
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp ((max (∑ k ∈ s, X k ω) 0 / A₀) ^ q)) ≤
      ∑ k ∈ s, ENNReal.ofReal (A k / B) *
        ENNReal.ofReal (Real.exp ((max (X k ω) 0 / A k) ^ q)) := by
    intro ω
    have hS : 0 ≤ ∑ k ∈ s, X k ω := Finset.sum_nonneg fun k _ => hX k ω
    have hJ := (convexOn_exp_pow q).map_sum_le (t := s) (w := fun k => A k / B)
      (p := fun k => X k ω / A k) (fun k _ => hw k)
      (by rw [← Finset.sum_div, div_self hB.ne']) (fun k _ => div_nonneg (hX k ω) (hA k).le)
    have hcomb : ∑ k ∈ s, A k / B * (X k ω / A k) = (∑ k ∈ s, X k ω) / B := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp [(hA k).ne']
    simp only [smul_eq_mul] at hJ
    rw [hcomb] at hJ
    rw [max_eq_left hS]
    calc ENNReal.ofReal (Real.exp (((∑ k ∈ s, X k ω) / A₀) ^ q))
        ≤ ENNReal.ofReal (Real.exp (((∑ k ∈ s, X k ω) / B) ^ q)) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          exact pow_le_pow_left₀ (div_nonneg hS (hB.le.trans hsA))
            (div_le_div_of_nonneg_left hS hB hsA) q
      _ ≤ ENNReal.ofReal (∑ k ∈ s, A k / B * Real.exp ((X k ω / A k) ^ q)) :=
          ENNReal.ofReal_le_ofReal hJ
      _ = _ := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun k _ => mul_nonneg (hw k) (Real.exp_pos _).le)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_mul (hw k), max_eq_left (hX k ω)]
  have hmeas : ∀ k, AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp ((max (X k ω) 0 / A k) ^ q))) P := fun k =>
    (continuous_oqIntegrand q (A k)).measurable.comp_aemeasurable (h k).1
  calc _ ≤ ∫⁻ ω, ∑ k ∈ s, ENNReal.ofReal (A k / B) *
        ENNReal.ofReal (Real.exp ((max (X k ω) 0 / A k) ^ q)) ∂P := lintegral_mono hpt
    _ = ∑ k ∈ s, ENNReal.ofReal (A k / B) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X k ω) 0 / A k) ^ q)) ∂P := by
        rw [lintegral_finsetSum' s fun k _ => (hmeas k).const_mul _]
        exact Finset.sum_congr rfl fun k _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ k ∈ s, ENNReal.ofReal (A k / B) * 2 :=
        Finset.sum_le_sum fun k _ => by gcongr; exact (h k).2
    _ = 2 := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun k _ => hw k, ← Finset.sum_div,
          ← hBdef, div_self hB.ne', ENNReal.ofReal_one, one_mul]

/-- Sums over a countable index set: if `X_k ≥ 0`, `A_k > 0` with `∑ A_k < ∞` and
`X_k ≤ 𝒪_q(A_k)` for every `k`, then `∑ X_k` converges almost surely and
`∑ X_k ≤ 𝒪_q(∑ A_k)`. -/
theorem isOq_tsum [IsProbabilityMeasure P] {ι : Type*} [Countable ι] {q : ℕ} (hq : q ≠ 0)
    {X : ι → Ω → ℝ} (hX : ∀ k ω, 0 ≤ X k ω) {A : ι → ℝ} (hA : ∀ k, 0 < A k)
    (hAs : Summable A) (h : ∀ k, IsOq P q (X k) (A k)) :
    (∀ᵐ ω ∂P, Summable fun k => X k ω) ∧ IsOq P q (fun ω => ∑' k, X k ω) (∑' k, A k) := by
  classical
  set A₀ := ∑' k, A k with hA₀
  have hA0 : 0 ≤ A₀ := tsum_nonneg fun k => (hA k).le
  set φ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp ((max r 0 / A₀) ^ q)) with hφ
  have hφc : Continuous φ := continuous_oqIntegrand q A₀
  set F : Finset ι → Ω → ℝ≥0∞ := fun s ω => φ (∑ k ∈ s, X k ω) with hFdef
  have hF : ∀ s, ∫⁻ ω, F s ω ∂P ≤ 2 := fun s =>
    lintegral_finsetSum_le_two hq hX hA h s (hAs.sum_le_tsum s fun k _ => (hA k).le)
  have hFm : ∀ s, AEMeasurable (F s) P := fun s =>
    hφc.measurable.comp_aemeasurable (Finset.aemeasurable_fun_sum s fun k _ => (h k).1)
  have hmono : ∀ ω, Monotone fun s : Finset ι => F s ω := by
    intro ω s t hst
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hst (fun k _ _ => hX k ω)
    have h0 : 0 ≤ ∑ k ∈ s, X k ω := Finset.sum_nonneg fun k _ => hX k ω
    rw [max_eq_left h0, max_eq_left (h0.trans h1)]
    exact pow_le_pow_left₀ (div_nonneg h0 hA0) (div_le_div_of_nonneg_right h1 hA0) q
  have hdir : Directed (· ≤ ·) F := fun s t =>
    ⟨s ∪ t, fun ω => hmono ω Finset.subset_union_left,
      fun ω => hmono ω Finset.subset_union_right⟩
  have hsup : ∫⁻ ω, ⨆ s, F s ω ∂P ≤ 2 := by
    rw [lintegral_iSup_directed hFm hdir]
    exact iSup_le hF
  have hfin : ∀ᵐ ω ∂P, ⨆ s, F s ω < ∞ :=
    ae_lt_top' (AEMeasurable.iSup hFm) (ne_top_of_le_ne_top ENNReal.ofNat_ne_top hsup)
  have hsum : ∀ᵐ ω ∂P, Summable fun k => X k ω := by
    filter_upwards [hfin] with ω hω
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨k₀⟩⟩
    · exact .of_finite
    have hpos : 0 < A₀ := hAs.tsum_pos (fun k => (hA k).le) k₀ (hA k₀)
    refine summable_of_sum_le (c := A₀ * (⨆ s, F s ω).toReal) (fun k => hX k ω) fun s => ?_
    have h0 : 0 ≤ ∑ k ∈ s, X k ω := Finset.sum_nonneg fun k _ => hX k ω
    have h1 : (∑ k ∈ s, X k ω) / A₀ ≤ (F s ω).toReal := by
      simp only [hFdef, hφ, max_eq_left h0]
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
      exact le_exp_pow hq (div_nonneg h0 hpos.le)
    have h2 : (F s ω).toReal ≤ (⨆ s, F s ω).toReal :=
      ENNReal.toReal_mono hω.ne (le_iSup (fun s => F s ω) s)
    rw [← div_le_iff₀' hpos]
    exact h1.trans h2
  refine ⟨hsum, ?_, ?_⟩
  · have heq : (fun ω => ∑' k, X k ω) = fun ω => (∑' k, ENNReal.ofReal (X k ω)).toReal := by
      funext ω
      rw [ENNReal.tsum_toReal_eq fun k => ENNReal.ofReal_ne_top]
      exact tsum_congr fun k => (ENNReal.toReal_ofReal (hX k ω)).symm
    rw [heq]
    exact (AEMeasurable.tsum fun k =>
      ENNReal.measurable_ofReal.comp_aemeasurable (h k).1).ennreal_toReal
  · calc ∫⁻ ω, φ (∑' k, X k ω) ∂P ≤ ∫⁻ ω, ⨆ s, F s ω ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsum] with ω hω
          exact le_of_tendsto' ((hφc.tendsto _).comp hω.hasSum)
            fun s => le_iSup (fun s => F s ω) s
      _ ≤ 2 := hsup

/-! ### Integrals -/

/-- Integrals: for a jointly measurable family `X(s) ≥ 0`, `s ∈ [0, T]`, with `X(s) ≤ 𝒪_q(A)`
for every `s ∈ [0, T]`, almost every realization `s ↦ X(s)` is integrable on `[0, T]` and
`∫_0^T X(s) ds ≤ 𝒪_q(T A)`. -/
theorem isOq_intervalIntegral [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0)
    {X : ℝ → Ω → ℝ} (hXm : Measurable (Function.uncurry X)) {T A : ℝ} (hT : 0 < T)
    (hA : 0 < A) (hX : ∀ s ∈ Icc 0 T, ∀ ω, 0 ≤ X s ω)
    (h : ∀ s ∈ Icc 0 T, IsOq P q (X s) A) :
    (∀ᵐ ω ∂P, IntegrableOn (fun s => X s ω) (Icc 0 T)) ∧
      IsOq P q (fun ω => ∫ s in (0)..T, X s ω) (T * A) := by
  set I := Icc (0 : ℝ) T with hI
  set Φ : ℝ → Ω → ℝ≥0∞ := fun s ω => ENNReal.ofReal (Real.exp ((max (X s ω) 0 / A) ^ q))
    with hΦ
  have hΦm : Measurable (Function.uncurry Φ) :=
    (continuous_oqIntegrand q A).measurable.comp hXm
  have hΦm' : Measurable fun p : Ω × ℝ => Φ p.2 p.1 := hΦm.comp measurable_swap
  have hvol : volume I = ENNReal.ofReal T := by rw [hI, Real.volume_Icc, sub_zero]
  have htot : ∫⁻ ω, (∫⁻ s in I, Φ s ω) ∂P ≤ 2 * ENNReal.ofReal T := by
    rw [lintegral_lintegral_swap hΦm'.aemeasurable]
    calc ∫⁻ s in I, ∫⁻ ω, Φ s ω ∂P ≤ ∫⁻ _ in I, 2 :=
          setLIntegral_mono' measurableSet_Icc fun s hs => (h s hs).2
      _ = 2 * ENNReal.ofReal T := by rw [setLIntegral_const, hvol]
  have hinner : Measurable fun ω => ∫⁻ s in I, Φ s ω := hΦm'.lintegral_prod_right'
  have hfin : ∀ᵐ ω ∂P, ∫⁻ s in I, Φ s ω < ∞ :=
    ae_lt_top' hinner.aemeasurable
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top) htot)
  have hXs : ∀ ω, Measurable fun s => X s ω := fun ω =>
    hXm.comp (measurable_id.prodMk measurable_const)
  have hΦs : ∀ ω, Measurable fun s => Φ s ω := fun ω =>
    hΦm.comp (measurable_id.prodMk measurable_const)
  have hgi : ∀ ω, ∫⁻ s in I, Φ s ω < ∞ →
      IntegrableOn (fun s => Real.exp ((X s ω / A) ^ q)) I := by
    intro ω hω
    have hi : IntegrableOn (fun s => (Φ s ω).toReal) I :=
      integrable_toReal_of_lintegral_ne_top (hΦs ω).aemeasurable hω.ne
    refine hi.congr_fun (fun s hs => ?_) measurableSet_Icc
    simp only [hΦ, max_eq_left (hX s hs ω)]
    exact ENNReal.toReal_ofReal (Real.exp_pos _).le
  have hint : ∀ ω, ∫⁻ s in I, Φ s ω < ∞ → IntegrableOn (fun s => X s ω) I := by
    intro ω hω
    refine ((hgi ω hω).const_mul A).mono' (hXs ω).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hX s hs ω)]
    have h0 : 0 ≤ X s ω / A := div_nonneg (hX s hs ω) hA.le
    calc X s ω = A * (X s ω / A) := by field_simp
      _ ≤ A * Real.exp ((X s ω / A) ^ q) :=
        mul_le_mul_of_nonneg_left (le_exp_pow hq h0) hA.le
  refine ⟨hfin.mono fun ω hω => hint ω hω, ?_, ?_⟩
  · have hm : StronglyMeasurable fun ω => ∫ s, X s ω ∂(volume.restrict (Ioc 0 T)) :=
      (hXm.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    refine hm.measurable.aemeasurable.congr (Eventually.of_forall fun ω => ?_)
    exact (intervalIntegral.integral_of_le hT.le).symm
  · have hpt : ∀ ω, ∫⁻ s in I, Φ s ω < ∞ →
        ENNReal.ofReal (Real.exp ((max (∫ s in (0)..T, X s ω) 0 / (T * A)) ^ q)) ≤
          ENNReal.ofReal T⁻¹ * ∫⁻ s in I, Φ s ω := by
      intro ω hω
      have hpos : 0 ≤ ∫ s in (0)..T, X s ω :=
        intervalIntegral.integral_nonneg hT.le fun s hs => hX s hs ω
      have hJ : Real.exp ((⨍ s in I, X s ω / A) ^ q) ≤
          ⨍ s in I, Real.exp ((X s ω / A) ^ q) :=
        (convexOn_exp_pow q).map_set_average_le (μ := volume) (t := I)
          (f := fun s => X s ω / A) (Real.continuous_exp.comp (continuous_pow q)).continuousOn
          isClosed_Ici (by rw [hvol]; exact ENNReal.ofReal_ne_zero_iff.mpr hT)
          (by rw [hvol]; exact ENNReal.ofReal_ne_top)
          ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun s hs =>
            div_nonneg (hX s hs ω) hA.le))
          ((hint ω hω).div_const A) (hgi ω hω)
      have hvr : volume.real I = T := by
        rw [measureReal_def, hvol, ENNReal.toReal_ofReal hT.le]
      have hav1 : ⨍ s in I, X s ω / A = (∫ s in (0)..T, X s ω) / (T * A) := by
        rw [setAverage_eq, hvr, integral_div, intervalIntegral.integral_of_le hT.le,
          integral_Icc_eq_integral_Ioc, smul_eq_mul]
        field_simp
      have hav2 : ⨍ s in I, Real.exp ((X s ω / A) ^ q) =
          T⁻¹ * (∫⁻ s in I, Φ s ω).toReal := by
        rw [setAverage_eq, hvr, smul_eq_mul, integral_eq_lintegral_of_nonneg_ae
          (Eventually.of_forall fun s => (Real.exp_pos _).le)
          (hgi ω hω).aestronglyMeasurable]
        congr 2
        refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        simp only [hΦ, max_eq_left (hX s hs ω)]
      rw [hav1, hav2] at hJ
      rw [max_eq_left hpos]
      calc ENNReal.ofReal (Real.exp (((∫ s in (0)..T, X s ω) / (T * A)) ^ q))
          ≤ ENNReal.ofReal (T⁻¹ * (∫⁻ s in I, Φ s ω).toReal) := ENNReal.ofReal_le_ofReal hJ
        _ = ENNReal.ofReal T⁻¹ * ∫⁻ s in I, Φ s ω := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hT.le), ENNReal.ofReal_toReal hω.ne]
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (∫ s in (0)..T, X s ω) 0 / (T * A)) ^ q)) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal T⁻¹ * (∫⁻ s in I, Φ s ω) ∂P :=
          lintegral_mono_ae (hfin.mono fun ω hω => hpt ω hω)
      _ = ENNReal.ofReal T⁻¹ * ∫⁻ ω, (∫⁻ s in I, Φ s ω) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal T⁻¹ * (2 * ENNReal.ofReal T) := by gcongr
      _ = 2 := by
          rw [mul_left_comm, ← ENNReal.ofReal_mul (inv_nonneg.mpr hT.le),
            inv_mul_cancel₀ hT.ne', ENNReal.ofReal_one, mul_one]

end

end LongRangeHeat
