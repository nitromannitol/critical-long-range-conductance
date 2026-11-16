import LongRangeHeat.Energy
import LongRangeHeat.LatticeSemigroup
import LongRangeHeat.GaussianTails
import LongRangeHeat.SampledForcing

/-!
# Bounds for the heat-equation homogenization estimate

Cauchy–Schwarz and stochastic integral bounds for the deterministic energy estimate.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LatticeProb.Heat LatticeProb.WhiteNoise LongRange MeasureTheory Set Filter
open scoped Interval ContDiff Topology

private theorem normSq_nonneg {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : Site d → ℝ) :
    0 ≤ latticeNormSq ε f := by
  unfold latticeNormSq
  exact mul_nonneg (pow_nonneg hε _) (tsum_nonneg fun q => sq_nonneg _)

/-- The rescaled lattice pairing satisfies Cauchy–Schwarz. -/
theorem abs_latticeInner_le {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {f g : Site d → ℝ}
    (hf : MemL2 f) (hg : MemL2 g) :
    |latticeInner ε f g| ≤ latticeNorm ε f * latticeNorm ε g := by
  have he : 0 ≤ ε ^ d := pow_nonneg hε _
  have hs := summable_mul_of_memL2 hf hg
  unfold latticeInner
  rw [abs_mul, abs_of_nonneg he]
  calc
    _ ≤ ε ^ d * ∑' q, |f q| * |g q| := by
      apply mul_le_mul_of_nonneg_left _ he
      simpa only [Real.norm_eq_abs, abs_mul] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ _ := pow_mul_tsum_abs_mul_le hε hf hg

/-- The field pairing is bounded by the field and gradient norms. -/
theorem abs_forcing_pair_le {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {v : Site d → ℝ} (hv : MemL2 v)
    (F : Fin d → Site d → ℝ) (hF : ∀ i, MemL2 (F i)) :
    |∑ i, latticeInner ε (F i) (discreteDeriv ε i v)| ≤
      Real.sqrt (∑ i, latticeNormSq ε (F i)) * Real.sqrt (gradNormSq ε v) := by
  calc
    _ ≤ ∑ i, |latticeInner ε (F i) (discreteDeriv ε i v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, latticeNorm ε (F i) * latticeNorm ε (discreteDeriv ε i v) := by
      apply Finset.sum_le_sum
      intro i hi
      exact abs_latticeInner_le hε (hF i) (memL2_discreteDeriv hv ε i)
    _ ≤ Real.sqrt (∑ i, latticeNorm ε (F i) ^ 2) *
        Real.sqrt (∑ i, latticeNorm ε (discreteDeriv ε i v) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp only [latticeNorm, Real.sq_sqrt (normSq_nonneg hε _), gradNormSq]

/-- A forcing representation yields the corresponding norm bound. -/
theorem forcing_pair_le_of_representation {d : ℕ} {ε κ A : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ)
    {p v : Site d → ℝ} (_hp : MemL2 p) (hv : MemL2 v)
    (F : Fin d → Site d → ℝ) (hF : ∀ i, MemL2 (F i))
    (hrep : |latticeInner ε p v - κ⁻¹ *
      ∑ i, latticeInner ε (F i) (discreteDeriv ε i v)| ≤ A / κ * latticeNorm ε v) :
    |latticeInner ε p v| ≤ A / κ * latticeNorm ε v +
      Real.sqrt (∑ i, latticeNormSq ε (F i)) * Real.sqrt (gradNormSq ε v) / κ := by
  have hc := abs_forcing_pair_le hε hv F hF
  have hsum : |κ⁻¹ * ∑ i, latticeInner ε (F i) (discreteDeriv ε i v)| ≤
      Real.sqrt (∑ i, latticeNormSq ε (F i)) * Real.sqrt (gradNormSq ε v) / κ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hκ), div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hκ.le)]
  have htriangle := abs_add_le (latticeInner ε p v - κ⁻¹ *
      ∑ i, latticeInner ε (F i) (discreteDeriv ε i v))
      (κ⁻¹ * ∑ i, latticeInner ε (F i) (discreteDeriv ε i v))
  have heq : latticeInner ε p v - κ⁻¹ *
      (∑ i, latticeInner ε (F i) (discreteDeriv ε i v)) + κ⁻¹ *
      (∑ i, latticeInner ε (F i) (discreteDeriv ε i v)) = latticeInner ε p v := by ring
  rw [heq] at htriangle
  linarith

/-- Integrating squared Gaussian tails controls the square root of the integral. -/
theorem isOq_sqrt_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {H : ℝ → Ω → ℝ} (hH : ∀ s r, 0 ≤ H s r)
    (hm : Measurable (Function.uncurry H)) {T C : ℝ} (hT : 0 < T) (hC : 0 < C)
    (hO : ∀ s ∈ Set.Icc 0 T, IsOq P 2 (H s) C) :
    (∀ᵐ r ∂P, IntegrableOn (fun s => H s r ^ 2) (Set.Icc 0 T)) ∧
      IsOq P 2 (fun r => Real.sqrt (∫ s in (0 : ℝ)..T, H s r ^ 2))
        (Real.sqrt (T * C ^ 2)) := by
  have hm' : Measurable (Function.uncurry fun s r => H s r ^ 2) := hm.pow_const 2
  have hs : ∀ s ∈ Set.Icc 0 T, IsOq P 1 (fun r => H s r ^ 2) (C ^ 2) :=
    fun s hs => (isOq_two_iff (hH s) C).mp (hO s hs)
  have hi := isOq_intervalIntegral (P := P) (q := 1) (by decide) hm' hT
    (sq_pos_of_pos hC) (fun s hs r => sq_nonneg _) hs
  refine ⟨hi.1, ?_⟩
  have hnonneg : ∀ r, 0 ≤ ∫ s in (0 : ℝ)..T, H s r ^ 2 := fun r =>
    intervalIntegral.integral_nonneg_of_forall hT.le (fun _ => sq_nonneg _)
  apply (isOq_two_iff (fun r => Real.sqrt_nonneg _) (Real.sqrt (T * C ^ 2))).mpr
  simpa only [Real.sq_sqrt (mul_nonneg hT.le (sq_nonneg C)), Real.sq_sqrt (hnonneg _)] using hi.2

/-- The sum of nonnegative variables with exponential bounds has the summed scale. -/
theorem isOq_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q : ℕ} (hq : q ≠ 0) {X Y : Ω → ℝ} {A B : ℝ}
    (hX0 : ∀ r, 0 ≤ X r) (hY0 : ∀ r, 0 ≤ Y r) (hA : 0 < A) (hB : 0 < B)
    (hX : IsOq P q X A) (hY : IsOq P q Y B) :
    IsOq P q (fun r => X r + Y r) (A + B) := by
  let F : Fin 2 → Ω → ℝ := ![X, Y]
  let C : Fin 2 → ℝ := ![A, B]
  have hF0 : ∀ i r, 0 ≤ F i r := by
    intro i r
    fin_cases i
    · exact hX0 r
    · exact hY0 r
  have hC : ∀ i, 0 < C i := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  have hF : ∀ i, IsOq P q (F i) (C i) := by
    intro i
    fin_cases i
    · exact hX
    · exact hY
  refine ⟨hX.1.add hY.1, ?_⟩
  have hh := lintegral_finsetSum_le_two (P := P) hq hF0 hC hF Finset.univ
    (show ∑ i, C i ≤ A + B by simp [C, Fin.sum_univ_two])
  simpa only [F, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

/-- An almost everywhere smaller measurable variable has the same exponential bound. -/
theorem isOq_of_ae_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {q : ℕ}
    {X Y : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hY : AEMeasurable Y P)
    (hYX : ∀ᵐ r ∂P, Y r ≤ X r) (hX : IsOq P q X A) : IsOq P q Y A := by
  refine ⟨hY, (lintegral_mono_ae (hYX.mono fun r hr => ?_)).trans hX.2⟩
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply pow_le_pow_left₀ (div_nonneg (le_max_right _ _) hA.le) _ q
  exact div_le_div_of_nonneg_right (max_le_max hr le_rfl) hA.le

/-- The generator applied to a measurable lattice field is measurable at each site. -/
theorem measurable_generator {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (a : Ω → Edge d → ℝ) (ha : ∀ e, Measurable fun r => a r e)
    (v : Ω → Site d → ℝ) (hv : ∀ q, Measurable fun r => v r q) (q : Site d) :
    Measurable (fun r => generator ε (a r) (v r) q) := by
  unfold generator
  refine measurable_const.mul (Measurable.tsum fun w => ?_)
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte]
    exact measurable_const
  · simp only [hw, ↓reduceDIte]
    exact (((ha _).mul ((hv _).sub (hv _))).mul measurable_const)

/-- The lattice heat solution at a fixed time and site is measurable in the conductances. -/
theorem measurable_latticeHeat {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (a : Ω → Edge d → ℝ) (ha : ∀ e, Measurable fun r => a r e)
    (f : (Fin d → ℝ) → ℝ) (t : ℝ) (q : Site d) :
    Measurable (fun r => latticeHeat ε (a r) f t q) := by
  have hi : ∀ n : ℕ, ∀ q, Measurable (fun r => (generator ε (a r))^[n] (restrict ε f) q) := by
    intro n
    induction n with
    | zero => intro q; exact measurable_const
    | succ n ih =>
      intro q
      simp only [Function.iterate_succ_apply']
      exact measurable_generator ε a ha _ ih q
  unfold latticeHeat
  exact Measurable.tsum fun n => measurable_const.mul (hi n q)

/-- At a fixed time, the lattice error norm is measurable in the conductances. -/
theorem measurable_latticeHeat_error_norm {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (a : Ω → Edge d → ℝ) (ha : ∀ e, Measurable fun r => a r e)
    (f : (Fin d → ℝ) → ℝ) (t : ℝ) :
    Measurable (fun r => latticeNorm ε
      (fun q => latticeHeat ε (a r) f t q - restrict ε (continuumHeat f t) q)) := by
  unfold latticeNorm latticeNormSq
  apply Measurable.sqrt
  exact measurable_const.mul (Measurable.tsum fun q =>
    ((measurable_latticeHeat ε a ha f t q).sub measurable_const).pow_const 2)

/-- The forcing field is jointly measurable in time and the conductances. -/
theorem measurable_forcingField {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (a : Ω → Edge d → ℝ) (ha : ∀ e, Measurable fun r => a r e)
    (g : ℝ → Site d → ℝ) (hg : ∀ q, Measurable fun t => g t q)
    (i : Fin d) (y : Site d) :
    Measurable (fun p : ℝ × Ω => forcingField ε (a p.2) (g p.1) i y) := by
  unfold forcingField
  refine measurable_const.mul (Finset.measurable_fun_sum _ fun w hw => ?_)
  refine measurable_const.mul (Finset.measurable_fun_sum _ fun x hx => ?_)
  unfold centeredIncrement
  by_cases hz : w = 0
  · simp only [hz, ↓reduceDIte]
    exact measurable_const
  · simp only [hz, ↓reduceDIte]
    exact (((ha _).comp measurable_snd).sub measurable_const).mul
      (((hg _).comp measurable_fst).sub ((hg _).comp measurable_fst))

/-- The lattice norm of the forcing field is jointly measurable. -/
theorem measurable_forcingFieldNorm {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ)
    (a : Ω → Edge d → ℝ) (ha : ∀ e, Measurable fun r => a r e)
    (g : ℝ → Site d → ℝ) (hg : ∀ q, Measurable fun t => g t q) :
    Measurable (fun p : ℝ × Ω => Real.sqrt (∑ i, latticeNormSq ε
      (forcingField ε (a p.2) (g p.1) i))) := by
  apply Measurable.sqrt
  apply Finset.measurable_fun_sum
  intro i hi
  unfold latticeNormSq
  exact measurable_const.mul (Measurable.tsum fun q =>
    (measurable_forcingField ε a ha g hg i q).pow_const 2)

/-- The continuum heat solution is continuous in nonnegative time at each point. -/
theorem continuousOn_continuumHeat_time {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : Fin d → ℝ) : ContinuousOn (fun t => continuumHeat f t x) (Set.Ici 0) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact (hasDerivWithinAt_continuumHeat_zero hd hf hfc x).continuousWithinAt
  · exact (hasDerivAt_continuumHeat hd hf hfc (lt_of_le_of_ne ht (Ne.symm ht0)) x).continuousAt.continuousWithinAt

/-- Each coordinate of the lattice error is continuous at nonnegative times. -/
theorem continuousOn_latticeHeat_error {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (q : Site d) : ContinuousOn (fun t => latticeHeat ε a f t q -
      restrict ε (continuumHeat f t) q) (Set.Ici 0) := by
  apply ContinuousOn.sub
  · exact (show Differentiable ℝ (fun t => latticeHeat ε a f t q) from fun t =>
      (hasDerivAt_latticeHeat hd hε hlam ha hfc t q).differentiableAt).continuous.continuousOn
  · exact continuousOn_continuumHeat_time hd hf hfc (physical ε q)

/-- The coordinate derivative of the lattice error at positive times. -/
theorem hasDerivAt_latticeHeat_error {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 < t) (q : Site d) :
    HasDerivAt (fun s => latticeHeat ε a f s q - restrict ε (continuumHeat f s) q)
      (generator ε a (latticeHeat ε a f t) q - contOp d (continuumHeat f t) (physical ε q)) t := by
  exact (hasDerivAt_latticeHeat hd hε hlam ha hfc t q).sub
    (hasDerivAt_continuumHeat hd hf hfc ht (physical ε q))

/-- The lattice heat path and its time derivative have uniform square-sum bounds on bounded
intervals. -/
theorem exists_latticeHeat_uniform_l2_bounds {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hfc : HasCompactSupport f) (T : ℝ) :
    ∃ R S : ℝ, ∀ t ∈ Set.Icc 0 T,
      (∑' q, latticeHeat ε a f t q ^ 2) ≤ R ∧
      (∑' q, generator ε a (latticeHeat ε a f t) q ^ 2) ≤ S := by
  let U := fun t => latticeHeatL2 hd hε hlam ha hfc t
  let A := generatorL2 hd hε hlam ha
  have hc : Continuous U := (show Differentiable ℝ U from fun t =>
    (hasDerivAt_latticeHeatL2 hd hε hlam ha hfc t).differentiableAt).continuous
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn (A.continuous.comp hc).continuousOn
  have hnorm (v : lp (fun _ : Site d => ℝ) 2) : ‖v‖ ^ 2 = ∑' q, v q ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) v
    simpa [Real.norm_eq_abs, Real.rpow_two] using h
  refine ⟨R ^ 2, S ^ 2, fun t ht => ⟨?_, ?_⟩⟩
  · change (∑' q, U t q ^ 2) ≤ R ^ 2
    rw [← hnorm]
    have h := hR t ht
    nlinarith [norm_nonneg (U t)]
  · change (∑' q, A (U t) q ^ 2) ≤ S ^ 2
    rw [← hnorm]
    have h := hS t ht
    change ‖A (U t)‖ ≤ S at h
    nlinarith [norm_nonneg (A (U t))]

/-- Sampling a compactly supported continuous function evolved by the continuum heat flow gives
uniform square-sum bounds on nonnegative time. -/
theorem exists_sampledHeat_uniform_l2_bound {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ R : ℝ, ∀ t : ℝ, 0 ≤ t →
      MemL2 (restrict ε (continuumHeat f t)) ∧
      (∑' q, restrict ε (continuumHeat f t) q ^ 2) ≤ R := by
  obtain ⟨C, hC⟩ := exists_sum_sq_continuumHeat_le hd hf hfc
  refine ⟨C / ε ^ d, fun t ht => ?_⟩
  have h := hC ε hε hε1 t ht 0
  simp only [add_zero] at h
  refine ⟨h.1, ?_⟩
  rw [le_div_iff₀ (pow_pos hε d)]
  simpa only [restrict, mul_comm] using h.2

/-- The continuum heat solution is measurable in time at each point. -/
theorem measurable_continuumHeat_time {d : ℕ} (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (x : Fin d → ℝ) : Measurable (fun t => continuumHeat f t x) := by
  have hz : ∀ t < 0, continuumHeat f t x = 0 := by
    intro t ht
    unfold continuumHeat
    rw [ite_eq_right (ne_of_lt ht)]
    simp only [heatKernel_of_nonpos ht.le, zero_mul, integral_zero]
  apply measurable_of_measurable_on_compl_singleton 0
  apply Continuous.measurable
  rw [← continuousOn_iff_continuous_domRestrict]
  intro t ht
  have hne : t ≠ 0 := by simpa using ht
  rcases lt_or_gt_of_ne hne with hn | hp
  · have he : (fun s => continuumHeat f s x) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
      (show ∀ᶠ s in 𝓝 t, s < 0 from Iio_mem_nhds hn).mono (fun s hs => hz s hs)
    exact (continuousAt_const.congr he.symm).continuousWithinAt
  · exact (hasDerivAt_continuumHeat hd hf hfc hp x).continuousAt.continuousWithinAt

/-- The coordinate derivative of the lattice error is measurable in time. -/
theorem measurable_latticeHeat_error_derivative_time {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (q : Site d) :
    Measurable (fun t => generator ε a (latticeHeat ε a f t) q -
      restrict ε (continuumHeat (contOp d f) t) q) := by
  have hm (q : Site d) : Measurable (fun t => latticeHeat ε a f t q) :=
    (show Differentiable ℝ (fun t => latticeHeat ε a f t q) from fun t =>
      (hasDerivAt_latticeHeat hd hε hlam ha hfc t q).differentiableAt).continuous.measurable
  apply Measurable.sub
  · exact measurable_generator ε (fun _ : ℝ => a) (fun _ => measurable_const)
      (fun t => latticeHeat ε a f t) hm q
  · exact measurable_continuumHeat_time hd (contDiff_contOp hf) (hasCompactSupport_contOp hf hfc)
      (physical ε q)

/-- The time-integrated forcing field has Gaussian tails. -/
theorem sampled_forcing_integral_isOq {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ),
      ConductanceLaw P lam a → ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ T : ℝ, 0 < T →
      (∀ᵐ r ∂P, IntegrableOn (fun s => (Real.sqrt (∑ i, latticeNormSq ε
        (forcingField ε (a r) (restrict ε (continuumHeat f s)) i))) ^ 2) (Set.Icc 0 T)) ∧
      IsOq P 2 (fun r => Real.sqrt (∫ s in (0 : ℝ)..T,
        (Real.sqrt (∑ i, latticeNormSq ε
          (forcingField ε (a r) (restrict ε (continuumHeat f s)) i))) ^ 2))
        (Real.sqrt T * C) := by
  obtain ⟨C, hCpos, hC⟩ := forcingField_gaussian_tails_sampled hd hf hfc hlam
  refine ⟨C, hCpos, ?_⟩
  intro Ω _ P a hA ε hε T hT
  let : IsProbabilityMeasure P := hA.isProbabilityMeasure
  let H : ℝ → Ω → ℝ := fun s r => Real.sqrt (∑ i, latticeNormSq ε
    (forcingField ε (a r) (restrict ε (continuumHeat f s)) i))
  have hm : Measurable (Function.uncurry H) := by
    exact measurable_forcingFieldNorm ε a hA.measurable
      (fun s => restrict ε (continuumHeat f s))
      (fun q => measurable_continuumHeat_time hd hf hfc (physical ε q))
  have hO : ∀ s ∈ Set.Icc 0 T, IsOq P 2 (H s) C := fun s hs =>
    (hC Ω P a hA ε hε s hs.1).2
  have hi := isOq_sqrt_integral P (H := H) (fun _ _ => Real.sqrt_nonneg _)
    hm hT hCpos hO
  refine ⟨hi.1, ?_⟩
  have hscale : Real.sqrt (T * C ^ 2) = Real.sqrt T * C := by
    rw [Real.sqrt_mul hT.le, Real.sqrt_sq hCpos.le]
  rw [← hscale]
  exact hi.2

/-- Uniform ℓ² bounds imply time integrability of the energy summands. -/
theorem intervalIntegrable_energy_of_uniform_l2_bounds {d : ℕ} (ε : ℝ) (w w' : ℝ → Site d → ℝ) {T R S : ℝ} (hT : 0 ≤ T)
    (hwm : ∀ q, Measurable (fun t => w t q))
    (hw'm : ∀ q, Measurable (fun t => w' t q))
    (hw : ∀ t ∈ Set.Icc 0 T, MemL2 (w t))
    (hw' : ∀ t ∈ Set.Icc 0 T, MemL2 (w' t))
    (hwb : ∀ t ∈ Set.Icc 0 T, (∑' q, w t q ^ 2) ≤ R)
    (hw'b : ∀ t ∈ Set.Icc 0 T, (∑' q, w' t q ^ 2) ≤ S) :
    IntervalIntegrable (fun t => ∑' q, |2 * w t q * w' t q|) volume 0 T ∧
      (∀ q, IntervalIntegrable (fun t => 2 * w t q * w' t q) volume 0 T) ∧
      IntervalIntegrable (fun t => 2 * latticeInner ε (w t) (w' t)) volume 0 T := by
  let C := 2 * Real.sqrt R * Real.sqrt S
  have hm (q : Site d) : Measurable (fun t => 2 * w t q * w' t q) :=
    (measurable_const.mul (hwm q)).mul (hw'm q)
  have hs (t : ℝ) (ht : t ∈ Set.Icc 0 T) : Summable (fun q => |2 * w t q * w' t q|) := by
    have h := ((summable_mul_of_memL2 (hw t ht) (hw' t ht)).mul_left 2).norm
    simpa only [Real.norm_eq_abs, mul_assoc] using h
  have hbound (t : ℝ) (ht : t ∈ Set.Icc 0 T) : (∑' q, |2 * w t q * w' t q|) ≤ C := by
    have h := tsum_abs_mul_le (hw t ht) (hw' t ht)
    have hR' := Real.sqrt_le_sqrt (hwb t ht)
    have hS' := Real.sqrt_le_sqrt (hw'b t ht)
    have hprod := mul_le_mul hR' hS' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc
      _ = 2 * ∑' q, |w t q| * |w' t q| := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        simp_rw [mul_assoc]
        rw [tsum_mul_left]
      _ ≤ 2 * (Real.sqrt (∑' q, w t q ^ 2) * Real.sqrt (∑' q, w' t q ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ C := by dsimp [C]; nlinarith
  have habsM : Measurable (fun t => ∑' q, |2 * w t q * w' t q|) :=
    Measurable.tsum fun q => (hm q).abs
  have hi : IntegrableOn (fun t => ∑' q, |2 * w t q * w' t q|) (Set.Icc 0 T) := by
    apply IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) habsM.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun q => abs_nonneg _)]
    exact hbound t ht
  have hiq : ∀ q, IntervalIntegrable (fun t => 2 * w t q * w' t q) volume 0 T := by
    intro q
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
    apply IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      (hm q).aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact ((hs t ht).le_tsum q (fun _ _ => abs_nonneg _)).trans (hbound t ht)
  have hinnerM : Measurable (fun t => 2 * latticeInner ε (w t) (w' t)) := by
    unfold latticeInner
    exact measurable_const.mul (measurable_const.mul
      (Measurable.tsum fun q => (hwm q).mul (hw'm q)))
  have hinner : IntegrableOn (fun t => 2 * latticeInner ε (w t) (w' t)) (Set.Icc 0 T) := by
    apply IntegrableOn.of_bound (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      hinnerM.aestronglyMeasurable (|ε ^ d| * C)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hsum : Summable (fun q => 2 * w t q * w' t q) := by
      have h := (summable_mul_of_memL2 (hw t ht) (hw' t ht)).mul_left 2
      simpa only [mul_assoc] using h
    have heq : 2 * latticeInner ε (w t) (w' t) = ε ^ d * ∑' q, 2 * w t q * w' t q := by
      unfold latticeInner
      simp_rw [mul_assoc]
      rw [tsum_mul_left]
      ring
    rw [Real.norm_eq_abs, heq, abs_mul]
    calc
      _ ≤ |ε ^ d| * ∑' q, |2 * w t q * w' t q| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg _)
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hi, hiq,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hinner⟩

/-- The generator is additive on square-summable lattice functions. -/
theorem generator_sub_of_memL2 {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {u v : Site d → ℝ} (hu : MemL2 u) (hv : MemL2 v) (q : Site d) :
    generator ε a (fun x => u x - v x) q = generator ε a u q - generator ε a v q := by
  have hm (w : Site d → ℝ) (hw : MemL2 w) : Memℓp w 2 := by
    apply memℓp_gen
    simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using hw
  let U : lp (fun _ : Site d => ℝ) 2 := ⟨u, hm u hu⟩
  let V : lp (fun _ : Site d => ℝ) 2 := ⟨v, hm v hv⟩
  have h := congrArg (fun z : lp (fun _ : Site d => ℝ) 2 => z q)
    ((generatorL2 hd hε hlam ha).map_sub U V)
  change generator ε a (fun x => u x - v x) q = generator ε a u q - generator ε a v q at h
  exact h

/-- The square sum of a difference is controlled by the two square sums. -/
theorem tsum_sq_sub_le {d : ℕ} {u v : Site d → ℝ} (hu : MemL2 u) (hv : MemL2 v) :
    (∑' q, (u q - v q) ^ 2) ≤ 2 * ((∑' q, u q ^ 2) + ∑' q, v q ^ 2) := by
  have h := Summable.tsum_le_tsum (fun q : Site d => show (u q - v q) ^ 2 ≤
      2 * (u q ^ 2 + v q ^ 2) by nlinarith [sq_nonneg (u q + v q)])
    (memL2_sub hu hv) ((hu.add hv).mul_left 2)
  simpa only [tsum_mul_left, hu.tsum_add hv] using h

/-- The error and its time derivative have uniform square-sum bounds. -/
theorem exists_latticeHeat_error_uniform_l2_bounds {d : ℕ} (hd : 1 ≤ d) {ε lam T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ R S : ℝ, ∀ t ∈ Icc 0 T,
      (∑' q, (latticeHeat ε a f t q - restrict ε (continuumHeat f t) q) ^ 2) ≤ R ∧
      (∑' q, (generator ε a (latticeHeat ε a f t) q -
        restrict ε (continuumHeat (contOp d f) t) q) ^ 2) ≤ S := by
  obtain ⟨R, S, hRS⟩ := exists_latticeHeat_uniform_l2_bounds hd hε hlam ha hfc T
  obtain ⟨P, hP⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1 hf.continuous hfc
  obtain ⟨Q, hQ⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1
    (contDiff_contOp hf).continuous (hasCompactSupport_contOp hf hfc)
  refine ⟨2 * (R + P), 2 * (S + Q), fun t ht => ⟨?_, ?_⟩⟩
  · have h := tsum_sq_sub_le (memL2_latticeHeat hd hε hlam ha hfc t) (hP t ht.1).1
    nlinarith [(hRS t ht).1, (hP t ht.1).2]
  · have h := tsum_sq_sub_le (memL2_generator hd hε hlam ha
      (memL2_latticeHeat hd hε hlam ha hfc t)) (hQ t ht.1).1
    nlinarith [(hRS t ht).2, (hQ t ht.1).2]

/-- The lattice-error energy summands are integrable on bounded time intervals. -/
theorem intervalIntegrable_latticeHeat_error_energy {d : ℕ} (hd : 1 ≤ d) {ε lam T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam) (hT : 0 ≤ T) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    let w := fun t q => latticeHeat ε a f t q - restrict ε (continuumHeat f t) q
    let w' := fun t q => generator ε a (latticeHeat ε a f t) q -
      restrict ε (continuumHeat (contOp d f) t) q
    IntervalIntegrable (fun t => ∑' q, |2 * w t q * w' t q|) volume 0 T ∧
      (∀ q, IntervalIntegrable (fun t => 2 * w t q * w' t q) volume 0 T) ∧
      IntervalIntegrable (fun t => 2 * latticeInner ε (w t) (w' t)) volume 0 T := by
  dsimp only
  obtain ⟨R, S, hRS⟩ := exists_latticeHeat_error_uniform_l2_bounds hd hε hε1 hlam ha hf hfc
  obtain ⟨P, hP⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1 hf.continuous hfc
  obtain ⟨Q, hQ⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1
    (contDiff_contOp hf).continuous (hasCompactSupport_contOp hf hfc)
  apply intervalIntegrable_energy_of_uniform_l2_bounds ε _ _ hT
  · intro q
    apply Measurable.sub
    · exact (show Differentiable ℝ (fun t => latticeHeat ε a f t q) from fun t =>
        (hasDerivAt_latticeHeat hd hε hlam ha hfc t q).differentiableAt).continuous.measurable
    · exact measurable_continuumHeat_time hd hf hfc (physical ε q)
  · intro q
    exact measurable_latticeHeat_error_derivative_time hd hε hlam ha hf hfc q
  · intro t ht
    exact memL2_sub (memL2_latticeHeat hd hε hlam ha hfc t) (hP t ht.1).1
  · intro t ht
    exact memL2_sub (memL2_generator hd hε hlam ha
      (memL2_latticeHeat hd hε hlam ha hfc t)) (hQ t ht.1).1
  · intro t ht
    exact (hRS t ht).1
  · intro t ht
    exact (hRS t ht).2

/-- The lattice error satisfies the mean and random forcing decomposition. -/
theorem latticeHeat_error_evolution {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 ≤ t) (q : Site d) :
    generator ε a (latticeHeat ε a f t) q - restrict ε (continuumHeat (contOp d f) t) q =
      generator ε a (fun q => latticeHeat ε a f t q - restrict ε (continuumHeat f t) q) q -
        (contOp d (continuumHeat f t) (physical ε q) -
          meanGenerator ε (restrict ε (continuumHeat f t)) q) -
        (meanGenerator ε (restrict ε (continuumHeat f t)) q -
          generator ε a (restrict ε (continuumHeat f t)) q) := by
  obtain ⟨P, hP⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1 hf.continuous hfc
  rw [generator_sub_of_memL2 hd hε hlam ha (memL2_latticeHeat hd hε hlam ha hfc t)
    (hP t ht).1, contOp_continuumHeat hd hf hfc ht]
  unfold LongRangeHeat.restrict
  ring

/-- The lattice energy estimate under uniform square-summability bounds. -/
theorem sSup_latticeNorm_le_of_uniform_l2_forcing {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (hκ : 0 < kappa d ε)
    (w w' p r : ℝ → Site d → ℝ) (G : ℝ → ℝ) {T A₁ A₂ R S : ℝ}
    (hT : 0 ≤ T) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hw0 : w 0 = 0)
    (hb : BddAbove ((fun t => latticeNorm ε (w t)) '' Set.Icc 0 T))
    (hw : ∀ t ∈ Set.Icc 0 T, MemL2 (w t))
    (hw' : ∀ t ∈ Set.Icc 0 T, MemL2 (w' t))
    (hwm : ∀ q, Measurable (fun t => w t q))
    (hw'm : ∀ q, Measurable (fun t => w' t q))
    (hwb : ∀ t ∈ Set.Icc 0 T, (∑' q, w t q ^ 2) ≤ R)
    (hw'b : ∀ t ∈ Set.Icc 0 T, (∑' q, w' t q ^ 2) ≤ S)
    (hc : ∀ q, ContinuousOn (fun t => w t q) (Set.Icc 0 T))
    (hdiff : ∀ q t, t ∈ Set.Ioo 0 T → HasDerivAt (fun s => w s q) (w' t q) t)
    (hGi : ∀ t ∈ Set.Icc 0 T, IntervalIntegrable (fun s => G s ^ 2) volume 0 t)
    (hs : ∀ t ∈ Set.Icc 0 T, MemL2 (p t) ∧ MemL2 (r t))
    (hode : ∀ t ∈ Set.Icc 0 T, ∀ q, w' t q = generator ε a (w t) q - p t q - r t q)
    (hmean : ∀ t ∈ Set.Icc 0 T, |latticeInner ε (p t) (w t)| ≤
      A₁ / kappa d ε * latticeNorm ε (w t))
    (hforce : ∀ t ∈ Set.Icc 0 T, |latticeInner ε (r t) (w t)| ≤
      A₂ / kappa d ε * latticeNorm ε (w t) +
        G t * Real.sqrt (gradNormSq ε (w t)) / kappa d ε) :
    sSup ((fun t => latticeNorm ε (w t)) '' Set.Icc 0 T) ≤
      2 * ((A₁ + A₂) / kappa d ε) * T +
        Real.sqrt (2 * (1 / (4 * (lam / 2) * kappa d ε)) * ∫ s in (0 : ℝ)..T, G s ^ 2) := by
  have hi := intervalIntegrable_energy_of_uniform_l2_bounds ε w w' hT hwm hw'm hw hw' hwb hw'b
  have hsub : ∀ t ∈ Set.Icc 0 T, Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    intro t ht
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hT]
    exact fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  apply sSup_latticeNorm_le_of_forcing_coordinates hd hε hlam ha hκ w w' p r G
    hT hA₁ hA₂ hw0 hb hw hw' hc hdiff
  · intro t ht q
    exact (hi.2.1 q).mono_set (hsub t ht)
  · intro t ht
    exact hi.1.mono_set (hsub t ht)
  · intro t ht
    exact hi.2.2.mono_set (hsub t ht)
  · exact hGi
  · exact hs
  · exact hode
  · exact hmean
  · exact hforce

/-- A bounded lattice norm supremum is measurable when coordinates are continuous in time
and measurable in the parameter. -/
theorem measurable_sSup_latticeNorm {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (w : ℝ → Ω → Site d → ℝ)
    (hwm : ∀ t q, Measurable fun r => w t r q)
    (hwc : ∀ r q, ContinuousOn (fun t => w t r q) (Icc 0 T))
    (hw : ∀ r t, t ∈ Icc 0 T → MemL2 (w t r))
    (hb : ∀ r, BddAbove ((fun t => latticeNorm ε (w t r)) '' Icc 0 T)) :
    Measurable (fun r => sSup ((fun t => latticeNorm ε (w t r)) '' Icc 0 T)) := by
  classical
  let I := Icc (0 : ℝ) T
  let : Nonempty I := ⟨⟨0, ⟨le_rfl, hT⟩⟩⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense I
  have hnm (t : I) : Measurable fun r => latticeNorm ε (w t r) := by
    unfold latticeNorm latticeNormSq
    exact (measurable_const.mul (Measurable.tsum fun q => (hwm t q).pow_const 2)).sqrt
  have hm := Measurable.sSup hDc fun t ht => hnm t
  convert hm using 1
  funext r
  let F : I → ℝ := fun t => latticeNorm ε (w t r)
  have hsub : F '' D ⊆ (fun t => latticeNorm ε (w t r)) '' I := by
    rintro y ⟨t, ht, rfl⟩
    exact ⟨t, t.2, rfl⟩
  have hbd : BddAbove (F '' D) := (hb r).mono hsub
  have hDn : D.Nonempty := hDd.nonempty
  have hA0 : 0 ≤ sSup (F '' D) := by
    obtain ⟨t, ht⟩ := hDn
    exact (Real.sqrt_nonneg _).trans (le_csSup hbd ⟨t, ht, rfl⟩)
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨0, ⟨le_rfl, hT⟩, rfl⟩⟩
    · rintro _ ⟨t, ht, rfl⟩
      apply (memL2_and_latticeNorm_le hε hA0 ?_).2
      intro S
      have hc : Continuous (fun x : I => ε ^ d * ∑ q ∈ S, w x r q ^ 2) := by
        apply continuous_const.mul
        apply continuous_finsetSum
        intro q hq
        exact ((hwc r q).domRestrict).pow 2
      have hclosed : IsClosed {x : I | ε ^ d * ∑ q ∈ S, w x r q ^ 2 ≤ (sSup (F '' D)) ^ 2} :=
        isClosed_le hc continuous_const
      have hD : D ⊆ {x : I | ε ^ d * ∑ q ∈ S, w x r q ^ 2 ≤ (sSup (F '' D)) ^ 2} := by
        intro x hx
        have hs : (∑ q ∈ S, w x r q ^ 2) ≤ ∑' q, w x r q ^ 2 :=
          (hw r x x.2).sum_le_tsum S (fun q hq => sq_nonneg _)
        have hn : (latticeNorm ε (w x r)) ^ 2 = ε ^ d * ∑' q, w x r q ^ 2 := by
          unfold latticeNorm latticeNormSq
          rw [Real.sq_sqrt (mul_nonneg (pow_nonneg hε.le _) (tsum_nonneg fun q => sq_nonneg _))]
        change ε ^ d * ∑ q ∈ S, w x r q ^ 2 ≤ (sSup (F '' D)) ^ 2
        calc
          _ ≤ (latticeNorm ε (w x r)) ^ 2 := by rw [hn]; exact mul_le_mul_of_nonneg_left hs (pow_nonneg hε.le _)
          _ ≤ _ := (sq_le_sq₀ (Real.sqrt_nonneg _) hA0).2 (le_csSup hbd ⟨x, hx, rfl⟩)
      have hall := closure_minimal hD hclosed
      rw [hDd.closure_eq] at hall
      exact hall (mem_univ ⟨t, ht⟩)
  · exact csSup_le (hDn.image F) (fun y hy => le_csSup (hb r) (hsub hy))

/-- The lattice error norms are uniformly bounded on a bounded time interval. -/
theorem bddAbove_latticeHeat_error {d : ℕ} (hd : 1 ≤ d) {ε lam T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    BddAbove ((fun t => latticeNorm ε
      (fun q => latticeHeat ε a f t q - restrict ε (continuumHeat f t) q)) '' Icc 0 T) := by
  obtain ⟨R, S, hRS⟩ := exists_latticeHeat_uniform_l2_bounds hd hε hlam ha hfc T
  obtain ⟨P, hP⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1 hf.continuous hfc
  refine ⟨Real.sqrt (ε ^ d * (2 * (R + P))), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hu := memL2_latticeHeat hd hε hlam ha hfc t
  have hv := (hP t ht.1).1
  have h := Summable.tsum_le_tsum (fun q : Site d => show
      (latticeHeat ε a f t q - restrict ε (continuumHeat f t) q) ^ 2 ≤
      2 * (latticeHeat ε a f t q ^ 2 + restrict ε (continuumHeat f t) q ^ 2) by
      nlinarith [sq_nonneg (latticeHeat ε a f t q + restrict ε (continuumHeat f t) q)])
    (memL2_sub hu hv) ((hu.add hv).mul_left 2)
  have hh : (∑' q, (latticeHeat ε a f t q - restrict ε (continuumHeat f t) q) ^ 2) ≤
      2 * (R + P) := by
    rw [tsum_mul_left, hu.tsum_add hv] at h
    nlinarith [(hRS t ht).1, (hP t ht.1).2]
  unfold latticeNorm latticeNormSq
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hh (pow_nonneg hε.le _))

/-- The time supremum of the lattice error norm is measurable in the conductances. -/
theorem measurable_latticeHeat_error_sup {d : ℕ} (hd : 1 ≤ d) {Ω : Type*}
    [MeasurableSpace Ω] {ε lam T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam) (hT : 0 ≤ T) (a : Ω → Edge d → ℝ)
    (ha : ∀ e, Measurable fun r => a r e)
    (haB : ∀ r e, lam ≤ a r e ∧ a r e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Measurable (fun r => sSup ((fun t => latticeNorm ε
      (fun q => latticeHeat ε (a r) f t q - restrict ε (continuumHeat f t) q)) '' Icc 0 T)) := by
  obtain ⟨R, hR⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1 hf.continuous hfc
  apply measurable_sSup_latticeNorm hε hT
    (fun t r q => latticeHeat ε (a r) f t q - restrict ε (continuumHeat f t) q)
  · intro t q
    exact (measurable_latticeHeat ε a ha f t q).sub measurable_const
  · intro r q
    exact (continuousOn_latticeHeat_error hd hε hlam (haB r) hf hfc q).mono
      (fun t ht => ht.1)
  · intro r t ht
    exact memL2_sub (memL2_latticeHeat hd hε hlam (haB r) hfc t) (hR t ht.1).1
  · intro r
    exact bddAbove_latticeHeat_error hd hε hε1 hlam (haB r) hf hfc

/-- A deterministic bound by an integrated Gaussian field yields a Gaussian bound. -/
theorem isOq_of_energy_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {H : ℝ → Ω → ℝ} (hH : ∀ s r, 0 ≤ H s r)
    (hm : Measurable (Function.uncurry H)) {T C a b : ℝ} (hT : 0 < T) (hC : 0 < C)
    (ha : 0 ≤ a) (hb : 0 < b) {Y : Ω → ℝ} (hYm : AEMeasurable Y P)
    (hO : ∀ s ∈ Set.Icc 0 T, IsOq P 2 (H s) C)
    (hbound : ∀ᵐ r ∂P, Y r ≤ a + b * Real.sqrt (∫ s in (0 : ℝ)..T, H s r ^ 2)) :
    (∀ᵐ r ∂P, IntegrableOn (fun s => H s r ^ 2) (Set.Icc 0 T)) ∧
      IsOq P 2 Y (2 * a + 3 * b * Real.sqrt (T * C ^ 2)) := by
  let R := Real.sqrt (T * C ^ 2)
  let Z : Ω → ℝ := fun r => Real.sqrt (∫ s in (0 : ℝ)..T, H s r ^ 2)
  have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos hT (sq_pos_of_pos hC))
  have hU : 0 < a + b * R := add_pos_of_nonneg_of_pos ha (mul_pos hb hR)
  have hI := isOq_sqrt_integral P hH hm hT hC hO
  have hz : IsOq P 2 Z R := hI.2
  have hconst : IsOq P 2 (fun _ => a + b * R) (2 * (a + b * R)) :=
    isOq_const (P := P) (q := 2) (by decide) hU
  have hscaled : IsOq P 2 (fun r => b * Z r) (b * R) := hz.const_mul hb
  have hadd := LongRangeHeat.isOq_add P (q := 2) (by decide) (fun _ => hU.le)
    (fun r => mul_nonneg hb.le (Real.sqrt_nonneg _)) (by positivity) (mul_pos hb hR)
    hconst hscaled
  have hA : 0 < 2 * (a + b * R) + b * R := by positivity
  have hcomp : ∀ᵐ r ∂P, Y r ≤ (a + b * R) + b * Z r := by
    filter_upwards [hbound] with r hr
    dsimp [Z] at *
    nlinarith [mul_nonneg hb.le hR.le]
  refine ⟨hI.1, ?_⟩
  have hh := LongRangeHeat.isOq_of_ae_le P hA hYm hcomp hadd
  convert hh using 1
  dsimp [R]
  ring

end LongRangeHeat
