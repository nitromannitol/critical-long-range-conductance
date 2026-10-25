import LongRange.Model.Conductance
import LatticeProb.Prob.HoeffdingSeries.Countable
import LatticeProb.Prob.StochasticO

/-!
# Hoeffding estimates for conductances

Injective families of edges inherit independence from Assumption (U). Centering and
rescaling their conductances gives countable weighted Hoeffding estimates.
-/

namespace LongRange

open MeasureTheory ProbabilityTheory LatticeProb

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ}
variable {a : Ω → Edge d → ℝ}

/-- Identical distribution identifies every edge mean with the base edge mean. -/
theorem AssumptionU.integral_eq_mean (hA : AssumptionU P lam a) (e : Edge d) :
    ∫ ω, a ω e ∂P = meanConductance P hA.one_le_dim a :=
  (hA.identDistrib e (baseEdge hA.one_le_dim)).integral_eq

/-- Uniform ellipticity makes each conductance integrable. -/
theorem AssumptionU.integrable (hA : AssumptionU P lam a) (e : Edge d) :
    Integrable (fun ω => a ω e) P := by
  haveI := hA.isProbabilityMeasure
  apply Integrable.of_bound (hA.measurable e).aestronglyMeasurable lam⁻¹
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hA.lam_pos.le.trans (hA.bounds ω e).1)]
    exact (hA.bounds ω e).2

/-- The mean inherits the same ellipticity interval as every conductance. -/
theorem AssumptionU.mean_mem_Icc (hA : AssumptionU P lam a) :
    meanConductance P hA.one_le_dim a ∈ Set.Icc lam lam⁻¹ := by
  haveI := hA.isProbabilityMeasure
  let e := baseEdge hA.one_le_dim
  have hl := integral_mono (integrable_const lam) (hA.integrable e)
    (fun ω => (hA.bounds ω e).1)
  have hu := integral_mono (hA.integrable e) (integrable_const lam⁻¹)
    (fun ω => (hA.bounds ω e).2)
  simpa only [integral_const, probReal_univ, one_smul, meanConductance, e, Set.mem_Icc] using
    And.intro hl hu

/-- Injective edge families satisfy the countable centered Hoeffding estimate. -/
theorem AssumptionU.osBound_weighted_tsum (hA : AssumptionU P lam a)
    {ι : Type*} [Countable ι] (e : ι → Edge d) (he : Function.Injective e)
    (b : ι → ℝ) (hb : Summable b) :
    Measurable (fun ω => ∑' i, b i * (a ω (e i) - meanConductance P hA.one_le_dim a)) ∧
    OsBound P 2 (2 * lam⁻¹ * Real.sqrt (∑' i, b i ^ 2))
      (fun ω => |∑' i, b i * (a ω (e i) - meanConductance P hA.one_le_dim a)|) := by
  haveI := hA.isProbabilityMeasure
  let m := meanConductance P hA.one_le_dim a
  let X := fun i ω => lam * (a ω (e i) - m)
  have hm : ∀ i, Measurable (X i) := fun i =>
    measurable_const.mul ((hA.measurable (e i)).sub measurable_const)
  have hi : iIndepFun X P := (hA.iIndep.precomp he).comp
    (fun _ x => lam * (x - m)) (fun _ => by fun_prop)
  have hc : ∀ i, ∫ ω, X i ω ∂P = 0 := by
    intro i
    dsimp only [X]
    rw [integral_const_mul, integral_sub (hA.integrable (e i)) (integrable_const m)]
    simp only [hA.integral_eq_mean, integral_const, probReal_univ, one_smul, m,
      sub_self, mul_zero]
  have hx : ∀ i ω, |X i ω| ≤ 1 := by
    intro i ω
    have ha := hA.bounds ω (e i)
    obtain ⟨hml, hmu⟩ := hA.mean_mem_Icc
    have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hA.lam_pos.ne'
    have ha0 := mul_nonneg hA.lam_pos.le (hA.lam_pos.le.trans ha.1)
    have hm0 := mul_nonneg hA.lam_pos.le (hA.lam_pos.le.trans hml)
    have ha1 := mul_le_mul_of_nonneg_left ha.2 hA.lam_pos.le
    have hm1 := mul_le_mul_of_nonneg_left hmu hA.lam_pos.le
    rw [hinv] at ha1 hm1
    dsimp only [X, m]
    rw [mul_sub, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hsum (ω : Ω) :
      (∑' i, b i / lam * X i ω) = ∑' i, b i * (a ω (e i) - m) := by
    congr 1
    funext i
    dsimp only [X]
    field_simp [hA.lam_pos.ne']
  have hsquare : (∑' i, (b i / lam) ^ 2) = lam⁻¹ ^ 2 * ∑' i, b i ^ 2 := by
    rw [← tsum_mul_left]
    congr 1
    funext i
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hscale : 2 * Real.sqrt (∑' i, (b i / lam) ^ 2) =
      2 * lam⁻¹ * Real.sqrt (∑' i, b i ^ 2) := by
    rw [hsquare, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hA.lam_pos.le)]
    ring
  refine ⟨measurable_weighted_tsum
    (fun i => (hA.measurable (e i)).sub measurable_const) b, ?_⟩
  have h := osBound_abs_weighted_tsum hm hi hc hx (hb.div_const lam)
  simpa only [hsum, hscale, m] using h

/-- The second moment has a universal constant and the ellipticity factor λ⁻². -/
theorem edge_hoeffding_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
      {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
      {ι : Type*} [Countable ι] (e : ι → Edge d), Function.Injective e →
      ∀ b : ι → ℝ, Summable b →
      Integrable (fun ω =>
        (∑' i, b i * (a ω (e i) - meanConductance P hA.one_le_dim a)) ^ 2) P ∧
      ∫ ω, (∑' i, b i * (a ω (e i) - meanConductance P hA.one_le_dim a)) ^ 2 ∂P ≤
        C * lam⁻¹ ^ 2 * ∑' i, b i ^ 2 := by
  obtain ⟨C, hC, hmoment⟩ := osBound_moment 2 2 (by norm_num) (by norm_num)
  refine ⟨4 * C, by positivity, ?_⟩
  intro d Ω _ P lam a hA ι _ e he b hb
  haveI := hA.isProbabilityMeasure
  obtain ⟨hm, hbound⟩ := hA.osBound_weighted_tsum e he b hb
  let S := fun ω => ∑' i, b i * (a ω (e i) - meanConductance P hA.one_le_dim a)
  have hnonneg : 0 ≤ ∑' i, b i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  by_cases hz : (∑' i, b i ^ 2) = 0
  · have hbzero : ∀ i, b i = 0 := by
      intro i
      have hi := (summable_sq_of_summable_real hb).le_tsum i
        (fun j _ => sq_nonneg (b j))
      rw [hz] at hi
      exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
    simp only [hbzero, zero_mul, tsum_zero, zero_pow (by decide : 2 ≠ 0),
      integral_zero, mul_zero, le_refl, and_true]
    exact integrable_const 0
  · have hθ : 0 < 2 * lam⁻¹ * Real.sqrt (∑' i, b i ^ 2) :=
      mul_pos (mul_pos (by norm_num) (inv_pos.mpr hA.lam_pos))
        (Real.sqrt_pos.mpr (lt_of_le_of_ne hnonneg (Ne.symm hz)))
    have hlin := hmoment P _ (fun ω => |S ω|) hθ hm.abs
      (fun ω => abs_nonneg _) hbound
    have hscale : (2 * lam⁻¹ * Real.sqrt (∑' i, b i ^ 2)) ^ 2 =
        4 * lam⁻¹ ^ 2 * ∑' i, b i ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hnonneg]
      ring
    have hlin' : ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂P ≤
        ENNReal.ofReal (4 * C * lam⁻¹ ^ 2 * ∑' i, b i ^ 2) := by
      simp only [Real.rpow_two, sq_abs] at hlin
      rw [hscale] at hlin
      convert hlin using 1
      congr 1
      ring
    have hint : Integrable (fun ω => S ω ^ 2) P := by
      apply (lintegral_ofReal_ne_top_iff_integrable
        (hm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => sq_nonneg _)).mp
      exact ne_of_lt (lt_of_le_of_lt hlin' ENNReal.ofReal_lt_top)
    refine ⟨hint, ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)]
    exact hlin'

end

end LongRange
