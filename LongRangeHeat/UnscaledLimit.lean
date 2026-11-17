import LongRangeHeat.Statements.InvariancePrinciple
import LongRangeHeat.ScaledUnitLaw
import LongRangeHeat.ScalingWeakConvergence
import LongRangeHeat.NormalizationScaling

/-!
# The unscaled annealed limit

The rescaled invariance principle and deterministic space-time changes give the annealed limit
of the unit walk in its original time parametrization.
-/

namespace LongRangeHeat

open Set Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.Euclidean.Lattice
open scoped Topology NNReal
open LongRange (Edge)

noncomputable section

/-- The natural-number clock, with an arbitrary positive clock at zero. -/
def naturalClock (n : ℕ) : {c : ℝ≥0 // 0 < c} :=
  if h : 0 < n then ⟨n, by exact_mod_cast h⟩ else ⟨1, zero_lt_one⟩

/-- The law of the unit walk under the `(n log n)^(-1/2)` space and `n` time scaling. -/
def normalizedUnitLaw {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {lam : ℝ} (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a)
    (n : ℕ) : ProbabilityMeasure (PathSpace d) :=
  (unitAnnealedLaw hd P a hP).map
    (scaledPath (Real.sqrt ((n : ℝ) * Real.log n))⁻¹ (naturalClock n))

/-- Continuous Brownian paths give a law supported on continuous càdlàg paths. -/
theorem ae_continuous_scaledBrownianPath {d : ℕ}
    (B : ProbabilityMeasure (LatticeProb.BrownianPath d)) (s : ℝ) :
    ∀ᵐ y ∂(B.map (scaledBrownianPath s) : Measure (PathSpace d)),
      Continuous y.1 := by
  have hset : MeasurableSet (Set.range (D.ofContinuous :
      C(Time, EuclideanSpace ℝ (Fin d)) → PathSpace d)) :=
    measurableSet_range_of_continuous_injective continuous_ofContinuous D.ofContinuous_injective
  have hrange : ∀ᵐ y ∂(B.map (scaledBrownianPath s) : Measure (PathSpace d)), y ∈ Set.range (D.ofContinuous :
        C(Time, EuclideanSpace ℝ (Fin d)) → PathSpace d) := by
    change ∀ᵐ y ∂Measure.map (scaledBrownianPath s) (B : Measure (LatticeProb.BrownianPath d)), y ∈ _
    apply (mem_ae_map_iff (measurable_scaledBrownianPath s).aemeasurable hset).2
    exact Filter.Eventually.of_forall fun w => ⟨⟨fun t => s • w t,
      w.continuous.const_smul s⟩, rfl⟩
  filter_upwards [hrange] with y hy
  obtain ⟨w, rfl⟩ := hy
  exact w.continuous

/-- Scaling a Brownian path law by a constant multiplies its spatial coefficient. -/
theorem scaledBrownianPath_map_scaled {d : ℕ}
    (B : ProbabilityMeasure (LatticeProb.BrownianPath d)) (b s : ℝ) :
    (B.map (scaledBrownianPath s)).map (scaledPath b ⟨1, zero_lt_one⟩) =
      B.map (scaledBrownianPath (b * s)) := by
  apply Subtype.ext
  change Measure.map (scaledPath b ⟨1, zero_lt_one⟩)
    (Measure.map (scaledBrownianPath s) (B : Measure (LatticeProb.BrownianPath d))) = _
  have hmap : Measurable (scaledPath (d := d) b ⟨1, zero_lt_one⟩) :=
    measurable_transformPath (fun y : EuclideanSpace ℝ (Fin d) => b • y)
      (continuous_const_smul b) (dilation 1 zero_lt_one)
  rw [Measure.map_map hmap (measurable_scaledBrownianPath s)]
  congr 1
  funext w
  apply Subtype.ext
  funext t
  simp only [Function.comp_def, scaledPath, transformPath_apply, dilation,
    OrderIso.mulLeft₀_apply, one_mul, scaledBrownianPath, D.ofContinuous_apply,
    ContinuousMap.coe_mk, mul_smul]

/-- The paper spacing and clock convert the rescaled law into the normalized unit law. -/
theorem normalizedUnitLaw_eq_scaled {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a) {A ε : ℝ} (hA : 0 < A)
    (hε : ε ∈ Ioo 0 1) (n : ℕ) (hn : 0 < n)
    (he : ε = unscaledSpacing A n) :
    let c : {c : ℝ≥0 // 0 < c} :=
      ⟨⟨LongRange.kappa d ε * ε ^ 2 * (n : ℝ),
        le_of_lt (mul_pos (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))
          (Nat.cast_pos.mpr hn))⟩,
        mul_pos (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))
          (Nat.cast_pos.mpr hn)⟩
    normalizedUnitLaw hd P a hP n =
      (annealedLaw hd P a hP hε.1).map (scaledPath (Real.sqrt (A / 2)) c) := by
  dsimp only
  let c : {c : ℝ≥0 // 0 < c} :=
    ⟨⟨LongRange.kappa d ε * ε ^ 2 * (n : ℝ),
      le_of_lt (mul_pos (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))
        (Nat.cast_pos.mpr hn))⟩,
      mul_pos (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))
        (Nat.cast_pos.mpr hn)⟩
  have hcompose := annealedLaw_map_scaledPath hd hε P a hP (Real.sqrt (A / 2)) c
  have htime : (⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
      one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩ :
        {c : ℝ≥0 // 0 < c}).1 * c.1 = (naturalClock n).1 := by
    apply NNReal.coe_injective
    simp only [naturalClock, hn, ↓reduceDIte, NNReal.coe_natCast]
    change (1 / (LongRange.kappa d ε * ε ^ 2)) *
      (LongRange.kappa d ε * ε ^ 2 * (n : ℝ)) = (n : ℝ)
    field_simp [(LongRange.kappa_pos hd hε).ne', hε.1.ne']
  have hclock : (⟨(⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
      one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩ :
        {c : ℝ≥0 // 0 < c}).1 * c.1,
      mul_pos (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))
        c.2⟩ : {c : ℝ≥0 // 0 < c}) = naturalClock n := Subtype.ext htime
  have hcoef : Real.sqrt (A / 2) * ε = (Real.sqrt ((n : ℝ) * Real.log n))⁻¹ := by
    rw [he, sqrt_mul_unscaledSpacing hA]
  dsimp only at hcompose
  rw [hcoef, hclock] at hcompose
  exact hcompose.symm

/-- The clock factor taking a rescaled walk to time `n` of the unit walk. -/
def rescaledClock {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo 0 1)
    (n : ℕ) (hn : 0 < n) : {c : ℝ≥0 // 0 < c} :=
  ⟨⟨LongRange.kappa d ε * ε ^ 2 * (n : ℝ),
    le_of_lt (mul_pos (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))
      (Nat.cast_pos.mpr hn))⟩,
    mul_pos (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)) (Nat.cast_pos.mpr hn)⟩

/-- A sequence of transformed laws transfers its Brownian limit to the unit walk. -/
theorem normalizedUnitLaw_tendsto_of_maps {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a) (B : ProbabilityMeasure (LatticeProb.BrownianPath d))
    (A s : ℝ) (hcoef : Real.sqrt (A / 2) * s = Real.sqrt (A / (2 * d)))
    (N : ℕ) (μ : ℕ → ProbabilityMeasure (PathSpace d))
    (c : ℕ → {c : ℝ≥0 // 0 < c}) (hc : Tendsto c atTop (𝓝 ⟨1, zero_lt_one⟩))
    (hbase : Tendsto μ atTop (𝓝 (B.map (scaledBrownianPath s))))
    (hlaw : ∀ n, normalizedUnitLaw hd P a hP (n + N) =
      (μ n).map (scaledPath (Real.sqrt (A / 2)) (c n))) :
    Tendsto (normalizedUnitLaw hd P a hP) atTop
      (𝓝 (B.map (scaledBrownianPath (Real.sqrt (A / (2 * d)))))) := by
  have htransfer := tendsto_map_scaledPath hbase (ae_continuous_scaledBrownianPath B s)
    (tendsto_const_nhds (x := Real.sqrt (A / 2))) hc
  rw [scaledBrownianPath_map_scaled, hcoef] at htransfer
  apply (tendsto_add_atTop_iff_nat N).mp
  apply htransfer.congr'
  exact Filter.Eventually.of_forall fun n => (hlaw n).symm

/-- Transfer a rescaled Brownian limit along the paper's spacing sequence. -/
theorem normalizedUnitLaw_tendsto_of_spacing {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a) (B : ProbabilityMeasure (LatticeProb.BrownianPath d))
    (A s : ℝ) (hA : 0 < A) (hcoef : Real.sqrt (A / 2) * s = Real.sqrt (A / (2 * d)))
    (N : ℕ) (e : ℕ → Ioo (0 : ℝ) (1 / 2))
    (hm : ∀ n, 0 < n + N) (he : ∀ n, (e n : ℝ) = unscaledSpacing A (n + N))
    (hclock : Tendsto (fun n => LongRange.kappa d (e n) * (e n : ℝ) ^ 2 *
      ((n + N : ℕ) : ℝ)) atTop (𝓝 1))
    (hbase : Tendsto (fun n => annealedLaw hd P a hP (e n).2.1) atTop
      (𝓝 (B.map (scaledBrownianPath s)))) :
    Tendsto (normalizedUnitLaw hd P a hP) atTop
      (𝓝 (B.map (scaledBrownianPath (Real.sqrt (A / (2 * d)))))) := by
  let m : ℕ → ℕ := fun n => n + N
  let c : ℕ → {c : ℝ≥0 // 0 < c} := fun n =>
    rescaledClock hd ⟨(e n).2.1, lt_trans (e n).2.2 (by norm_num)⟩ (m n) (hm n)
  have hc : Tendsto c atTop (𝓝 ⟨1, zero_lt_one⟩) := by
    apply tendsto_subtype_rng.mpr
    apply NNReal.tendsto_coe.mp
    exact hclock
  apply normalizedUnitLaw_tendsto_of_maps hd P a hP B A s hcoef N
    (fun n => annealedLaw hd P a hP (e n).2.1) c hc hbase
  intro n
  have hε : (e n : ℝ) ∈ Ioo 0 1 := ⟨(e n).2.1,
    lt_trans (e n).2.2 (by norm_num)⟩
  apply normalizedUnitLaw_eq_scaled hd P a hP hA hε (m n) (hm n)
  simpa only [m, Nat.cast_add] using he n


/-- The unit walk has the unscaled annealed Brownian limit. -/
theorem normalizedUnitLaw_tendsto
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (LatticeProb.BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (LatticeProb.BrownianPath d))) :
    let A : ℝ := (d : ℝ) *
      (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
    Tendsto (normalizedUnitLaw hd P a hP) atTop
      (𝓝 (B.map (scaledBrownianPath (Real.sqrt (A / (2 * d)))))) := by
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  change Tendsto (normalizedUnitLaw hd P a hP) atTop
    (𝓝 (B.map (scaledBrownianPath (Real.sqrt (A / (2 * d))))))
  have hA : 0 < A := by
    dsimp [A]
    rw [← LatticeProb.Euclidean.Shell.unitBallVolume_eq_pi_div_gamma]
    exact mul_pos (Nat.cast_pos.mpr (by omega))
      (LatticeProb.Euclidean.Shell.unitBallVolume_pos d)
  have hspacing : Tendsto (fun n : ℕ => unscaledSpacing A n) atTop (𝓝[>] 0) :=
    (tendsto_unscaledSpacing hA).comp tendsto_natCast_atTop_atTop
  have hvalid : ∀ᶠ n : ℕ in atTop, unscaledSpacing A n ∈ Ioo (0 : ℝ) (1 / 2) := by
    filter_upwards [hspacing.eventually self_mem_nhdsWithin,
      hspacing.eventually ((eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
        nhdsWithin_le_nhds)] with n hn hn'
    exact ⟨hn, hn'⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hvalid
  let N := max N₀ 2
  let m : ℕ → ℕ := fun n => n + N
  have hm (n : ℕ) : 2 ≤ m n := (le_max_right _ _).trans (Nat.le_add_left _ _)
  have he (n : ℕ) : unscaledSpacing A (m n) ∈ Ioo (0 : ℝ) (1 / 2) :=
    hN₀ (m n) ((le_max_left _ _).trans (Nat.le_add_left _ _))
  let e : ℕ → Ioo (0 : ℝ) (1 / 2) := fun n => ⟨unscaledSpacing A (m n), he n⟩
  have hmAt : Tendsto (fun n : ℕ => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N)
  have he0 : Tendsto e atTop (Filter.comap Subtype.val (𝓝 0)) := by
    apply Filter.tendsto_comap_iff.mpr
    exact ((tendsto_unscaledSpacing hA).comp hmAt).mono_right nhdsWithin_le_nhds
  let s : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2)
  have hbase : Tendsto (fun n => annealedLaw hd P a hP (e n).2.1) atTop
      (𝓝 (B.map (scaledBrownianPath s))) := by
    exact (Statements.annealed_invariance_principle hMSC hNash hDavies hEK hFdd
      hd P a hP B hB).2.comp he0
  have hclock : Tendsto (fun n => LongRange.kappa d (e n) * (e n : ℝ) ^ 2 *
      (m n : ℝ)) atTop (𝓝 1) := (tendsto_kappa_unscaledSpacing hd).comp hmAt
  exact normalizedUnitLaw_tendsto_of_spacing hd P a hP B A s hA
    (sqrt_mul_dimension_rpow hA.le) N e (fun n => by have := hm n; omega)
    (fun n => by simp only [e, m, Nat.cast_add]) hclock hbase

end
end LongRangeHeat
