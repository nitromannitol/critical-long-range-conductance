import LongRangeHeat.Aldous
import LongRange.Support.Prob.Cadlag.HalfLine.FddAssembly
import LongRange.Support.Prob.Cadlag.HalfLine.AldousHalfLine
import LatticeProb.Prob.BrownianPathSpace

/-!
# The annealed invariance principle: assembly

The annealed laws `P^ann_0 = E[P^a_0]` of the walks `X^{ε_n}` are relatively compact in the
Skorokhod space `D([0, ∞), ℝ^d)` and converge to the law of `d^{-1/2} W` once their
finite-dimensional marginals do.

* The displacement bound of Proposition 4.1(ii) gives tight time marginals and, through
  Proposition 4.2, the stopping-increment condition of Aldous.
* The cited criterion of Ethier–Kurtz (Chapter 3, Theorem 8.6) turns the stopping-increment
  condition into relative compactness; the cited convergence theorem of Ethier–Kurtz
  (Chapter 3, Theorem 7.8(b)) turns relative compactness and finite-dimensional convergence into
  weak convergence. The paper cites Kallenberg (2002, Theorems 16.10 and 16.11) and Aldous (1978)
  for the same two steps.
-/

namespace LongRangeHeat

open MeasureTheory Filter LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.Euclidean.Lattice
open scoped NNReal ENNReal Topology
open LongRange (Edge walkRates walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The displacement bound of Proposition 4.1(ii), in the form used for the annealed law: the
probability that the walk started at `x` is more than `η` away from `x` at time `u` is at most
`C u (1 + ln (1 + η)) / η²` as soon as `ε ≤ η`. -/
theorem transitionKernel_displacement_le (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ (x : Site d) (u : ℝ≥0) (η : ℝ), ε ≤ η →
      (walkRates hd hε.1 hlam.1 a ha).transitionKernel u x
          {z | η < dist (walkEmbed ε z) (walkEmbed ε x)} ≤
        ENNReal.ofReal (C * u * (1 + Real.log (1 + η)) / η ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := LongRangeHeat.Statements.heat_kernel_bounds hMSC hNash hDavies hd hlam
  refine ⟨C, hC, fun ε hε a ha x u η hεη => ?_⟩
  have hη : 0 < η := lt_of_lt_of_le hε.1 hεη
  have hset : {z | η < dist (walkEmbed ε z) (walkEmbed ε x)} =
      {z | η < radius (physical ε (z - x))} := by
    ext z
    have hphys : physical ε (z - x) = physical ε z - physical ε x := by
      funext k
      simp [physical, mul_sub]
    simp only [Set.mem_ofPred_eq, LongRange.dist_walkEmbed, hphys]
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, LatticeProb.JumpChain.BoundedRates.transitionKernel_zero, ProbabilityTheory.Kernel.id_apply,
      Measure.dirac_apply' _ ((Set.to_countable _).measurableSet)]
    rw [Set.indicator_of_notMem]
    · exact bot_le
    · simp [hη.not_gt]
  · rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact (hbound ε hε a ha x x).2 u (pos_iff_ne_zero.mpr hu) η hεη |>.trans_eq (by ring)

/-- Away from the origin the logarithmic displacement bound is below any prescribed level. -/
theorem exists_displacement_radius {C t η : ℝ} (hC : 0 < C) (ht : 0 ≤ t) (hη : 0 < η) :
    ∃ R : ℝ, 1 ≤ R ∧ C * t * (1 + Real.log (1 + R)) / R ^ 2 ≤ η := by
  refine ⟨max 1 (2 * C * t / η), le_max_left _ _, ?_⟩
  set R := max 1 (2 * C * t / η) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hRη : 2 * C * t ≤ η * R := by
    have : 2 * C * t / η ≤ R := le_max_right _ _
    rw [div_le_iff₀ hη] at this
    linarith
  have hlog : Real.log (1 + R) ≤ R := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + R by linarith)
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hCt : 0 ≤ C * t := mul_nonneg hC.le ht
  calc C * t * (1 + Real.log (1 + R)) ≤ C * t * (2 * R) := by
        apply mul_le_mul_of_nonneg_left _ hCt
        linarith
    _ = (2 * C * t) * R := by ring
    _ ≤ (η * R) * R := by gcongr
    _ = η * R ^ 2 := by ring

section Annealed

variable (hd : 1 ≤ d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {lam : ℝ}
  (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a)

include hP in
/-- The annealed time marginals are tight, uniformly in `ε ∈ (0, 1/2)`: the time `t` position
exceeds `R` with probability at most `C t (1 + ln (1 + R)) / R²` as soon as `ε ≤ R`. -/
theorem annealedLaw_marginal_tail_le (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ (t : ℝ≥0) (R : ℝ), ε ≤ R →
      (annealedLaw hd P a hP hε.1 : Measure (PathSpace d)) {X | R < ‖X.1 t‖} ≤
        ENNReal.ofReal (C * t * (1 + Real.log (1 + R)) / R ^ 2) := by
  obtain ⟨C, hC, hk⟩ := transitionKernel_displacement_le hMSC hNash hDavies hd hP.lam_mem
  refine ⟨C, hC, fun ε hε t R hεR => ?_⟩
  have hB : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | R < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hpre : {X : PathSpace d | R < ‖X.1 t‖} = (fun X : PathSpace d => X.1 t) ⁻¹' {y | R < ‖y‖} :=
    rfl
  have := hP.isProbabilityMeasure
  rw [hpre, annealedLaw_eval_apply hd P a hP hε.1 t hB]
  calc ∫⁻ ω, (walkRates hd hε.1 hP.lam_mem.1 (a ω) (hP.bounds ω)).transitionKernel t 0
          (walkEmbed ε ⁻¹' {y | R < ‖y‖}) ∂P
      ≤ ∫⁻ _ω, ENNReal.ofReal (C * t * (1 + Real.log (1 + R)) / R ^ 2) ∂P := by
        refine lintegral_mono fun ω => ?_
        have h0 : walkEmbed ε (0 : Site d) = 0 := by
          ext k
          simp [walkEmbed, physical]
        have hset : walkEmbed ε ⁻¹' {y | R < ‖y‖} =
            {z | R < dist (walkEmbed ε z) (walkEmbed ε (0 : Site d))} := by
          ext z
          simp [h0, dist_zero_right]
        rw [hset]
        exact hk ε hε (a ω) (hP.bounds ω) 0 t R hεR
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

variable {hd P a hP}

include hP in
/-- Uniformly in `n`, the time marginal of the annealed law of `X^{ε_n}` leaves a large ball with
small probability. -/
theorem annealedLaw_exists_radius (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ n, (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d))
      {X | R < ‖X.1 t‖} ≤ ENNReal.ofReal η := by
  obtain ⟨C, hC, hbound⟩ := annealedLaw_marginal_tail_le hd P a hP hMSC hNash hDavies
  obtain ⟨R, hR1, hR⟩ := exists_displacement_radius hC t.2 hη
  refine ⟨R, by linarith, fun n => (hbound (ε n) (hε n) t R ?_).trans
    (ENNReal.ofReal_le_ofReal hR)⟩
  linarith [(hε n).2]

include hP in
/-- The time marginals of the annealed laws of `X^{ε_n}` form a tight family. -/
theorem annealedLaw_marginals_isTight (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) (t : ℝ≥0) :
    IsTightMeasureSet {Measure.map (fun X : PathSpace d => X.1 t)
      (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)) | n} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro r hr
  obtain ⟨η, hη0, hη⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  obtain ⟨R, hR0, hR⟩ := annealedLaw_exists_radius (hd := hd) (P := P) (a := a) (hP := hP)
    hMSC hNash hDavies hε t (show (0 : ℝ) < η from by exact_mod_cast hη0)
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [Measure.map_apply (measurable_eval t) (Metric.isClosed_closedBall.measurableSet.compl)]
  have hset : (fun X : PathSpace d => X.1 t) ⁻¹' (Metric.closedBall 0 R)ᶜ = {X | R < ‖X.1 t‖} := by
    ext X
    simp [not_le]
  rw [hset]
  refine (hR n).trans ?_
  rw [ENNReal.ofReal_coe_nnreal]
  exact hη.le

include hP in
/-- The compact-set form of the tightness of the time marginals at every rational time. -/
theorem annealedLaw_exists_compact (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) {η : ℝ} (hη : 0 < η) (t : ℝ≥0) :
    ∃ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K ∧ ∀ n,
      ENNReal.ofReal (1 - η) ≤
        (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)) {X | X.1 t ∈ K} := by
  obtain ⟨R, hR0, hR⟩ := annealedLaw_exists_radius (hd := hd) (P := P) (a := a) (hP := hP)
    hMSC hNash hDavies hε t hη
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun n => ?_⟩
  have hm : MeasurableSet {X : PathSpace d | R < ‖X.1 t‖} :=
    measurableSet_lt measurable_const (measurable_norm.comp (measurable_eval t))
  have hset : {X : PathSpace d | X.1 t ∈ Metric.closedBall 0 R} = {X | R < ‖X.1 t‖}ᶜ := by
    ext X
    simp [not_lt]
  rw [hset, prob_compl_eq_one_sub hm, ENNReal.ofReal_sub _ hη.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left (hR n) 1

include hP in
/-- Aldous' condition in the form of the cited relative-compactness criterion: along every
sequence of bounded discrete stopping times of the canonical filtration, the probability that the
increment after a delay `u ≤ δ` is at least `η` has a `limsup` that tends to `0` with `δ`. -/
theorem annealedLaw_stoppingIncrementCondition
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hε0 : Tendsto ε atTop (𝓝 0)) :
    stoppingIncrementCondition (Ω := fun _ : ℕ => PathSpace d)
      (fun n => annealedLaw hd P a hP (hε n).1) (fun _ => id) := by
  obtain ⟨C, hC, hk⟩ := transitionKernel_displacement_le hMSC hNash hDavies hd hP.lam_mem
  intro H hH η hη τ hτ
  set c : ℝ := C * (1 + Real.log (1 + η / 2)) / (η / 2) ^ 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log (1 + η / 2) := Real.log_nonneg (by linarith)
    positivity
  have hev : ∀ᶠ n in atTop, ε n ≤ η / 2 := hε0.eventually (ge_mem_nhds (by linarith))
  have hle : ∀ δ : ℝ, limsup (fun n => ⨆ u : ℝ≥0, ⨆ (_ : (u : ℝ) ≤ δ),
      ((annealedLaw hd P a hP (hε n).1 : ProbabilityMeasure (PathSpace d)) :
        Measure (PathSpace d)) {w | η ≤ dist ((id w).1 (τ n w + u)) ((id w).1 (τ n w))}) atTop ≤
      ENNReal.ofReal (c * δ) := by
    intro δ
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev] with n hn
    refine iSup_le fun u => iSup_le fun hu => ?_
    have hsub : {w : PathSpace d | η ≤ dist ((id w).1 (τ n w + u)) ((id w).1 (τ n w))} ⊆
        {X | η / 2 < dist (X.1 (((τ n X : ℝ≥0) : ℝ).toNNReal + u))
          (X.1 ((τ n X : ℝ≥0) : ℝ).toNNReal)} := by
      intro w hw
      simp only [Set.mem_ofPred_eq, id, Real.toNNReal_coe] at hw ⊢
      linarith
    refine (measure_mono hsub).trans ?_
    have hτm : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | ((τ n X : ℝ≥0) : ℝ) ≤ t} := by
      intro t
      have := (hτ n).2.2 t
      simpa only [NNReal.coe_le_coe] using this
    refine (annealedLaw_stopping_le hd P a hP (hε n).1 hτm (fun X => (τ n X).2) u (η / 2)
      (ENNReal.ofReal (C * u * (1 + Real.log (1 + η / 2)) / (η / 2) ^ 2))
      (fun ω y => hk (ε n) (hε n) (a ω) (hP.bounds ω) y u (η / 2) hn)).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have : C * u * (1 + Real.log (1 + η / 2)) / (η / 2) ^ 2 = c * u := by
      rw [hc]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hu hc0
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (c * δ)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => c * δ) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous fun δ : ℝ => c * δ := continuous_const.mul continuous_id
      simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using ENNReal.tendsto_ofReal h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun δ => bot_le) hle

include hP in
/-- The annealed laws of `X^{ε_n}` have relatively compact range in the Skorokhod space, by the
cited criterion of Ethier–Kurtz (Chapter 3, Theorem 8.6) applied to the tight time marginals and
Aldous' condition. -/
theorem annealedLaw_isCompact_closure_range
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hε0 : Tendsto ε atTop (𝓝 0)) :
    IsCompact (closure (Set.range (fun n => annealedLaw hd P a hP (hε n).1))) := by
  have := isCompact_closure_range_map_of_stoppingIncrementCondition
    (Ω := fun _ : ℕ => PathSpace d) (fun n => annealedLaw hd P a hP (hε n).1)
    (fun _ => id) hEK (fun _ => measurable_id)
    (fun η hη t _ => annealedLaw_exists_compact hMSC hNash hDavies hε hη (t : ℝ).toNNReal)
    (annealedLaw_stoppingIncrementCondition hMSC hNash hDavies hε hε0)
  have hmap : (fun n => (annealedLaw hd P a hP (hε n).1).map (id : PathSpace d → PathSpace d)) =
      fun n => annealedLaw hd P a hP (hε n).1 := by
    funext n
    exact Subtype.ext Measure.map_id
  simpa only [hmap] using this

include hP in
/-- **Assembly of the annealed invariance principle.** If the finite-dimensional marginals of
the annealed laws of `X^{ε_n}` at strictly increasing positive times converge weakly to those
of a probability law `ν` on the Skorokhod space, then the annealed laws converge weakly to `ν`.
The tightness of the time marginals and Aldous' condition come from Propositions 4.1 and 4.2;
the cited results of Ethier–Kurtz (Chapter 3, Theorems 7.8(b) and 8.6) supply the compactness
criterion and the convergence criterion. -/
theorem annealed_invariance_of_fdd
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hε0 : Tendsto ε atTop (𝓝 0))
    (ν : ProbabilityMeasure (PathSpace d))
    (hfdd : ∀ {k : ℕ} (ts : Fin k → ℝ≥0), StrictMono ts → (∀ j, 0 < ts j) →
      Tendsto (fun n => jointLaw (annealedLaw hd P a hP (hε n).1) ts) atTop
        (𝓝 (jointLaw ν ts))) :
    Tendsto (fun n => annealedLaw hd P a hP (hε n).1) atTop (𝓝 ν) := by
  refine tendsto_of_relativelyCompact_productTests hFdd
    (annealedLaw_isCompact_closure_range hMSC hNash hDavies hEK hε hε0)
    (fun t => annealedLaw_marginals_isTight hMSC hNash hDavies hε t) ?_
  intro m ss hmono hpos φ
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hfdd ss hmono hpos))
    (LatticeProb.productTest φ)
  simpa only [LatticeProb.productTest_apply] using h

end Annealed

section Brownian

/-- The continuous path `t ↦ s W_t` of a Brownian path `W`, as an element of the Skorokhod
space. -/
def scaledBrownianPath (s : ℝ) (w : BrownianPath d) : PathSpace d :=
  D.ofContinuous ⟨fun t => s • w t, w.continuous.const_smul s⟩

theorem measurable_scaledBrownianPath (s : ℝ) : Measurable (scaledBrownianPath (d := d) s) := by
  apply measurable_iff_measurable_eval.mpr
  intro t
  change Measurable (fun w : BrownianPath d => s • w t)
  exact ((continuous_eval_const t : Continuous fun w : BrownianPath d => w t).measurable).const_smul s

/-- The joint law of the evaluations of `s W` is the law of the corresponding evaluations of the
Brownian path. -/
theorem jointLaw_map_scaledBrownianPath (B : ProbabilityMeasure (BrownianPath d)) (s : ℝ)
    {k : ℕ} (ts : Fin k → ℝ≥0) :
    jointLaw (B.map (scaledBrownianPath s)) ts =
      B.map (fun w : BrownianPath d => fun j => s • w (ts j)) := by
  apply Subtype.ext
  change Measure.map _ (Measure.map _ (B : Measure (BrownianPath d))) = Measure.map _ _
  rw [Measure.map_map (measurable_pi_iff.mpr fun j => measurable_eval (ts j))
    (measurable_scaledBrownianPath s)]
  rfl

variable {hd : 1 ≤ d} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ}
  {a : Ω → Edge d → ℝ}

/-- **The annealed invariance principle from finite-dimensional convergence.** If, along every
sequence `ε_n → 0` in `(0, 1/2)`, the finite-dimensional marginals of the annealed laws at
strictly increasing positive times converge weakly to those of `s W`, then the annealed laws
converge weakly, as `ε → 0` in `(0, 1/2)`, to the law of `s W`. -/
theorem annealed_invariance_of_brownian_fdd
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    (hP : ConductanceLaw P lam a) (B : ProbabilityMeasure (BrownianPath d)) (s : ℝ)
    (hfdd : ∀ (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)), Tendsto ε atTop (𝓝 0) →
      ∀ {k : ℕ} (ts : Fin k → ℝ≥0), StrictMono ts → (∀ j, 0 < ts j) →
        Tendsto (fun n => (annealedLaw hd P a hP (hε n).1).map
          (fun X : PathSpace d => fun j => X.1 (ts j))) atTop
          (𝓝 (B.map (fun w : BrownianPath d => fun j => s • w (ts j))))) :
    Tendsto (fun ε : Set.Ioo (0 : ℝ) (1 / 2) => annealedLaw hd P a hP ε.2.1)
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 (B.map (scaledBrownianPath s))) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro ε hε0
  have hε0' : Tendsto (fun n => ((ε n : Set.Ioo (0 : ℝ) (1 / 2)) : ℝ)) atTop (𝓝 0) :=
    Filter.tendsto_comap_iff.1 hε0
  exact annealed_invariance_of_fdd (hP := hP) hMSC hNash hDavies hEK hFdd
    (fun n => (ε n).2) hε0' (B.map (scaledBrownianPath s))
    (fun {k} ts hts hpos => by
      rw [jointLaw_map_scaledBrownianPath]
      exact hfdd (fun n => (ε n : ℝ)) (fun n => (ε n).2) hε0' ts hts hpos)

/-- A probability measure on a space with at most one point is determined: there is only one. -/
theorem subsingleton_probabilityMeasure {X : Type*} [MeasurableSpace X] [Subsingleton X] :
    Subsingleton (ProbabilityMeasure X) := by
  refine ⟨fun μ ν => ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  ext s _
  rcases s.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp
  · have hs : s = Set.univ := Set.eq_univ_of_forall fun x => Subsingleton.elim x y ▸ hy
    subst hs
    simp

/-- **The annealed invariance principle from finite-dimensional convergence.** If, along every
sequence `ε_n → 0` in `(0, 1/2)`, the finite-dimensional marginals of the annealed laws at
strictly increasing times `t_1 < ⋯ < t_k` with `k ≥ 1` converge weakly to those of `s W`, then
the annealed laws converge weakly, as `ε → 0` in `(0, 1/2)`, to the law of `s W`. -/
theorem annealed_invariance_of_fdd_convergence
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    (hP : ConductanceLaw P lam a) (B : ProbabilityMeasure (BrownianPath d)) (s : ℝ)
    (hfdd : ∀ (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)), Tendsto ε atTop (𝓝 0) →
      ∀ {k : ℕ}, 1 ≤ k → ∀ ts : Fin k → ℝ≥0, StrictMono ts →
        Tendsto (fun n => (annealedLaw hd P a hP (hε n).1).map
          (fun X : PathSpace d => fun j => X.1 (ts j))) atTop
          (𝓝 (B.map (fun w : BrownianPath d => fun j => s • w (ts j))))) :
    Tendsto (fun ε : Set.Ioo (0 : ℝ) (1 / 2) => annealedLaw hd P a hP ε.2.1)
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 (B.map (scaledBrownianPath s))) := by
  refine annealed_invariance_of_brownian_fdd hMSC hNash hDavies hEK hFdd hP B s ?_
  intro ε hε hε0 k ts hts _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Subsingleton (ProbabilityMeasure (Fin 0 → EuclideanSpace ℝ (Fin d))) := subsingleton_probabilityMeasure
    exact tendsto_const_nhds.congr fun n => Subsingleton.elim _ _
  · exact hfdd ε hε hε0 hk ts hts

end Brownian

end

end LongRangeHeat
