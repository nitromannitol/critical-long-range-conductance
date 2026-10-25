import LongRange.Walk.ContinuumSemigroup
import LongRange.Walk.KilledResolvent
import LongRange.Walk.HomogenizationEvent
import LatticeProb.Analysis.DenseSmoothFamily
import LatticeProb.Analysis.Elliptic.BallDomain
import LatticeProb.Analysis.Elliptic.OneDimExistence
import LatticeProb.External.GilbargTrudingerExistence
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Resolvent convergence on one almost sure event

Classical homogenization and sampling convergence give resolvent convergence on countable
dense families in coordinate Euclidean balls. Uniform operator bounds extend this event
to all square-integrable data. Dimension one uses the proved interval existence theorem.
-/

namespace LongRange

open MeasureTheory Filter Topology LatticeProb LatticeProb.Elliptic
open LatticeProb.Euclidean.Lattice LatticeProb.ContractionSemigroup
open scoped ContDiff NNReal ENNReal

noncomputable section

variable {d : ℕ}

/-- Coordinate Euclidean balls have the regularity required by homogenization. -/
theorem continuumDomain_isC2HolderDomain (σ : ℝ) {R : ℝ} (hR : 0 < R) :
    IsC2HolderDomain σ (continuumDomain (d := d) R) :=
  isC2HolderDomain_image_ball σ 0 hR

/-- Positive mass Dirichlet existence on balls, including dimension one. -/
theorem exists_classicalDirichletSolution_continuumDomain
    (h614 : External.GilbargTrudingerExistence) (hd : 1 ≤ d)
    {R a₀ : ℝ} (hR : 0 < R) (ha₀ : 0 < a₀)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hh : c0HolderNorm (1 / 2) (closure (continuumDomain R)) f < ⊤) :
    ∃ u, IsClassicalDirichletSolution (continuumDomain R) 1 a₀ f u := by
  by_cases hd1 : d = 1
  · subst d
    have hball : continuumDomain (d := 1) R =
        {x : Fin 1 → ℝ | |x 0 - 0| < R} := by
      rw [continuumDomain, image_ball_eq 0 hR]
      ext x
      simp only [Set.mem_setOf_eq, map_zero, Pi.zero_apply, sub_zero,
        Fin.sum_univ_one]
      exact by
        simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (x 0)) hR.le)
    rw [hball]
    exact exists_classicalDirichletSolution_one_ball hR zero_lt_one ha₀
      hf.continuousOn
  · exact exists_classicalDirichletSolution_of_gt h614 (by omega)
      (by norm_num) (by norm_num) (continuumDomain_isC2HolderDomain _ hR)
      ha₀ zero_le_one hh

/-- Every ball admits dense smooth data and corresponding classical solutions. -/
theorem exists_dense_classical_family
    (h614 : External.GilbargTrudingerExistence) (hd : 1 ≤ d)
    {R a₀ : ℝ} (hR : 0 < R) (ha₀ : 0 < a₀) :
    ∃ (f u : ℕ → (Fin d → ℝ) → ℝ)
      (hf : ∀ k, MemLp (f k) 2 (volume.restrict (continuumDomain R))) (M : ℕ → ℝ),
      DenseRange (fun k => (hf k).toLp (f k)) ∧
      ∀ k, ContDiff ℝ ∞ (f k) ∧ HasCompactSupport (f k) ∧
        tsupport (f k) ⊆ continuumDomain R ∧
        c0HolderNorm (1 / 2) (closure (continuumDomain R)) (f k) ≤
          ENNReal.ofReal (M k) ∧
        IsClassicalDirichletSolution (continuumDomain R) 1 a₀ (f k) (u k) := by
  have hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2) hR
  obtain ⟨f, hf, hdense, hreg⟩ := exists_dense_smooth_family_infty_holder hU.1 hU.2.2.1
  have hex (k : ℕ) := (hreg k).2.2.2 (1 / 2) (by norm_num) (by norm_num)
  choose M hMnonneg hM using fun k => (hex k).2.2
  have hsol (k : ℕ) : ∃ u,
      IsClassicalDirichletSolution (continuumDomain R) 1 a₀ (f k) u :=
    exists_classicalDirichletSolution_continuumDomain h614 hd hR ha₀
      (hreg k).1.continuous (hex k).1
  choose u hu using hsol
  exact ⟨f, u, hf, M, hdense, fun k =>
    ⟨(hreg k).1, (hreg k).2.1, (hreg k).2.2.1, hM k, hu k⟩⟩

/-- The discrete carrier norm agrees with the paper's sampled norm. -/
theorem norm_toLp_latticeMeasure {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (g : Site d → ℝ) :
    ‖(memLp_latticeMeasure hε hb g).toLp g‖ = l2Norm ε U g := by
  rw [l2Norm, ← norm_sq_toLp_latticeMeasure hε hb g, Real.sqrt_sq (norm_nonneg _)]

/-- Uniformly continuous zero extensions have vanishing sampling error in carrier norm. -/
theorem tendsto_norm_cellAverageLp_sub_sample
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    {F : (Fin d → ℝ) → ℝ} (hF : UniformContinuous F)
    (hzero : ∀ y, y ∉ U → F y = 0)
    (hf : MemLp F 2 (volume.restrict U)) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      ‖cellAverageLp ε.property hU hb (hf.toLp F) -
        (memLp_latticeMeasure ε.property hb (fun q => F (physical ε q))).toLp _‖)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  have hlim := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_cellAverage_sub_sample_of_uniformContinuous hb hF hzero)
  have heq (ε : {ε : ℝ // 0 < ε}) :
      ‖cellAverageLp ε.property hU hb (hf.toLp F) -
        (memLp_latticeMeasure ε.property hb (fun q => F (physical ε q))).toLp _‖ =
      Real.sqrt (l2NormSq ε U
        (fun q => cellAverage ε U F q - F (physical ε q))) := by
    rw [cellAverageLp_toLp ε.property hU hb hf, ← MemLp.toLp_sub]
    exact norm_toLp_latticeMeasure ε.property hb _
  simp only [Real.sqrt_zero] at hlim
  simpa only [heq, Function.comp_def] using hlim.comp tendsto_comap

/-- A classical zero-boundary solution has a uniformly continuous zero extension. -/
theorem uniformContinuous_indicator_classical {U : Set (Fin d → ℝ)}
    (hb : Bornology.IsBounded U) {μ a₀ : ℝ} {f u : (Fin d → ℝ) → ℝ}
    (hu : IsClassicalDirichletSolution U μ a₀ f u) :
    UniformContinuous (U.indicator u) := by
  have hc : Continuous (U.indicator u) := continuous_indicator hu.2.2.1 hu.2.1
  have hs : HasCompactSupport (U.indicator u) := by
    apply hb.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h u)
  exact hs.uniformContinuous_of_continuous hc

/-- Cell averages approximate sampled classical solutions, using zero boundary values. -/
theorem tendsto_norm_cellAverageLp_sub_classical
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    {μ a₀ : ℝ} {f u : (Fin d → ℝ) → ℝ}
    (hu : IsClassicalDirichletSolution U μ a₀ f u)
    (huLp : MemLp u 2 (volume.restrict U)) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      ‖cellAverageLp ε.property hU hb (huLp.toLp u) -
        (memLp_latticeMeasure ε.property hb (fun q => u (physical ε q))).toLp _‖)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  have heq : U.indicator u =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact Set.indicator_of_mem hx u
  have hi : MemLp (U.indicator u) 2 (volume.restrict U) := huLp.ae_eq heq.symm
  have hlim := tendsto_norm_cellAverageLp_sub_sample hU hb
    (uniformContinuous_indicator_classical hb hu)
    (fun y hy => Set.indicator_of_notMem hy u) hi
  rw [MemLp.toLp_congr hi huLp heq] at hlim
  have hs (ε : {ε : ℝ // 0 < ε}) :
      (memLp_latticeMeasure ε.property hb
        (fun q => U.indicator u (physical ε q))).toLp _ =
      (memLp_latticeMeasure ε.property hb
        (fun q => u (physical ε q))).toLp _ := by
    apply MemLp.toLp_congr
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (latticeSet_finite ε.property hb).measurableSet]
      with q hq
    exact Set.indicator_of_mem (show physical ε q ∈ U from hq) u
  simpa only [hs] using hlim

/-- Classical data give almost sure convergence of the sampled killed resolvents. -/
theorem ae_tendsto_sampled_killedResolvent
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (ha : AssumptionU P lam a)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain (1 / 2) U)
    {M : ℝ} {f u : (Fin d → ℝ) → ℝ}
    (hf : c0HolderNorm (1 / 2) (closure U) f ≤ ENNReal.ofReal M)
    (hu : IsClassicalDirichletSolution U 1
      (meanConductance P hd a / (2 * d)) f u) :
    ∀ᵐ ξ ∂P, Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      ‖resolvent (discreteKilledSemigroup hd ε.property ha.lam_pos
          (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
          ((memLp_latticeMeasure ε.property hU.2.2.1
            (fun q => f (physical ε q))).toLp _) -
        (memLp_latticeMeasure ε.property hU.2.2.1
          (fun q => u (physical ε q))).toLp _‖)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  classical
  unfold IsC2HolderDomain at hU
  filter_upwards [ae_tendsto_discrete_solution h619 h66 h37 h637 d hd lam
    (1 / 2) 1 (by norm_num) zero_le_one U hU M P a ha f u hf hu] with ξ hξ
  let v : ℝ → Site d → ℝ := fun ε =>
    if hε : 0 < ε then
      (latticeSet ε U).indicator (fun q =>
        resolvent (discreteKilledSemigroup hd hε ha.lam_pos
          (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
          ((memLp_latticeMeasure hε hU.2.2.1
            (fun q => f (physical ε q))).toLp _) q)
    else 0
  have hv (ε : ℝ) (hε : 0 < ε) :=
    killedResolvent_eq_solution hd hε ha.lam_pos (a ξ) (ha.bounds ξ)
      hU.2.2.1 zero_lt_one (fun q => f (physical ε q))
  have hs : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε U (v ε) := by
    intro ε hε
    simpa only [v, dif_pos hε.1] using (hv ε hε.1).1
  have heq : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet ε U,
      1 * v ε q - generator ε (a ξ) (v ε) q = f (physical ε q) := by
    intro ε hε
    simpa only [v, dif_pos hε.1] using (hv ε hε.1).2.2
  have hlim := (hξ v hs heq).comp
    (tendsto_comap (f := (Subtype.val : {ε : ℝ // 0 < ε} → ℝ)))
  apply hlim.congr
  intro ε
  simp only [Function.comp_apply]
  rw [← norm_toLp_latticeMeasure ε.property hU.2.2.1]
  have hvLp : (memLp_latticeMeasure ε.property hU.2.2.1 (v ε)).toLp (v ε) =
      resolvent (discreteKilledSemigroup hd ε.property ha.lam_pos
        (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
        ((memLp_latticeMeasure ε.property hU.2.2.1
          (fun q => f (physical ε q))).toLp _) := by
    simpa only [v, dif_pos ε.property] using (hv ε ε.property).2.1
  change ‖(memLp_latticeMeasure ε.property hU.2.2.1 (v ε)).toLp (v ε) -
    (memLp_latticeMeasure ε.property hU.2.2.1
      (fun q => u (physical ε q))).toLp _‖ = _
  rw [hvLp]

/-- Sampling convergence transfers classical homogenization to cell-average data. -/
theorem ae_tendsto_classical_cellAverage_resolvent
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (ha : AssumptionU P lam a)
    {R : ℝ} (hR : 0 < R) {μB : Measure (BrownianPath d)}
    (hμB : IsStandardBrownianLaw μB)
    {f u : (Fin d → ℝ) → ℝ} (hfc : ContDiff ℝ ∞ f)
    (hfs : HasCompactSupport f) (hfU : tsupport f ⊆ continuumDomain R)
    (hu : IsClassicalDirichletSolution (continuumDomain R) 1
      (meanConductance P hd a / (2 * d)) f u)
    (hf : MemLp f 2 (volume.restrict (continuumDomain R))) :
    let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2) hR
    ∀ᵐ ξ ∂P, Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      ‖resolvent (discreteKilledSemigroup hd ε.property ha.lam_pos
          (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
          (cellAverageLp ε.property hU.1.measurableSet hU.2.2.1 (hf.toLp f)) -
        cellAverageLp ε.property hU.1.measurableSet hU.2.2.1
          (resolvent (continuumSemigroup R (meanConductance P hd a / (2 * d)) hμB)
            1 zero_lt_one (hf.toLp f))‖)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  dsimp only
  let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2) hR
  have hfinite := c0HolderNorm_lt_top_of_smooth_compact hfc hfs
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (closure (continuumDomain R))
  have hbound : c0HolderNorm (1 / 2) (closure (continuumDomain R)) f ≤
      ENNReal.ofReal (c0HolderNorm (1 / 2) (closure (continuumDomain R)) f).toReal :=
    (ENNReal.ofReal_toReal hfinite.ne).ge
  obtain ⟨hf', huLp, hid⟩ := continuumResolvent_classical hμB hR
    (continuum_coefficient_pos ha hd) zero_lt_one hu hfc.continuous.continuousOn
  have hzero : ∀ y, y ∉ continuumDomain R → f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (hfU (subset_tsupport f hne))
  have hforce := tendsto_norm_cellAverageLp_sub_sample hU.1.measurableSet hU.2.2.1
    (hfs.uniformContinuous_of_continuous hfc.continuous) hzero hf
  have hsol := tendsto_norm_cellAverageLp_sub_classical hU.1.measurableSet hU.2.2.1
    hu huLp
  filter_upwards [ae_tendsto_sampled_killedResolvent h619 h66 h37 h637 hd P a ha
    hU hbound hu] with ξ hξ
  rw [show hf'.toLp f = hf.toLp f from rfl] at hid
  simp only [hid]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun ε => ?_) (by simpa only [add_zero] using (hforce.add hξ).add hsol)
  let A := resolvent (discreteKilledSemigroup hd ε.property ha.lam_pos
    (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
  let π := cellAverageLp ε.property hU.1.measurableSet hU.2.2.1
  let F := (memLp_latticeMeasure ε.property hU.2.2.1
    (fun q => f (physical ε q))).toLp (fun q => f (physical ε q))
  let V := (memLp_latticeMeasure ε.property hU.2.2.1
    (fun q => u (physical ε q))).toLp (fun q => u (physical ε q))
  change ‖A (π (hf.toLp f)) - π (huLp.toLp u)‖ ≤
    ‖π (hf.toLp f) - F‖ + ‖A F - V‖ + ‖π (huLp.toLp u) - V‖
  have hA : ‖A (π (hf.toLp f)) - A F‖ ≤ ‖π (hf.toLp f) - F‖ := by
    rw [← map_sub]
    simpa only [inv_one, one_mul] using
      A.le_of_opNorm_le (norm_resolvent_le _ zero_lt_one) (π (hf.toLp f) - F)
  calc
    _ = ‖(A (π (hf.toLp f)) - A F) + (A F - V) +
        (V - π (huLp.toLp u))‖ := by congr 1; abel
    _ ≤ ‖A (π (hf.toLp f)) - A F‖ + ‖A F - V‖ +
        ‖V - π (huLp.toLp u)‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by rw [norm_sub_rev V]; exact add_le_add (add_le_add hA le_rfl) le_rfl

/-- One event gives cell-average resolvent convergence on dense families for all radii. -/
theorem exists_dense_family_ae_cellAverage_resolvent
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (ha : AssumptionU P lam a)
    {μB : Measure (BrownianPath d)} (hμB : IsStandardBrownianLaw μB) :
    ∃ (f : {R : ℕ // 1 ≤ R} → ℕ → (Fin d → ℝ) → ℝ)
      (hf : ∀ R k, MemLp (f R k) 2 (volume.restrict (continuumDomain R.val))),
      (∀ R, DenseRange (fun k => (hf R k).toLp (f R k))) ∧
      (∀ R k, ContDiff ℝ ∞ (f R k) ∧ HasCompactSupport (f R k) ∧
        tsupport (f R k) ⊆ continuumDomain R.val) ∧
      ∀ᵐ ξ ∂P, ∀ R k,
        let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2)
          (show (0 : ℝ) < R.val by exact_mod_cast (lt_of_lt_of_le
            Nat.zero_lt_one R.property))
        Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
          ‖resolvent (discreteKilledSemigroup hd ε.property ha.lam_pos
              (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
              (cellAverageLp ε.property hU.1.measurableSet hU.2.2.1
                ((hf R k).toLp (f R k))) -
            cellAverageLp ε.property hU.1.measurableSet hU.2.2.1
              (resolvent (continuumSemigroup R.val
                (meanConductance P hd a / (2 * d)) hμB) 1 zero_lt_one
                ((hf R k).toLp (f R k)))‖)
          (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  have hR (R : {R : ℕ // 1 ≤ R}) : (0 : ℝ) < R.val := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one R.property)
  have hex (R : {R : ℕ // 1 ≤ R}) :=
    exists_dense_classical_family h614 hd (hR R) (continuum_coefficient_pos ha hd)
  choose f u hf M hdense hreg using hex
  refine ⟨f, hf, hdense, ?_, ?_⟩
  · intro R k
    exact ⟨(hreg R k).1, (hreg R k).2.1, (hreg R k).2.2.1⟩
  · apply ae_all_iff.mpr
    intro R
    apply ae_all_iff.mpr
    intro k
    exact ae_tendsto_classical_cellAverage_resolvent h619 h66 h37 h637 hd P a ha
      (hR R) hμB (hreg R k).1 (hreg R k).2.1 (hreg R k).2.2.1
      (hreg R k).2.2.2.2 (hf R k)

/-- Uniformly bounded linear errors vanish everywhere if they vanish on a dense family. -/
theorem tendsto_norm_of_dense_family {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {ι : Type*} {K : ι → Type*}
    [∀ i, NormedAddCommGroup (K i)] [∀ i, NormedSpace ℝ (K i)]
    (A : ∀ i, H →L[ℝ] K i) (hA : ∀ i, ‖A i‖ ≤ 2)
    {l : Filter ι} {v : ℕ → H} (hv : DenseRange v)
    (hlim : ∀ k, Tendsto (fun i => ‖A i (v k)‖) l (𝓝 0)) (f : H) :
    Tendsto (fun i => ‖A i f‖) l (𝓝 0) := by
  have hLip (i : ι) : LipschitzWith 2 (fun f => ‖A i f‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist ‖A i x‖ ‖A i y‖ ≤ ‖A i x - A i y‖ := dist_norm_norm_le _ _
      _ = ‖A i (x - y)‖ := by rw [map_sub]
      _ ≤ 2 * ‖x - y‖ := (A i).le_of_opNorm_le (hA i) _
      _ = (2 : ℝ≥0) * dist x y := by rw [dist_eq_norm]; rfl
  exact hv.induction_on f
    ((LipschitzWith.uniformEquicontinuous _ 2 hLip).equicontinuous.isClosed_setOf_tendsto
      continuous_const) hlim

/-- Almost sure resolvent convergence holds for every datum on every integer-radius ball. -/
theorem ae_tendsto_resolvent
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (ha : AssumptionU P lam a)
    {μB : Measure (BrownianPath d)} (hμB : IsStandardBrownianLaw μB) :
    ∀ᵐ ξ ∂P, ∀ R : ℕ, ∀ hR : 1 ≤ R,
      let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2)
        (show (0 : ℝ) < R by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
      ∀ f : Lp ℝ 2 (volume.restrict (continuumDomain R)),
        Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
          ‖resolvent (discreteKilledSemigroup hd ε.property ha.lam_pos
              (a ξ) (ha.bounds ξ) hU.2.2.1) 1 zero_lt_one
              (cellAverageLp ε.property hU.1.measurableSet hU.2.2.1 f) -
            cellAverageLp ε.property hU.1.measurableSet hU.2.2.1
              (resolvent (continuumSemigroup R
                (meanConductance P hd a / (2 * d)) hμB) 1 zero_lt_one f)‖)
          (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  obtain ⟨v, hv, hdense, _, hevent⟩ :=
    exists_dense_family_ae_cellAverage_resolvent h619 h66 h37 h637 h614 hd P a ha hμB
  filter_upwards [hevent] with ξ hξ
  intro R hR
  dsimp only
  let r : {R : ℕ // 1 ≤ R} := ⟨R, hR⟩
  let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2)
    (show (0 : ℝ) < R by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
  let B := resolvent (continuumSemigroup R
    (meanConductance P hd a / (2 * d)) hμB) 1 zero_lt_one
  let π (ε : {ε : ℝ // 0 < ε}) :=
    cellAverageLp ε.property hU.1.measurableSet hU.2.2.1
  let D (ε : {ε : ℝ // 0 < ε}) := resolvent
    (discreteKilledSemigroup hd ε.property ha.lam_pos (a ξ) (ha.bounds ξ) hU.2.2.1)
    1 zero_lt_one
  let A (ε : {ε : ℝ // 0 < ε}) := (D ε).comp (π ε) - (π ε).comp B
  have hB : ‖B‖ ≤ 1 := by simpa only [inv_one] using norm_resolvent_le _ zero_lt_one
  have hD (ε) : ‖D ε‖ ≤ 1 := by
    simpa only [inv_one] using norm_resolvent_le _ zero_lt_one
  have hπ (ε) : ‖π ε‖ ≤ 1 := norm_cellAverageLp_le _ _ _
  have hA (ε) : ‖A ε‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    have hleft := (D ε).opNorm_comp_le (π ε)
    have hright := (π ε).opNorm_comp_le B
    have hleft' : ‖(D ε).comp (π ε)‖ ≤ 1 :=
      hleft.trans (by nlinarith [hD ε, hπ ε, norm_nonneg (D ε), norm_nonneg (π ε)])
    have hright' : ‖(π ε).comp B‖ ≤ 1 :=
      hright.trans (by nlinarith [hπ ε, hB, norm_nonneg (π ε), norm_nonneg B])
    linarith
  intro f
  exact tendsto_norm_of_dense_family A hA (hdense r) (hξ r) f

end

end LongRange
