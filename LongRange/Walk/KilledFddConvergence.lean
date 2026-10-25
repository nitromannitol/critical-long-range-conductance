import LongRange.Walk.KilledFdd
import LongRange.Walk.BoundaryCells
import LongRange.Walk.Pairing
import LongRange.Walk.ContinuumSemigroup
import LatticeProb.Topology.EpsFilter
import LatticeProb.Analysis.BackwardRecursion
import LatticeProb.Prob.BrownianDirichlet.KilledFdd

/-!
# Convergence of finite killed observations

Cell averaging intertwines bounded observations asymptotically. Boundary-cell estimates
supply the terminal constant, and contraction propagates convergence through finite products.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.ContractionSemigroup
open scoped NNReal Topology BoundedContinuousFunction

noncomputable section

variable {d : ℕ}

/-- The coordinate image of a Euclidean ball is the Euclidean radius sublevel. -/
theorem continuumDomain_eq_radius (R : ℝ) :
    continuumDomain (d := d) R = {x : Fin d → ℝ | radius x < R} := by
  ext x
  simp only [continuumDomain, Set.mem_image, Metric.mem_ball, dist_zero_right,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change radius (WithLp.ofLp y) < R
    rw [radius_norm, WithLp.toLp_ofLp]
    exact hy
  · intro hx
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    simpa only [← radius_norm] using hx

/-- Pairing a varying convergent vector with a fixed averaged vector preserves the limit. -/
theorem tendsto_inner_cellAverageLp_varying
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    (hfront : volume (frontier U) = 0) (ε : ℕ → {ε : ℝ // 0 < ε})
    (hε : Tendsto ε atTop (comap Subtype.val (𝓝[>] (0 : ℝ))))
    (g f : Lp ℝ 2 (volume.restrict U)) (fn : ∀ n, discreteL2 (ε n) U)
    (hf : VaryingConverges (fun n => cellAverageLp (ε n).property hU hb) fn f) :
    Tendsto (fun n => inner ℝ (cellAverageLp (ε n).property hU hb g) (fn n))
      atTop (𝓝 (inner ℝ g f)) := by
  have herr : Tendsto (fun n =>
      inner ℝ (cellAverageLp (ε n).property hU hb g)
        (fn n - cellAverageLp (ε n).property hU hb f)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (by simpa only [mul_zero] using hf.const_mul ‖g‖)
    intro n
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (norm_cellAverageLinearMap_le (ε n).property hU hb g) (norm_nonneg _))
  have hpair := (tendsto_inner_cellAverageLp hU hb hfront g f).comp hε
  simpa only [Function.comp_def, inner_sub_right, sub_add_cancel, zero_add] using herr.add hpair

/-- Constant-one lattice vectors converge to the constant-one L² class on a ball. -/
theorem varyingConverges_one {R : ℝ} (hR : 0 < R)
    (hU : MeasurableSet (continuumDomain (d := d) R))
    (hb : Bornology.IsBounded (continuumDomain (d := d) R))
    (ε : ℕ → {ε : ℝ // 0 < ε})
    (hε : Tendsto ε atTop (comap Subtype.val (𝓝[>] (0 : ℝ))))
    (h1 : MemLp (fun _ : Fin d → ℝ => (1 : ℝ)) 2
      (volume.restrict (continuumDomain (d := d) R))) :
    VaryingConverges (fun n => cellAverageLp (ε n).property hU hb)
      (fun n => (memLp_latticeMeasure (ε n).property hb (fun _ => 1)).toLp _)
      (h1.toLp _) := by
  have ht := (Real.continuous_sqrt.tendsto _).comp
    ((tendsto_one_sub_cellAverage (d := d) hR).comp (tendsto_comap.comp hε))
  have he (n : ℕ) :
      ‖(memLp_latticeMeasure (ε n).property hb (fun _ => (1 : ℝ))).toLp _ -
        cellAverageLp (ε n).property hU hb (h1.toLp _)‖ =
      Real.sqrt (l2NormSq (ε n) (continuumDomain (d := d) R)
        (fun q => 1 - cellAverage (ε n) (continuumDomain (d := d) R)
          (fun _ => 1) q)) := by
    rw [cellAverageLp_toLp _ _ _ h1, ← MemLp.toLp_sub]
    have hn := norm_sq_toLp_latticeMeasure (ε n).property hb
      (fun q => 1 - cellAverage (ε n) (continuumDomain R) (fun _ => 1) q)
    rw [← hn, Real.sqrt_sq_eq_abs, abs_norm]
    rfl
  change Tendsto (fun n => ‖_ - _‖) atTop (𝓝 0)
  simp only [Function.comp_def, Real.sqrt_zero] at ht
  simpa only [← continuumDomain_eq_radius, ← he] using ht

/-- Initial full-space averages agree with domain averages for a density zero off the domain. -/
theorem full_cellAverage_toLp_eq {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    {g : (Fin d → ℝ) → ℝ} (hg : MemLp g 2 (volume.restrict U))
    (hzero : ∀ y, y ∉ U → g y = 0) :
    (memLp_latticeMeasure hε hb (cellAverage ε Set.univ g)).toLp _ =
      cellAverageLp hε hU hb (hg.toLp g) := by
  rw [cellAverageLp_toLp hε hU hb hg]
  apply MemLp.toLp_congr
  apply Eventually.of_forall
  intro q
  unfold cellAverage
  congr 2
  funext y
  rw [Set.indicator_univ]
  by_cases hy : y ∈ U
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, hzero y hy]

/-- Marks in a finite coordinate schedule are Borel measurable in Euclidean space. -/
private theorem measurable_observation_marks (k : ℕ) (δ : Fin k → ℝ≥0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    ∀ a ∈ List.ofFn (fun i => (δ i,
      fun x : EuclideanSpace ℝ (Fin d) => φ i (EuclideanSpace.equiv (Fin d) ℝ x))),
      Measurable a.2 := by
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact ((φ i).continuous.comp (EuclideanSpace.equiv (Fin d) ℝ).continuous).measurable

/-- The uniform norms bound every mark in the finite Euclidean schedule. -/
private theorem bounded_observation_marks (k : ℕ) (δ : Fin k → ℝ≥0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    ∀ a ∈ List.ofFn (fun i => (δ i,
      fun x : EuclideanSpace ℝ (Fin d) => φ i (EuclideanSpace.equiv (Fin d) ℝ x))),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |a.2 y| ≤ C := by
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact ⟨‖φ i‖, norm_nonneg _, fun y => by
    simpa only [Real.norm_eq_abs] using (φ i).norm_coe_le_norm
      (EuclideanSpace.equiv (Fin d) ℝ y)⟩

/-- The coordinate class of the genuine Brownian backward kernel for a finite schedule. -/
def continuumKilledProduct (R a₀ : ℝ) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (k : ℕ) (δ : Fin k → ℝ≥0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    Lp ℝ 2 (volume.restrict (continuumDomain (d := d) R)) :=
  coordLp R ((memLp_killedProductKernel (B := Metric.ball 0 R) Metric.isOpen_ball
    (Real.sqrt (2 * a₀)) hμ _ (measurable_observation_marks k δ φ)
    (bounded_observation_marks k δ φ)).toLp _)

/-- Coordinate transport commutes with multiplication by a coordinate mark. -/
private theorem coordLp_mul (R : ℝ) (φ : (Fin d → ℝ) →ᵇ ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : MemLp f 2 (volume.restrict (Metric.ball 0 R)))
    (hφf : MemLp (fun x => φ (EuclideanSpace.equiv (Fin d) ℝ x) * f x)
      2 (volume.restrict (Metric.ball 0 R))) :
    coordLp R (hφf.toLp _) = mulLp (continuumDomain R) φ (coordLp R (hf.toLp _)) := by
  change Lp.compMeasurePreserving _ _ _ = _
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  filter_upwards [(hφf.comp_measurePreserving (coord_symm_measurePreserving R)).coeFn_toLp,
    mulLp_apply (continuumDomain R) φ (coordLp R (hf.toLp f)),
    (hf.comp_measurePreserving (coord_symm_measurePreserving R)).coeFn_toLp]
    with x hx hy hz
  rw [hx, hy]
  change _ = φ x * (Lp.compMeasurePreserving _ _ (hf.toLp f)) x
  rw [Lp.toLp_compMeasurePreserving, hz]
  rfl

/-- The transported Brownian kernel follows the same recursion as the killed walk. -/
private theorem continuumKilledProduct_succ (R a₀ : ℝ) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (k : ℕ) (δ : Fin (k + 1) → ℝ≥0)
    (φ : Fin (k + 1) → ((Fin d → ℝ) →ᵇ ℝ)) :
    continuumKilledProduct R a₀ hμ (k + 1) δ φ =
      (continuumSemigroup R a₀ hμ).operator (δ 0)
        (mulLp (continuumDomain R) (φ 0)
          (continuumKilledProduct R a₀ hμ k (fun i => δ i.succ) (fun i => φ i.succ))) := by
  let rest := List.ofFn (fun i : Fin k => (δ i.succ,
    fun x : EuclideanSpace ℝ (Fin d) => φ i.succ (EuclideanSpace.equiv (Fin d) ℝ x)))
  obtain ⟨hdata, hout, heq⟩ := killedProductKernel_toLp_cons
    (B := Metric.ball 0 R) Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ (δ 0)
    (((φ 0).continuous.comp (EuclideanSpace.equiv (Fin d) ℝ).continuous).measurable)
    (norm_nonneg (φ 0)) (fun y => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using
        (φ 0).norm_coe_le_norm (EuclideanSpace.equiv (Fin d) ℝ y))
    rest (measurable_observation_marks k _ _) (bounded_observation_marks k _ _)
  unfold continuumKilledProduct
  simp only [List.ofFn_succ]
  change coordLp R (hout.toLp _) = _
  rw [heq]
  change coordLp R ((killedSemigroup Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ).operator
    (δ 0) (hdata.toLp _)) = coordLp R
      ((killedSemigroup Metric.isOpen_ball (Real.sqrt (2 * a₀)) hμ).operator
        (δ 0) ((coordLp R).symm _))
  congr 2
  rw [← coordLp_mul R (φ 0) _
    (memLp_killedProductKernel Metric.isOpen_ball _ hμ rest
      (measurable_observation_marks k _ _) (bounded_observation_marks k _ _)) hdata,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- The empty Brownian backward kernel transports to the constant-one coordinate class. -/
private theorem continuumKilledProduct_zero (R a₀ : ℝ) {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ)
    (δ : Fin 0 → ℝ≥0) (φ : Fin 0 → ((Fin d → ℝ) →ᵇ ℝ))
    (h1 : MemLp (fun _ : Fin d → ℝ => (1 : ℝ)) 2
      (volume.restrict (continuumDomain (d := d) R))) :
    continuumKilledProduct R a₀ hμ 0 δ φ = h1.toLp _ := by
  unfold continuumKilledProduct
  simp only [List.ofFn_zero, killedProductKernel]
  change Lp.compMeasurePreserving _ _ _ = _
  rw [Lp.toLp_compMeasurePreserving]
  rfl

/-- Finite killed backward products converge to the transported Brownian backward kernel. -/
theorem varyingConverges_killedBackwardProduct (hd : 1 ≤ d)
    {lam R : ℝ} (hlam : 0 < lam) (hR : 0 < R) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (a₀ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (hU : MeasurableSet (continuumDomain (d := d) R))
    (hb : Bornology.IsBounded (continuumDomain (d := d) R))
    (ε : ℕ → {ε : ℝ // 0 < ε})
    (hε : Tendsto ε atTop (comap Subtype.val (𝓝[>] (0 : ℝ))))
    (hconv : UniformSemigroupConvergence (fun n => cellAverageLp (ε n).property hU hb)
      (continuumSemigroup R a₀ hμ)
      (fun n => discreteKilledSemigroup hd (ε n).property hlam a ha hb))
    (k : ℕ) (δ : Fin k → ℝ≥0) (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    VaryingConverges (fun n => cellAverageLp (ε n).property hU hb)
      (fun n => killedBackwardProduct hd (ε n).property hlam a ha hb k δ φ)
      (continuumKilledProduct R a₀ hμ k δ φ) := by
  induction k with
  | zero =>
    letI : IsFiniteMeasure (volume.restrict (continuumDomain (d := d) R)) :=
      isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
    have h1 : MemLp (fun _ : Fin d → ℝ => (1 : ℝ)) 2
        (volume.restrict (continuumDomain (d := d) R)) := memLp_const 1
    rw [continuumKilledProduct_zero R a₀ hμ δ φ h1]
    exact varyingConverges_one hR hU hb ε hε h1
  | succ k ih =>
    rw [continuumKilledProduct_succ]
    have htail := ih (fun i => δ i.succ) (fun i => φ i.succ)
    have hmul := htail.map (mulLp (continuumDomain R) (φ 0))
      (fun n => mulDiscrete (ε n) (continuumDomain R) (φ 0))
      (fun n => norm_mulDiscrete_le _ _ _) (fun g =>
        (tendsto_mul_cellAverage_commutator hU hb (φ 0) g).comp hε)
    exact hmul.semigroup (continuumSemigroup R a₀ hμ)
      (fun n => discreteKilledSemigroup hd (ε n).property hlam a ha hb)
      (δ 0) (hconv.varyingConverges (δ 0))

/-- Killed walk product expectations converge to the Brownian product expectation under
its independent initial density, assuming uniform killed-semigroup convergence. -/
theorem tendsto_killed_product_expectation (hd : 1 ≤ d)
    {lam R : ℝ} (hlam : 0 < lam) (hR : 0 < R) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (a₀ : ℝ)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (hU : MeasurableSet (continuumDomain (d := d) R))
    (hb : Bornology.IsBounded (continuumDomain (d := d) R))
    (ε : ℕ → Eps)
    (hε : Tendsto ε atTop epsFilter)
    (hconv : UniformSemigroupConvergence (fun n => cellAverageLp (ε n).property.1 hU hb)
      (continuumSemigroup R a₀ hμ)
      (fun n => discreteKilledSemigroup hd (ε n).property.1 hlam a ha hb))
    (g : (Fin d → ℝ) → ℝ) (hgm : Measurable g) (hg : MemLp g 2 volume)
    (hc : HasCompactSupport g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∫ x, g x = 1)
    (hsupp : Function.support g ⊆ continuumDomain (d := d) (R / 2))
    (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    Tendsto (fun n => ∫ h, {h : JumpChain.RegularHistory (Site d) |
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet (ε n) (continuumDomain R)}.indicator
      (fun h => ∏ i : Fin k, φ i (physical (ε n) (h.position (t i.succ)))) h
        ∂(walkRates hd (ε n).property.1 hlam a ha).regularLaw
          (initialLaw (ε n) g (ε n).property.1 (integrable_initial_density hg hc)
            (Eventually.of_forall hg0) hg1 : Measure (Site d)))
      atTop (𝓝 (∫ p, killedProduct (Metric.ball 0 R) (Real.sqrt (2 * a₀))
        (List.ofFn (fun i => (t i.succ - t i.castSucc,
          fun x : EuclideanSpace ℝ (Fin d) => φ i (EuclideanSpace.equiv (Fin d) ℝ x))))
        p.1 p.2 ∂(((volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)).withDensity
          (fun x => ENNReal.ofReal (g (EuclideanSpace.equiv (Fin d) ℝ x)))).prod μ))) := by
  let εpos : ℕ → {ε : ℝ // 0 < ε} := fun n => ⟨(ε n).val, (ε n).property.1⟩
  have hεpos : Tendsto εpos atTop (comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [tendsto_comap_iff, tendsto_nhdsWithin_iff]
    exact ⟨tendsto_epsFilter_iff.mp hε,
      Eventually.of_forall (fun n => (ε n).property.1)⟩
  have hzero : ∀ x, x ∉ continuumDomain (d := d) R → g x = 0 := by
    intro x hx
    by_contra hne
    have hs := hsupp (Function.mem_support.mpr hne)
    rw [continuumDomain_eq_radius] at hs hx
    exact hx (show radius x < R by dsimp only [Set.mem_setOf_eq] at hs; linarith)
  have hfront : volume (frontier (continuumDomain (d := d) R)) = 0 := by
    rw [continuumDomain_eq_radius]
    exact measure_mono_null (frontier_lt_subset_eq (radius_continuous d) continuous_const)
      (volume_radius_eq_zero hR)
  have hLp : MemLp g 2 (volume.restrict (continuumDomain (d := d) R)) :=
    hg.restrict _
  have hLpE := hLp.comp_measurePreserving (coord_measurePreserving (d := d) R)
  have hcoord : coordLp R (hLpE.toLp _) = hLp.toLp g := by
    change Lp.compMeasurePreserving _ _ _ = _
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    exact Eventually.of_forall (fun x => congrArg g
      ((EuclideanSpace.equiv (Fin d) ℝ).apply_symm_apply x))
  have hprob : ∫⁻ x, ENNReal.ofReal (g (EuclideanSpace.equiv (Fin d) ℝ x))
      ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)) = 1 := by
    have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        g (EuclideanSpace.equiv (Fin d) ℝ x)) (volume.restrict (Metric.ball 0 R)) :=
      (coord_measurePreserving (d := d) R).integrable_comp_of_integrable
        (integrable_initial_density hg hc).integrableOn
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => hg0 _))]
    rw [(coord_measurePreserving (d := d) R).integral_comp
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding g]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero, hg1, ENNReal.ofReal_one]
  letI : IsFiniteMeasure (volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hid := killed_product_density_inner (B := Metric.ball 0 R) Metric.isOpen_ball
    (Real.sqrt (2 * a₀)) hμ
    (List.ofFn (fun i => (t i.succ - t i.castSucc,
      fun x : EuclideanSpace ℝ (Fin d) => φ i (EuclideanSpace.equiv (Fin d) ℝ x))))
    (measurable_observation_marks k _ φ) (bounded_observation_marks k _ φ)
    (hgm.comp (EuclideanSpace.equiv (Fin d) ℝ).continuous.measurable)
    (fun x => hg0 _) hLpE hprob
  simp only [Function.comp_def] at hid hcoord
  rw [hid, ← (coordLp (d := d) R).inner_map_map, hcoord]
  have hprod := varyingConverges_killedBackwardProduct hd hlam hR a ha a₀ hμ hU hb
    εpos hεpos hconv k (fun i => t i.succ - t i.castSucc) φ
  have hpair := tendsto_inner_cellAverageLp_varying hU hb hfront εpos hεpos
    (hLp.toLp g) _ _ hprod
  convert hpair using 1
  · funext n
    rw [initialLaw_killed_product_expectation_eq_inner hd (ε n).property.1 hlam a ha hb
      g (integrable_initial_density hg hc) (Eventually.of_forall hg0) hg1 k t ht ht0 φ,
      full_cellAverage_toLp_eq (ε n).property.1 hU hb hLp hzero]
  · rfl

end

end LongRange
