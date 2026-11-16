import LongRangeHeat.Annealed
import LongRangeHeat.Statements.HeatKernelBounds
import LongRange.Walk.Compactness

/-!
# Aldous' criterion for the rescaled walk

The displacement bound of Proposition 4.1 and the Markov property of the jump chain at
deterministic times control the increment of the walk after a stopping time of the canonical
filtration of path space. Stopping times are approximated from above by dyadic stopping times,
and the right continuity of paths transfers the bound to the limit.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.JumpChain LatticeProb.Euclidean.Lattice
open scoped ENNReal NNReal
open LongRange (Edge walkRates walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The canonical filtration of path space: the information of the coordinate process up to time
`t`. -/
abbrev canonicalSigma (d : ℕ) (t : ℝ≥0) : MeasurableSpace (PathSpace d) :=
  naturalSigma (id : PathSpace d → PathSpace d) t

theorem measurableSet_preimage_halfLinePath {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0)
    {A : Set (PathSpace d)} (hA : MeasurableSet[canonicalSigma d t] A) :
    MeasurableSet[BoundedRates.naturalSigma t]
      (RegularHistory.halfLinePath (walkEmbed ε) ⁻¹' A) := by
  rw [← naturalSigma_halfLinePath_eq (walkEmbed ε) (LongRange.walkEmbed_injective hε) t]
  have : MeasurableSpace.comap (RegularHistory.halfLinePath (walkEmbed ε))
      (canonicalSigma d t) =
      naturalSigma (RegularHistory.halfLinePath (walkEmbed ε)) t := by
    simp only [canonicalSigma, naturalSigma, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    rfl
  rw [← this]
  exact ⟨A, hA, rfl⟩

/-- Markov property at a deterministic time: on an event of the canonical filtration at time `t`,
the probability that the walk moves by more than `η` during the next `u` units of time is at most
`b`, whenever `b` bounds the displacement probability of every starting point. -/
theorem quenchedLaw_inter_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (t u : ℝ≥0)
    {A : Set (PathSpace d)} (hA : MeasurableSet[canonicalSigma d t] A) (η : ℝ) (b : ℝ≥0∞)
    (hK : ∀ y, (walkRates hd hε hlam a ha).transitionKernel u y
      {z | η < dist (walkEmbed ε z) (walkEmbed ε y)} ≤ b) :
    (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d))
        (A ∩ {X | η < dist (X.1 (t + u)) (X.1 t)}) ≤
      b * (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d)) A := by
  set rates := walkRates hd hε hlam a ha with hrates
  have hAm : MeasurableSet A :=
    naturalSigma_le (id : PathSpace d → PathSpace d) (fun s => measurable_eval s) t A hA
  have hDm : MeasurableSet {X : PathSpace d | η < dist (X.1 (t + u)) (X.1 t)} :=
    measurableSet_lt measurable_const
      ((measurable_eval (t + u)).dist (measurable_eval t))
  rw [quenchedLaw_apply hd hε hlam a ha x (hAm.inter hDm), quenchedLaw_apply hd hε hlam a ha x hAm]
  set A' := RegularHistory.halfLinePath (walkEmbed ε) ⁻¹' A with hA'
  set D' : Set (RegularHistory (Site d)) :=
    {h | η < dist (walkEmbed ε (h.position (t + u))) (walkEmbed ε (h.position t))} with hD'
  have hD'm : MeasurableSet D' :=
    measurableSet_lt measurable_const
      (((measurable_of_countable (walkEmbed ε)).comp
        (RegularHistory.measurable_position (t + u))).dist
        ((measurable_of_countable (walkEmbed ε)).comp (RegularHistory.measurable_position t)))
  have hpre : RegularHistory.halfLinePath (walkEmbed ε) ⁻¹'
      (A ∩ {X | η < dist (X.1 (t + u)) (X.1 t)}) = A' ∩ D' := rfl
  rw [hpre]
  let g : Site d → Site d → ℝ≥0∞ := fun x y =>
    if η < dist (walkEmbed ε y) (walkEmbed ε x) then 1 else 0
  have hg : Measurable (Function.uncurry g) := measurable_of_countable _
  have hmk := rates.setLIntegral_markov (Measure.dirac x) t u A'
    (measurableSet_preimage_halfLinePath hε t hA) g hg
  have hLHS : ∫⁻ h in A', g (h.position t) (h.position (t + u))
      ∂rates.regularLaw (Measure.dirac x) = rates.regularLaw (Measure.dirac x) (A' ∩ D') := by
    have : (fun h : RegularHistory (Site d) => g (h.position t) (h.position (t + u))) =
        D'.indicator 1 := by
      funext h
      simp only [g, Set.indicator_apply, hD', Set.mem_ofPred_eq, Pi.one_apply]
    rw [this, lintegral_indicator_one hD'm, Measure.restrict_apply hD'm, Set.inter_comm]
  have hinner : ∀ y : Site d, ∑' z, rates.transitionKernel u y {z} * g y z ≤ b := by
    intro y
    have : ∀ z, rates.transitionKernel u y {z} * g y z =
        {z | η < dist (walkEmbed ε z) (walkEmbed ε y)}.indicator
          (fun z => rates.transitionKernel u y {z}) z := by
      intro z
      simp only [g, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs <;> simp
    simp_rw [this]
    rw [Measure.tsum_indicator_apply_singleton _ _ (Set.to_countable _).measurableSet]
    exact hK y
  rw [← hLHS, hmk]
  calc ∫⁻ h in A', ∑' z, rates.transitionKernel u (h.position t) {z} * g (h.position t) z
        ∂rates.regularLaw (Measure.dirac x)
      ≤ ∫⁻ h in A', b ∂rates.regularLaw (Measure.dirac x) :=
        lintegral_mono fun h => hinner _
    _ = b * rates.regularLaw (Measure.dirac x) A' := by
        rw [setLIntegral_const]

theorem canonicalSigma_mono {s t : ℝ≥0} (hst : s ≤ t) :
    canonicalSigma d s ≤ canonicalSigma d t :=
  biSup_mono fun _ hr => hr.trans hst

theorem canonicalSigma_le (t : ℝ≥0) : canonicalSigma d t ≤ (inferInstance : MeasurableSpace (PathSpace d)) :=
  naturalSigma_le (id : PathSpace d → PathSpace d) (fun s => measurable_eval s) t

section Dyadic

variable (τ : PathSpace d → ℝ)

/-- The dyadic grid point of mesh `2⁻ᵏ` at or above `τ X`, as the index `⌈2ᵏ τ X⌉`. -/
def dyadicIndex (k : ℕ) (X : PathSpace d) : ℕ := ⌈(2 : ℝ) ^ k * τ X⌉₊

/-- The grid point of mesh `2⁻ᵏ` with index `j`. -/
def gridPoint (k j : ℕ) : ℝ≥0 := (j : ℝ≥0) / 2 ^ k

variable {τ}

theorem dyadicIndex_le_iff (k : ℕ) (X : PathSpace d) (i : ℕ) :
    dyadicIndex τ k X ≤ i ↔ τ X ≤ (gridPoint k i : ℝ) := by
  unfold dyadicIndex gridPoint
  rw [Nat.ceil_le]
  push_cast
  rw [le_div_iff₀ (by positivity), mul_comm]

theorem measurableSet_dyadicIndex_le (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t})
    (k i : ℕ) :
    MeasurableSet[canonicalSigma d (gridPoint k i)] {X | dyadicIndex τ k X ≤ i} := by
  simp_rw [dyadicIndex_le_iff]
  exact hτ _

theorem measurableSet_dyadicIndex_eq (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t})
    (k j : ℕ) :
    MeasurableSet[canonicalSigma d (gridPoint k j)] {X | dyadicIndex τ k X = j} := by
  have hmono : ∀ i, i ≤ j → canonicalSigma d (gridPoint k i) ≤ canonicalSigma d (gridPoint k j) :=
    fun i hij => canonicalSigma_mono (by
      unfold gridPoint
      gcongr)
  have : {X : PathSpace d | dyadicIndex τ k X = j} = {X | dyadicIndex τ k X ≤ j} ∩
      ⋂ i ∈ Finset.range j, {X | dyadicIndex τ k X ≤ i}ᶜ := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      Finset.mem_range, not_le]
    constructor
    · intro h
      exact ⟨h.le, fun i hi => h ▸ hi⟩
    · rintro ⟨h1, h2⟩
      by_contra hne
      exact absurd (h2 _ (lt_of_le_of_ne h1 hne)) (lt_irrefl _)
  rw [this]
  refine (measurableSet_dyadicIndex_le hτ k j).inter ?_
  refine @MeasurableSet.biInter _ _ (canonicalSigma d (gridPoint k j)) _ _
    (Finset.range j).countable_toSet fun i hi => ?_
  exact (hmono i (Finset.mem_range.mp hi).le _
    (measurableSet_dyadicIndex_le hτ k i).compl)

/-- The event that the increment after the dyadic approximation of `τ` exceeds `η`. -/
def dyadicEvent (τ : PathSpace d → ℝ) (k : ℕ) (u : ℝ≥0) (η : ℝ) : Set (PathSpace d) :=
  {X | η < dist (X.1 (gridPoint k (dyadicIndex τ k X) + u)) (X.1 (gridPoint k (dyadicIndex τ k X)))}

theorem dyadicEvent_eq (k : ℕ) (u : ℝ≥0) (η : ℝ) :
    dyadicEvent τ k u η = ⋃ j : ℕ, ({X | dyadicIndex τ k X = j} ∩
      {X | η < dist (X.1 (gridPoint k j + u)) (X.1 (gridPoint k j))}) := by
  ext X
  simp only [dyadicEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨_, rfl, h⟩
  · rintro ⟨j, hj, h⟩
    subst hj
    exact h

theorem measurableSet_dyadicEvent (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t})
    (k : ℕ) (u : ℝ≥0) (η : ℝ) : MeasurableSet (dyadicEvent τ k u η) := by
  rw [dyadicEvent_eq]
  refine MeasurableSet.iUnion fun j => ?_
  exact (canonicalSigma_le _ _ (measurableSet_dyadicIndex_eq hτ k j)).inter
    (measurableSet_lt measurable_const
      ((measurable_eval _).dist (measurable_eval _)))

/-- The quenched probability that the increment after the dyadic approximation of a stopping time
exceeds `η` is at most the uniform displacement bound. -/
theorem quenchedLaw_dyadicEvent_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t}) (k : ℕ) (u : ℝ≥0)
    (η : ℝ) (b : ℝ≥0∞)
    (hK : ∀ y, (walkRates hd hε hlam a ha).transitionKernel u y
      {z | η < dist (walkEmbed ε z) (walkEmbed ε y)} ≤ b) :
    (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d)) (dyadicEvent τ k u η) ≤ b := by
  set ν : Measure (PathSpace d) := (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d))
    with hν
  have : IsProbabilityMeasure ν := inferInstance
  have hAm : ∀ j, MeasurableSet {X : PathSpace d | dyadicIndex τ k X = j} := fun j =>
    canonicalSigma_le _ _ (measurableSet_dyadicIndex_eq hτ k j)
  have hdisj : Pairwise (Function.onFun Disjoint fun j : ℕ => {X : PathSpace d | dyadicIndex τ k X = j}) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro X hi hj
    exact hij (hi.symm.trans hj)
  have hunion : (⋃ j : ℕ, {X : PathSpace d | dyadicIndex τ k X = j}) = Set.univ := by
    ext X
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨_, rfl⟩
  rw [dyadicEvent_eq]
  calc ν (⋃ j : ℕ, ({X | dyadicIndex τ k X = j} ∩
        {X | η < dist (X.1 (gridPoint k j + u)) (X.1 (gridPoint k j))}))
      ≤ ∑' j : ℕ, ν ({X | dyadicIndex τ k X = j} ∩
        {X | η < dist (X.1 (gridPoint k j + u)) (X.1 (gridPoint k j))}) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, b * ν {X | dyadicIndex τ k X = j} :=
        ENNReal.tsum_le_tsum fun j =>
          quenchedLaw_inter_le hd hε hlam a ha x (gridPoint k j) u
            (measurableSet_dyadicIndex_eq hτ k j) η b hK
    _ = b * ν (⋃ j : ℕ, {X | dyadicIndex τ k X = j}) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj hAm]
    _ = b := by rw [hunion, measure_univ, mul_one]

theorem gridPoint_dyadicIndex_bounds (k : ℕ) (X : PathSpace d) (h0 : 0 ≤ τ X) :
    τ X ≤ (gridPoint k (dyadicIndex τ k X) : ℝ) ∧
      (gridPoint k (dyadicIndex τ k X) : ℝ) ≤ τ X + (1 / 2) ^ k := by
  unfold gridPoint dyadicIndex
  push_cast
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hnn : 0 ≤ (2 : ℝ) ^ k * τ X := mul_nonneg h2.le h0
  constructor
  · rw [le_div_iff₀ h2, mul_comm]
    exact Nat.le_ceil _
  · rw [div_le_iff₀ h2, add_mul, one_div_pow, one_div, inv_mul_cancel₀ h2.ne']
    have := (Nat.ceil_lt_add_one hnn).le
    linarith

theorem tendsto_gridPoint (X : PathSpace d) (h0 : 0 ≤ τ X) :
    Filter.Tendsto (fun k => gridPoint k (dyadicIndex τ k X)) Filter.atTop
      (nhds (τ X).toNNReal) := by
  rw [← NNReal.tendsto_coe]
  have hc : ((τ X).toNNReal : ℝ) = τ X := Real.coe_toNNReal _ h0
  rw [hc]
  have h12 : Filter.Tendsto (fun k : ℕ => τ X + (1 / 2 : ℝ) ^ k) Filter.atTop (nhds (τ X)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
    (fun k => (gridPoint_dyadicIndex_bounds k X h0).1)
    (fun k => (gridPoint_dyadicIndex_bounds k X h0).2)

theorem tendsto_eval_of_ge (X : PathSpace d) {s : ℕ → ℝ≥0} {s₀ : ℝ≥0}
    (hs : Filter.Tendsto s Filter.atTop (nhds s₀)) (hge : ∀ k, s₀ ≤ s k) :
    Filter.Tendsto (fun k => X.1 (s k)) Filter.atTop (nhds (X.1 s₀)) :=
  (X.2.1 s₀).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hs, Filter.Eventually.of_forall hge⟩)

theorem subset_eventually_dyadicEvent (hτ0 : ∀ X, 0 ≤ τ X) (u : ℝ≥0) (η : ℝ) :
    {X : PathSpace d | η < dist (X.1 ((τ X).toNNReal + u)) (X.1 (τ X).toNNReal)} ⊆
      {X | ∀ᶠ k in Filter.atTop, X ∈ dyadicEvent τ k u η} := by
  intro X hX
  have hs := tendsto_gridPoint (τ := τ) X (hτ0 X)
  have hge : ∀ k, (τ X).toNNReal ≤ gridPoint k (dyadicIndex τ k X) := fun k => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hτ0 X)]
    exact (gridPoint_dyadicIndex_bounds k X (hτ0 X)).1
  have h1 := tendsto_eval_of_ge X hs hge
  have h2 := tendsto_eval_of_ge X (hs.add_const u) (fun k => add_le_add_left (hge k) u)
  exact (h2.dist h1).eventually (lt_mem_nhds hX)

theorem setOf_eventually_dyadicEvent (τ : PathSpace d → ℝ) (u : ℝ≥0) (η : ℝ) :
    {X : PathSpace d | ∀ᶠ k in Filter.atTop, X ∈ dyadicEvent τ k u η} =
      ⋃ N : ℕ, ⋂ k : ℕ, ⋂ (_ : N ≤ k), dyadicEvent τ k u η := by
  ext X
  simp only [Set.mem_ofPred_eq, Filter.eventually_atTop, Set.mem_iUnion, Set.mem_iInter]

theorem measurableSet_eventually_dyadicEvent
    (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t}) (u : ℝ≥0) (η : ℝ) :
    MeasurableSet {X : PathSpace d | ∀ᶠ k in Filter.atTop, X ∈ dyadicEvent τ k u η} := by
  rw [setOf_eventually_dyadicEvent]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_dyadicEvent hτ k u η

theorem quenchedLaw_stopping_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t}) (u : ℝ≥0)
    (η : ℝ) (b : ℝ≥0∞)
    (hK : ∀ y, (walkRates hd hε hlam a ha).transitionKernel u y
      {z | η < dist (walkEmbed ε z) (walkEmbed ε y)} ≤ b) :
    (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d))
      {X | ∀ᶠ k in Filter.atTop, X ∈ dyadicEvent τ k u η} ≤ b := by
  have hU := setOf_eventually_dyadicEvent τ u η
  have hmono : Monotone fun N : ℕ => ⋂ k : ℕ, ⋂ (_ : N ≤ k), dyadicEvent τ k u η := by
    intro N M hNM
    exact Set.iInter₂_mono' fun k hk => ⟨k, hNM.trans hk, subset_rfl⟩
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun N => ?_
  exact (measure_mono (Set.iInter₂_subset N le_rfl)).trans
    (quenchedLaw_dyadicEvent_le hd hε hlam a ha x hτ N u η b hK)

/-- Annealed form of the stopping bound: a uniform bound on the displacement probabilities of the
walk, valid for every realization of the conductances, bounds the annealed probability that the
increment after a stopping time of the canonical filtration exceeds `η`. -/
theorem annealedLaw_stopping_le (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {lam : ℝ} (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[canonicalSigma d t] {X | τ X ≤ t}) (hτ0 : ∀ X, 0 ≤ τ X)
    (u : ℝ≥0) (η : ℝ) (b : ℝ≥0∞)
    (hK : ∀ ω y, (walkRates hd hε hP.lam_mem.1 (a ω) (hP.bounds ω)).transitionKernel u y
      {z | η < dist (walkEmbed ε z) (walkEmbed ε y)} ≤ b) :
    (annealedLaw hd P a hP hε : Measure (PathSpace d))
      {X | η < dist (X.1 ((τ X).toNNReal + u)) (X.1 (τ X).toNNReal)} ≤ b := by
  have := hP.isProbabilityMeasure
  calc (annealedLaw hd P a hP hε : Measure (PathSpace d))
        {X | η < dist (X.1 ((τ X).toNNReal + u)) (X.1 (τ X).toNNReal)}
      ≤ (annealedLaw hd P a hP hε : Measure (PathSpace d))
        {X | ∀ᶠ k in Filter.atTop, X ∈ dyadicEvent τ k u η} :=
        measure_mono (subset_eventually_dyadicEvent hτ0 u η)
    _ = ∫⁻ ω, (quenchedLaw hd hε hP.lam_mem.1 (a ω) (hP.bounds ω) 0 : Measure (PathSpace d))
          {X | ∀ᶠ k in Filter.atTop, X ∈ dyadicEvent τ k u η} ∂P :=
        annealedLaw_apply hd P a hP hε (measurableSet_eventually_dyadicEvent hτ u η)
    _ ≤ ∫⁻ _ω, b ∂P :=
        lintegral_mono fun ω => quenchedLaw_stopping_le hd hε hP.lam_mem.1 (a ω) (hP.bounds ω) 0
          hτ u η b (hK ω)
    _ = b := by rw [lintegral_const, measure_univ, mul_one]

end Dyadic

end

end LongRangeHeat
