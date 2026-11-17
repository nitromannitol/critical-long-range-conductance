import LongRangeHeat.PathScaling
import LongRange.HeatKernel.Rescaled

/-!
# Annealed law of the unit walk

The unit-scale jump rates define quenched path laws which depend measurably on the
conductance field. Averaging these laws gives the annealed unit-walk law.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.JumpChain LatticeProb.Euclidean.Lattice
open scoped ENNReal NNReal
open LongRange (Edge unitRates unitRate walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The unit walk started at a lattice site, embedded in Euclidean space. -/
def unitQuenchedLaw (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) : ProbabilityMeasure (PathSpace d) :=
  pathLaw (unitRates hd hlam a ha) (Measure.dirac x) (walkEmbed 1)

/-- Unit jump rates depend measurably on the conductance field. -/
theorem measurable_unitRate {Ω : Type*} [MeasurableSpace Ω] (a : Ω → Edge d → ℝ)
    (hma : ∀ e, Measurable fun ω => a ω e) (x y : Site d) :
    Measurable fun ω => unitRate (a ω) x y := by
  unfold unitRate
  by_cases h : y - x = 0
  · simp only [h, dite_true]
    exact measurable_const
  · simp only [h, dite_false]
    exact (hma _).mul measurable_const

theorem unitQuenchedLaw_apply (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d)
    {B : Set (PathSpace d)} (hB : MeasurableSet B) :
    (unitQuenchedLaw hd hlam a ha x : Measure (PathSpace d)) B =
      (unitRates hd hlam a ha).regularLaw (Measure.dirac x)
        (RegularHistory.halfLinePath (walkEmbed 1) ⁻¹' B) := by
  unfold unitQuenchedLaw pathLaw
  change Measure.map (RegularHistory.halfLinePath (walkEmbed 1))
    ((unitRates hd hlam a ha).regularLaw (Measure.dirac x)) B = _
  rw [Measure.map_apply (measurable_halfLinePath _) hB]

theorem measurable_unitQuenchedLaw (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Type*} [MeasurableSpace Ω] (a : Ω → Edge d → ℝ)
    (ha : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹) (hma : ∀ e, Measurable fun ω => a ω e)
    (x : Site d) :
    Measurable fun ω => (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d)) := by
  set r : Ω → BoundedRates (Site d) := fun ω => unitRates hd hlam (a ω) (ha ω) with hr
  have hq : ∀ i j, Measurable fun ω => (r ω).q i j := fun i j =>
    measurable_unitRate a hma i j
  have hR : ∀ ω, (r ω).R = 2 * (lam⁻¹ * ∑' w : Site d, LongRange.jumpKernel (physical 1 w)) := fun ω => rfl
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  let m : Time → MeasurableSpace (PathSpace d) := fun t =>
    MeasurableSpace.comap (fun x : PathSpace d => x.1 t) inferInstance
  have hgen : (inferInstance : MeasurableSpace (PathSpace d)) = MeasurableSpace.generateFrom
      (piiUnionInter (fun t => {s | MeasurableSet[m t] s}) Set.univ) := by
    rw [generateFrom_piiUnionInter_measurableSet m Set.univ, iSup_univ]
    exact borel_eq_iSup_comap_eval
  refine MeasurableSpace.induction_on_inter
    (C := fun B _ => Measurable fun ω =>
      (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d)) B) hgen
    (isPiSystem_piiUnionInter _ (fun t => ?_) Set.univ) ?_ ?_ ?_ ?_ B hB
  · exact @MeasurableSpace.isPiSystem_measurableSet _ (m t)
  · simp only [measure_empty]
    exact measurable_const
  · intro s hs
    obtain ⟨F, -, f, hf, rfl⟩ := hs
    have hfA : ∀ u ∈ F, ∃ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A ∧
        (fun y : PathSpace d => y.1 u) ⁻¹' A = f u := fun u hu =>
      MeasurableSpace.measurableSet_comap.mp (hf u hu)
    choose! A hA hAf using hfA
    have hmeas : ∀ ω, (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d))
        (⋂ u ∈ F, f u) = (r ω).regularLaw (Measure.dirac x)
          {h | ∀ u ∈ F, h.position u ∈ walkEmbed 1 ⁻¹' A u} := by
      intro ω
      have hmf : MeasurableSet (⋂ u ∈ F, f u) := MeasurableSet.biInter F.countable_toSet
        fun u hu => by
          rw [← hAf u hu]
          exact measurable_eval u (hA u hu)
      rw [unitQuenchedLaw_apply hd hlam (a ω) (ha ω) x hmf]
      congr 1
      ext h
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
      refine forall₂_congr fun u hu => ?_
      rw [← hAf u hu]
      rfl
    simp_rw [hmeas]
    exact measurable_regularLaw_cylinder hq hR x F _
  · intro s hs ih
    have : ∀ ω, (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d)) sᶜ =
        1 - (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d)) s := fun ω =>
      prob_compl_eq_one_sub hs
    simp_rw [this]
    exact measurable_const.sub ih
  · intro f hdisj hfm ih
    have : ∀ ω, (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d)) (⋃ i, f i) =
        ∑' i, (unitQuenchedLaw hd hlam (a ω) (ha ω) x : Measure (PathSpace d)) (f i) :=
      fun ω => measure_iUnion hdisj hfm
    simp_rw [this]
    exact Measurable.tsum ih

/-- The annealed law of the unit walk started at the origin. -/
def unitAnnealedLaw (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {lam : ℝ}
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) :
    ProbabilityMeasure (PathSpace d) :=
  haveI := hP.isProbabilityMeasure
  ⟨P.bind fun ω => (unitQuenchedLaw hd hP.lam_mem.1 (a ω) (hP.bounds ω) 0 :
      Measure (PathSpace d)),
    ⟨by
      rw [Measure.bind_apply MeasurableSet.univ (measurable_unitQuenchedLaw hd hP.lam_mem.1 a
        hP.bounds hP.measurable 0).aemeasurable]
      simp only [measure_univ, lintegral_const, one_mul]⟩⟩

theorem unitAnnealedLaw_apply (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {lam : ℝ} (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a)
    {B : Set (PathSpace d)} (hB : MeasurableSet B) :
    (unitAnnealedLaw hd P a hP : Measure (PathSpace d)) B =
      ∫⁻ ω, (unitQuenchedLaw hd hP.lam_mem.1 (a ω) (hP.bounds ω) 0 : Measure (PathSpace d)) B
        ∂P :=
  Measure.bind_apply hB (measurable_unitQuenchedLaw hd hP.lam_mem.1 a hP.bounds hP.measurable
    0).aemeasurable

/-- Ordered position distributions of the rescaled walk agree with those of the unit walk
at the corresponding accelerated times. -/
theorem walk_regularLaw_position_fdd_eq_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (k : ℕ)
    (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (z : Fin (k + 1) → Site d) :
    let c : ℝ≥0 := ⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩
    (LongRange.walkRates hd hε.1 hlam a ha).regularLaw (Measure.dirac x)
        {h | ∀ i : Fin (k + 1), 0 < i → h.position (t i) = z i} =
      (unitRates hd hlam a ha).regularLaw (Measure.dirac x)
        {h | ∀ i : Fin (k + 1), 0 < i → h.position (c * t i) = z i} := by
  dsimp only
  let c : ℝ≥0 := ⟨1 / (LongRange.kappa d ε * ε ^ 2),
    le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩
  have hmono : Monotone (fun i => c * t i) := fun _ _ hij => by
    simpa only [mul_comm] using mul_le_mul_left (ht hij) c
  have hzero : c * t 0 = 0 := by rw [ht0, mul_zero]
  rw [(LongRange.walkRates hd hε.1 hlam a ha).regularLaw_position_fdd
    (Measure.dirac x) k t ht ht0 z,
    (unitRates hd hlam a ha).regularLaw_position_fdd
    (Measure.dirac x) k (fun i => c * t i) hmono hzero z]
  apply tsum_congr
  intro x₀
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [LongRange.walk_transitionKernel_eq_unit hd hε hlam a ha]
  rw [← mul_tsub c (t i.succ) (t i.castSucc)]
  rfl

/-- Ordered observations at nonnegative times have the same joint law after the clock change. -/
theorem walk_regularLaw_observations_eq_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (k : ℕ)
    (t : Fin k → ℝ≥0) (ht : Monotone t) (z : Fin k → Site d) :
    let c : ℝ≥0 := ⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩
    (LongRange.walkRates hd hε.1 hlam a ha).regularLaw (Measure.dirac x)
        {h | ∀ i : Fin k, h.position (t i) = z i} =
      (unitRates hd hlam a ha).regularLaw (Measure.dirac x)
        {h | ∀ i : Fin k, h.position (c * t i) = z i} := by
  have hmono : Monotone (Fin.cons 0 t) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j _
      simp only [Fin.cons_zero]
      exact zero_le
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact (not_le_of_gt i.succ_pos hij).elim
      · intro hij
        simpa only [Fin.cons_succ] using ht (Fin.succ_le_succ_iff.mp hij)
  have h := walk_regularLaw_position_fdd_eq_unit hd hε hlam a ha x k
    (Fin.cons 0 t) hmono rfl (Fin.cons x z)
  simpa only [Fin.forall_fin_succ, lt_self_iff_false, false_implies, Fin.succ_pos,
    Fin.cons_succ, forall_const, true_and] using h

/-- Ordered cylinder events are preserved by the deterministic clock change. -/
theorem walk_regularLaw_cylinder_eq_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (k : ℕ)
    (t : Fin k → ℝ≥0) (ht : Monotone t) (B : Fin k → Set (Site d)) :
    let c : ℝ≥0 := ⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩
    (LongRange.walkRates hd hε.1 hlam a ha).regularLaw (Measure.dirac x)
        {h | ∀ i : Fin k, h.position (t i) ∈ B i} =
      (unitRates hd hlam a ha).regularLaw (Measure.dirac x)
        {h | ∀ i : Fin k, h.position (c * t i) ∈ B i} := by
  dsimp only
  let c : ℝ≥0 := ⟨1 / (LongRange.kappa d ε * ε ^ 2),
    le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩
  let Y : Set (Fin k → Site d) := {z | ∀ i, z i ∈ B i}
  have hevent (u : Fin k → ℝ≥0) :
      {h : RegularHistory (Site d) | ∀ i, h.position (u i) ∈ B i} =
        ⋃ z ∈ Y, {h : RegularHistory (Site d) | ∀ i, h.position (u i) = z i} := by
    ext h
    simp only [Y, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hh
      exact ⟨fun i => h.position (u i), hh, fun _ => rfl⟩
    · rintro ⟨z, hz, heq⟩ i
      rw [heq i]
      exact hz i
  have hmeas (u : Fin k → ℝ≥0) (z : Fin k → Site d) :
      MeasurableSet {h : RegularHistory (Site d) | ∀ i, h.position (u i) = z i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (RegularHistory.measurable_position _) (measurableSet_singleton _)
  have hdisj (u : Fin k → ℝ≥0) : Y.PairwiseDisjoint
      (fun z : Fin k → Site d => {h : RegularHistory (Site d) |
        ∀ i, h.position (u i) = z i}) := by
    intro z _ z' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro h hh hh'
    apply hne
    funext i
    rw [← hh i, ← hh' i]
  rw [hevent t, hevent (fun i => c * t i),
    measure_biUnion (Set.to_countable Y) (hdisj t) (fun z _ => hmeas t z),
    measure_biUnion (Set.to_countable Y) (hdisj _) (fun z _ => hmeas _ z)]
  apply tsum_congr
  intro z
  exact walk_regularLaw_observations_eq_unit hd hε hlam a ha x k t ht z

/-- The physical lattice embedding is the unit embedding multiplied by the spacing. -/
theorem walkEmbed_eq_smul (ε : ℝ) (x : Site d) :
    walkEmbed ε x = ε • walkEmbed 1 x := by
  ext i
  change ε * (x i : ℝ) = ε * (1 * (x i : ℝ))
  ring

/-- The rescaled quenched walk is the deterministic space-time transform of the unit walk. -/
theorem quenchedLaw_eq_scaled_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) :
    let c : {c : ℝ≥0 // 0 < c} := ⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
      one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩
    (quenchedLaw hd hε.1 hlam a ha x : Measure (PathSpace d)) =
      Measure.map (scaledPath ε c) (unitQuenchedLaw hd hlam a ha x : Measure (PathSpace d)) := by
  dsimp only
  let c : {c : ℝ≥0 // 0 < c} := ⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
    le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
    one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩
  have hscale : Measurable (scaledPath (d := d) ε c) :=
    measurable_transformPath (fun y : EuclideanSpace ℝ (Fin d) => ε • y)
      (continuous_const_smul ε) (dilation c.1 c.2)
  let m : Time → MeasurableSpace (PathSpace d) := fun t =>
    MeasurableSpace.comap (fun x : PathSpace d => x.1 t) inferInstance
  have hgen : (inferInstance : MeasurableSpace (PathSpace d)) = MeasurableSpace.generateFrom
      (piiUnionInter (fun t => {s | MeasurableSet[m t] s}) Set.univ) := by
    rw [generateFrom_piiUnionInter_measurableSet m Set.univ, iSup_univ]
    exact borel_eq_iSup_comap_eval
  have hpi : IsPiSystem (piiUnionInter (fun t => {s | MeasurableSet[m t] s}) Set.univ) :=
    isPiSystem_piiUnionInter _ (fun t => @MeasurableSpace.isPiSystem_measurableSet _ (m t)) _
  apply ext_of_generate_finite _ hgen hpi
  · intro s hs
    obtain ⟨F, -, f, hf, rfl⟩ := hs
    have hfA : ∀ u ∈ F, ∃ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A ∧
        (fun y : PathSpace d => y.1 u) ⁻¹' A = f u := fun u hu =>
      MeasurableSpace.measurableSet_comap.mp (hf u hu)
    choose! A hA hAf using hfA
    have hmf : MeasurableSet (⋂ u ∈ F, f u) := MeasurableSet.biInter F.countable_toSet
      fun u hu => by
        rw [← hAf u hu]
        exact measurable_eval u (hA u hu)
    rw [Measure.map_apply hscale hmf, quenchedLaw_apply hd hε.1 hlam a ha x hmf,
      unitQuenchedLaw_apply hd hlam a ha x (hscale hmf)]
    let t : Fin F.card ↪o Time := F.orderEmbOfFin rfl
    have hmem : ∀ i, t i ∈ F := fun i => F.orderEmbOfFin_mem rfl i
    have hex : ∀ u ∈ F, ∃ i, t i = u := by
      intro u hu
      have : u ∈ Set.range t := by
        rw [show Set.range t = ↑F from Finset.range_orderEmbOfFin F rfl]
        exact hu
      exact this
    have hleft : (RegularHistory.halfLinePath (walkEmbed ε)) ⁻¹' (⋂ u ∈ F, f u) =
        {h | ∀ i, h.position (t i) ∈ walkEmbed ε ⁻¹' A (t i)} := by
      ext h
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hh i
        have h' := hh (t i) (hmem i)
        rw [← hAf (t i) (hmem i)] at h'
        exact h'
      · intro hh u hu
        obtain ⟨i, rfl⟩ := hex u hu
        rw [← hAf (t i) (hmem i)]
        exact hh i
    have hright : (RegularHistory.halfLinePath (walkEmbed 1)) ⁻¹'
        (scaledPath ε c ⁻¹' (⋂ u ∈ F, f u)) =
        {h | ∀ i, h.position (c.1 * t i) ∈ walkEmbed ε ⁻¹' A (t i)} := by
      ext h
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hh i
        have h' := hh (t i) (hmem i)
        rw [← hAf (t i) (hmem i)] at h'
        change ε • walkEmbed 1 (h.position (c.1 * t i)) ∈ A (t i) at h'
        rw [← walkEmbed_eq_smul] at h'
        exact h'
      · intro hh u hu
        obtain ⟨i, rfl⟩ := hex u hu
        rw [← hAf (t i) (hmem i)]
        change ε • walkEmbed 1 (h.position (c.1 * t i)) ∈ A (t i)
        rw [← walkEmbed_eq_smul]
        exact hh i
    rw [hleft, hright]
    exact walk_regularLaw_cylinder_eq_unit hd hε hlam a ha x F.card t t.monotone
      (fun i => walkEmbed ε ⁻¹' A (t i))
  · rw [Measure.map_apply hscale MeasurableSet.univ]
    simp only [Set.preimage_univ, measure_univ]

/-- Averaging the quenched identity gives the annealed space-time scaling identity. -/
theorem annealedLaw_eq_scaled_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) :
    let c : {c : ℝ≥0 // 0 < c} := ⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
      one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩
    (annealedLaw hd P a hP hε.1 : Measure (PathSpace d)) =
      Measure.map (scaledPath ε c) (unitAnnealedLaw hd P a hP : Measure (PathSpace d)) := by
  dsimp only
  let c : {c : ℝ≥0 // 0 < c} := ⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
    le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
    one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩
  have hscale : Measurable (scaledPath (d := d) ε c) :=
    measurable_transformPath (fun y : EuclideanSpace ℝ (Fin d) => ε • y)
      (continuous_const_smul ε) (dilation c.1 c.2)
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hscale hB, annealedLaw_apply hd P a hP hε.1 hB,
    unitAnnealedLaw_apply hd P a hP (hscale hB)]
  apply lintegral_congr
  intro ω
  rw [quenchedLaw_eq_scaled_unit hd hε hP.lam_mem.1 (a ω) (hP.bounds ω) 0,
    Measure.map_apply hscale hB]

end

end LongRangeHeat
