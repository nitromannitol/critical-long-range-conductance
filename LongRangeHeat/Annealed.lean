import LongRangeHeat.QuenchedMeasurable
import LongRangeHeat.Defs
import LongRange.Walk.Increments

/-!
# The quenched and annealed laws of the rescaled walk

The quenched law `P^a_x` of the walk `X^ε` started at `x` is the law of its embedded jump-chain
path on the half-line Skorokhod space `D([0, ∞), ℝ^d)`. For a random environment the map
`ω ↦ P^{a ω}_x` is measurable, so the annealed law `P^ann_x = E[P^a_x]` is a probability measure
on path space. The time marginals of the quenched law are the transition kernels.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.JumpChain LatticeProb.Euclidean.Lattice
open scoped ENNReal NNReal
open LongRange (Edge walkRates walkRate walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The half-line Skorokhod space of paths in `ℝ^d`. -/
abbrev PathSpace (d : ℕ) : Type := D (EuclideanSpace ℝ (Fin d))

/-- The quenched law `P^a_x` of the walk `X^ε` started at `x`, on `D([0, ∞), ℝ^d)`. -/
def quenchedLaw (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) : ProbabilityMeasure (PathSpace d) :=
  pathLaw (walkRates hd hε hlam a ha) (Measure.dirac x) (walkEmbed ε)

theorem measurable_walkRate {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ) (a : Ω → Edge d → ℝ)
    (hma : ∀ e, Measurable fun ω => a ω e) (x y : Site d) :
    Measurable fun ω => walkRate ε (a ω) x y := by
  unfold walkRate
  by_cases h : y - x = 0
  · simp only [h, dite_true]
    exact measurable_const
  · simp only [h, dite_false]
    exact (measurable_const.mul (hma _)).mul measurable_const

theorem quenchedLaw_apply (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) {B : Set (PathSpace d)}
    (hB : MeasurableSet B) :
    (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d)) B =
      (walkRates hd hε hlam a ha).regularLaw (Measure.dirac x)
        (RegularHistory.halfLinePath (walkEmbed ε) ⁻¹' B) := by
  unfold quenchedLaw pathLaw
  change Measure.map (RegularHistory.halfLinePath (walkEmbed ε))
    ((walkRates hd hε hlam a ha).regularLaw (Measure.dirac x)) B = _
  rw [Measure.map_apply (measurable_halfLinePath _) hB]

/-- The map from the environment to the quenched path law is measurable. -/
theorem measurable_quenchedLaw (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    {Ω : Type*} [MeasurableSpace Ω] (a : Ω → Edge d → ℝ)
    (ha : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹) (hma : ∀ e, Measurable fun ω => a ω e)
    (x : Site d) :
    Measurable fun ω => (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d)) := by
  set r : Ω → BoundedRates (Site d) := fun ω => walkRates hd hε hlam (a ω) (ha ω) with hr
  have hq : ∀ i j, Measurable fun ω => (r ω).q i j := fun i j =>
    measurable_walkRate ε a hma i j
  have hR : ∀ ω, (r ω).R = ε ^ d / LongRange.kappa d ε * lam⁻¹ *
      ∑' w : Site d, LongRange.jumpKernel (physical ε w) + 1 := fun ω => rfl
  refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
  let m : Time → MeasurableSpace (PathSpace d) := fun t =>
    MeasurableSpace.comap (fun x : PathSpace d => x.1 t) inferInstance
  have hgen : (inferInstance : MeasurableSpace (PathSpace d)) = MeasurableSpace.generateFrom
      (piiUnionInter (fun t => {s | MeasurableSet[m t] s}) Set.univ) := by
    rw [generateFrom_piiUnionInter_measurableSet m Set.univ, iSup_univ]
    exact borel_eq_iSup_comap_eval
  refine MeasurableSpace.induction_on_inter
    (C := fun B _ => Measurable fun ω =>
      (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d)) B) hgen
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
    have hmeas : ∀ ω, (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d))
        (⋂ u ∈ F, f u) = (r ω).regularLaw (Measure.dirac x)
          {h | ∀ u ∈ F, h.position u ∈ walkEmbed ε ⁻¹' A u} := by
      intro ω
      have hmf : MeasurableSet (⋂ u ∈ F, f u) := MeasurableSet.biInter F.countable_toSet
        fun u hu => by
          rw [← hAf u hu]
          exact measurable_eval u (hA u hu)
      rw [quenchedLaw_apply hd hε hlam (a ω) (ha ω) x hmf]
      congr 1
      ext h
      simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
      refine forall₂_congr fun u hu => ?_
      rw [← hAf u hu]
      rfl
    simp_rw [hmeas]
    exact measurable_regularLaw_cylinder hq hR x F _
  · intro s hs ih
    have : ∀ ω, (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d)) sᶜ =
        1 - (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d)) s := fun ω =>
      prob_compl_eq_one_sub hs
    simp_rw [this]
    exact measurable_const.sub ih
  · intro f hdisj hfm ih
    have : ∀ ω, (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d)) (⋃ i, f i) =
        ∑' i, (quenchedLaw hd hε hlam (a ω) (ha ω) x : Measure (PathSpace d)) (f i) :=
      fun ω => measure_iUnion hdisj hfm
    simp_rw [this]
    exact Measurable.tsum ih

/-- The annealed law `P^ann_0 = E[P^a_0]` of the walk `X^ε` started at the origin: the mixture of
the quenched laws over the environment. -/
def annealedLaw (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {lam : ℝ}
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε) :
    ProbabilityMeasure (PathSpace d) :=
  haveI := hP.isProbabilityMeasure
  ⟨P.bind fun ω => (quenchedLaw hd hε hP.lam_mem.1 (a ω) (hP.bounds ω) 0 :
      Measure (PathSpace d)),
    ⟨by
      rw [Measure.bind_apply MeasurableSet.univ (measurable_quenchedLaw hd hε hP.lam_mem.1 a
        hP.bounds hP.measurable 0).aemeasurable]
      simp only [measure_univ, lintegral_const, one_mul]⟩⟩

theorem annealedLaw_apply (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {lam : ℝ} (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε)
    {B : Set (PathSpace d)} (hB : MeasurableSet B) :
    (annealedLaw hd P a hP hε : Measure (PathSpace d)) B =
      ∫⁻ ω, (quenchedLaw hd hε hP.lam_mem.1 (a ω) (hP.bounds ω) 0 : Measure (PathSpace d)) B
        ∂P :=
  Measure.bind_apply hB (measurable_quenchedLaw hd hε hP.lam_mem.1 a hP.bounds hP.measurable
    0).aemeasurable

/-- The time marginal of the quenched law is the transition kernel at that time, transported by
the embedding of the lattice into `ℝ^d`. -/
theorem quenchedLaw_map_eval (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (t : ℝ≥0) :
    (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d)).map (fun X => X.1 t) =
      (((walkRates hd hε hlam a ha).transitionKernel t x : Measure (Site d))).map
        (walkEmbed ε) := by
  have hpos : ((walkRates hd hε hlam a ha).regularLaw (Measure.dirac x)).map
      (fun h => h.position t) = (walkRates hd hε hlam a ha).transitionKernel t x := by
    apply Measure.ext_of_singleton
    intro j
    rw [Measure.map_apply (RegularHistory.measurable_position t) (measurableSet_singleton j)]
    exact (walkRates hd hε hlam a ha).regularLaw_dirac_position t x j
  have hmap : (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d)) =
      Measure.map (RegularHistory.halfLinePath (walkEmbed ε))
        ((walkRates hd hε hlam a ha).regularLaw (Measure.dirac x)) := rfl
  rw [hmap, Measure.map_map (measurable_eval t) (measurable_halfLinePath _), ← hpos,
    Measure.map_map (measurable_of_countable _) (RegularHistory.measurable_position t)]
  rfl

theorem quenchedLaw_eval_apply (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (t : ℝ≥0)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    (quenchedLaw hd hε hlam a ha x : Measure (PathSpace d)) ((fun X => X.1 t) ⁻¹' B) =
      (walkRates hd hε hlam a ha).transitionKernel t x (walkEmbed ε ⁻¹' B) := by
  rw [← Measure.map_apply (measurable_eval t) hB, quenchedLaw_map_eval,
    Measure.map_apply (measurable_of_countable _) hB]

/-- The time marginal of the annealed law is the environment average of the transition kernels. -/
theorem annealedLaw_eval_apply (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {lam : ℝ} (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ≥0) {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    (annealedLaw hd P a hP hε : Measure (PathSpace d)) ((fun X => X.1 t) ⁻¹' B) =
      ∫⁻ ω, (walkRates hd hε hP.lam_mem.1 (a ω) (hP.bounds ω)).transitionKernel t 0
        (walkEmbed ε ⁻¹' B) ∂P := by
  rw [annealedLaw_apply hd P a hP hε (measurable_eval t hB)]
  exact lintegral_congr fun ω => quenchedLaw_eval_apply hd hε hP.lam_mem.1 (a ω) (hP.bounds ω)
    0 t hB

end

end LongRangeHeat
