import LongRangeAudit.QuenchedInvariance.Vocabulary
import LongRangeHeat.QuenchedMeasurable

/-! # Vocabulary for the annealed invariance principle -/

namespace LongRangeAudit.QuenchedInvariance

open Filter MeasureTheory ProbabilityTheory TopologicalSpace
open _root_.LongRangeAudit.QuenchedInvariance.LatticeProb
  _root_.LongRangeAudit.QuenchedInvariance.LatticeProb.Cadlag.HalfLine
  _root_.LongRangeAudit.QuenchedInvariance.LatticeProb.JumpChain
  _root_.LongRangeAudit.QuenchedInvariance.LatticeProb.Euclidean.Lattice
open scoped ENNReal NNReal Topology
open _root_.LongRangeAudit.QuenchedInvariance.LongRange (Edge walkRates walkRate walkEmbed)

noncomputable section
namespace LatticeProb.External
open _root_.LongRangeAudit.QuenchedInvariance.LatticeProb.Graph.LongRangeKernel

/-- The uniform Murugan–Saloff-Coste heat-kernel estimate. -/
def MuruganSaloffCosteUniform : Prop :=
  ∀ (X : Type) (G : WeightedGraph X), Infinite X → G.graph.Connected →
    ∀ (V φ : ℝ → ℝ) (γ : ℝ),
    (∃ C_μ : ℝ, 1 ≤ C_μ ∧ ∀ x,
      C_μ⁻¹ ≤ (G.mass x : ℝ) ∧ (G.mass x : ℝ) ≤ C_μ) →
    IsVolumeProfile V →
    (∃ C_h : ℝ, 1 < C_h ∧ ∀ x r, 0 < r →
      ENNReal.ofReal (C_h⁻¹ * V r) ≤ G.volume x r ∧
      G.volume x r ≤ ENNReal.ofReal (C_h * V r)) →
    (∃ p₀ : ℝ, 0 < p₀ ∧ ∀ x y, G.graph.Adj x y →
      p₀ ≤ (G.weight x y : ℝ) / (G.mass x : ℝ)) →
    1 < γ →
    (∃ C : ℝ, 0 < C ∧ ∀ x y (n : ℕ), 1 ≤ n →
      G.heat n x y ≤ ENNReal.ofReal
        (C / V ((n : ℝ) ^ (1 / γ)) *
          Real.exp (-(((G.graph.dist x y : ℝ) ^ γ / (C * n)) ^ (1 / (γ - 1)))))) →
    (∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n → G.graph.dist x y ≤ n →
      ENNReal.ofReal (c / V ((n : ℝ) ^ (1 / γ)) *
        Real.exp (-(((G.graph.dist x y : ℝ) ^ γ / (c * n)) ^ (1 / (γ - 1))))) ≤
          G.heat n x y + G.heat (n + 1) x y) →
    IsJumpScale φ →
    ∀ ζ : ℝ → ℝ, IsInverseScale γ φ ζ →
    ∀ C_φ : ℝ, 0 < C_φ →
    ∃ C : ℝ, 0 < C ∧ ∀ k : X → X → ℝ≥0∞, IsMarkovDensity G.mass k →
      (∀ x y, k x y = k y x) →
      (∀ x y,
        ENNReal.ofReal (C_φ⁻¹ / (V (G.graph.dist x y) * φ (G.graph.dist x y))) ≤ k x y ∧
        k x y ≤ ENNReal.ofReal (C_φ / (V (G.graph.dist x y) * φ (G.graph.dist x y)))) →
      ∀ n : ℕ,
        ENNReal.ofReal (C⁻¹ / V (ζ n)) ≤ evenKernelSup G.mass k n ∧
        evenKernelSup G.mass k n ≤ ENNReal.ofReal (C / V (ζ n))


/-- Discrete stopping times for the natural filtration on a bounded horizon. -/
def discreteNaturalStopping {E Ω : Type*} [MetricSpace E] [MeasurableSpace E]
    (Y : Ω → D E) (T : ℝ) (tau : Ω → Time) : Prop :=
  (Set.range tau).Countable ∧ (∀ w, (tau w : ℝ) ≤ T) ∧
    ∀ t : Time, @MeasurableSet Ω (naturalSigma Y t) {w | tau w ≤ t}

/-- The stopped increment quantity in the compactness criterion. -/
def stoppingOscillation {E Ω : Type*} [MetricSpace E] [MeasurableSpace E]
    [m : MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (Y : Ω → D E)
    (beta T delta : ℝ) : ℝ≥0∞ :=
  ⨆ tau : Ω → Time, ⨆ (_ : discreteNaturalStopping Y T tau),
    ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ delta),
      ∫⁻ w, ⨆ v : Time, ⨆ (_ : (v : ℝ) ≤ min delta (tau w)),
        incrementPower Y beta (tau w + u) (tau w) w *
          incrementPower Y beta (tau w) (tau w - v) w ∂P

/-- The implication (c) implies (a) with a specified outer aggregation of process indices.
Only `iSup` and sequential `limsup` are used in the cited proposition below. -/
def stoppingCompactnessImplication (A : Type)
    (aggregate : (A → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ (E : Type) [MetricSpace E] [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E]
    [BorelSpace E] (Ω : A → Type) (m : ∀ a, MeasurableSpace (Ω a))
    (P : ∀ a, @ProbabilityMeasure (Ω a) (m a)) (Y : ∀ a, Ω a → D E),
    (∀ a, @Measurable (Ω a) (D E) (m a) inferInstance (Y a)) →
    (∀ a t, @Measurable (Ω a) E (m a) inferInstance (fun w => (Y a w).1 t)) →
    (∀ eta : ℝ, 0 < eta → ∀ t : ℚ, 0 ≤ t → ∃ K : Set E, IsCompact K ∧
      ∀ a, ENNReal.ofReal (1 - eta) ≤
        (P a : @Measure (Ω a) (m a)) {w | (Y a w).1 (t : ℝ).toNNReal ∈ K}) →
    (∀ T : ℝ, 0 < T → ∃ beta : ℝ, 0 < beta ∧
      Tendsto (fun delta : ℝ => aggregate (fun a =>
        @stoppingOscillation E (Ω a) _ _ (m a) (P a) (Y a) beta T delta))
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun delta : ℝ => aggregate (fun a =>
        ∫⁻ w, incrementPower (Y a) beta delta.toNNReal 0 w
          ∂(P a : @Measure (Ω a) (m a)))) (𝓝[>] 0) (𝓝 0)) →
    IsCompact (closure (Set.range (fun a =>
      @ProbabilityMeasure.map (Ω a) (D E) (m a) inferInstance (P a) (Y a))))

/-- Ethier–Kurtz, Chapter 3, Theorem 8.6(c) implies (a), together with Remark 8.7(b).
The first conjunct is the family statement; the second replaces both outer suprema
by sequential limsups. Rational-time marginal compactness is retained in both. -/
def EthierKurtzRelativeCompactnessStopping : Prop :=
  (∀ A : Type, stoppingCompactnessImplication A (fun f => ⨆ a, f a)) ∧
    stoppingCompactnessImplication ℕ (fun f => Filter.limsup f atTop)

end LatticeProb.External

variable {d : ℕ}

/-- Independent uniformly elliptic conductances with mean one. -/
structure ConductanceLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ)
    (a : Ω → Edge d → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  lam_mem : lam ∈ Set.Ioc (0 : ℝ) 1
  measurable : ∀ e, Measurable fun ω => a ω e
  indep : iIndepFun (fun e ω => a ω e) P
  bounds : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹
  mean_one : ∀ e, ∫ ω, a ω e ∂P = 1


/-- Transport the measurable-cylinder result to the equivalent jump-rate vocabulary. -/
theorem measurable_regularLaw_cylinder {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    {r : Ω → LatticeProb.JumpChain.BoundedRates S} {R : ℝ}
    (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (x : S) (F : Finset ℝ≥0) (B : ℝ≥0 → Set S) :
    Measurable fun ω => (r ω).regularLaw (Measure.dirac x)
      {h | ∀ s ∈ F, h.position s ∈ B s} := by
  let r' : Ω → _root_.LatticeProb.JumpChain.BoundedRates S := fun ω =>
    ⟨(r ω).q, (r ω).q_nonneg, (r ω).q_self, (r ω).summable,
      (r ω).R, (r ω).R_pos, (r ω).total_le⟩
  exact _root_.LongRangeHeat.measurable_regularLaw_cylinder (r := r') hq hR x F B

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


end
end LongRangeAudit.QuenchedInvariance
