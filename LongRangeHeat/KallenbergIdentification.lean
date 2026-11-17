import LongRange.Support.Prob.Cadlag.HalfLine.Separable
import LongRange.Support.Prob.Cadlag.HalfLine.Laws
import LongRangeHeat.KallenbergEvaluation
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Identification of càdlàg path laws

Finite-dimensional laws determine a law on half-line Skorokhod path space.
-/

namespace LatticeProb.Cadlag.HalfLine

open MeasureTheory TopologicalSpace Filter
open scoped Topology

variable {E : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]

/-- A path law is determined by all its finite-dimensional distributions. -/
theorem eq_of_jointLaw_eq {μ ν : ProbabilityMeasure (D E)}
    (h : ∀ (k : ℕ) (ts : Fin k → Time), jointLaw μ ts = jointLaw ν ts) : μ = ν := by
  classical
  let coord : D E → Time → E := fun x t => x.1 t
  have hcoord : Measurable coord := measurable_pi_iff.mpr fun t => measurable_eval t
  have heval : borel (D E) ≤ MeasurableSpace.comap coord (inferInstance : MeasurableSpace (Time → E)) := by
    apply borel_le_iSup_comap_eval.trans
    refine iSup_le fun t => ?_
    have ht : Measurable (fun f : Time → E => f t) := measurable_pi_apply t
    simpa only [MeasurableSpace.comap_comp, BorelSpace.measurable_eq, Function.comp_def, coord]
      using MeasurableSpace.comap_mono (g := coord) ht.comap_le
  have hproject (I : Finset Time) :
      Measure.map I.restrict (Measure.map coord (μ : Measure (D E))) =
        Measure.map I.restrict (Measure.map coord (ν : Measure (D E))) := by
    let e := Fintype.equivFin I
    let ts : Fin (Fintype.card I) → Time := fun i => (e.symm i).1
    have hj := congrArg (fun ρ : ProbabilityMeasure (Fin (Fintype.card I) → E) =>
      (ρ : Measure (Fin (Fintype.card I) → E))) (h _ ts)
    have hm : Measurable (fun y : Fin (Fintype.card I) → E => fun i : I => y (e i)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
    have hmapped := congrArg (Measure.map (fun y : Fin (Fintype.card I) → E =>
      fun i : I => y (e i))) hj
    simp only [jointLaw, ProbabilityMeasure.toMeasure_map] at hmapped
    rw [Measure.map_map hm (measurable_eval_family ts),
      Measure.map_map hm (measurable_eval_family ts)] at hmapped
    rw [Measure.map_map (Finset.measurable_restrict I) hcoord,
      Measure.map_map (Finset.measurable_restrict I) hcoord]
    convert hmapped using 1 <;> congr 1 <;> funext x i <;>
      simp only [Function.comp_apply, Finset.restrict_def, ts, coord, Equiv.symm_apply_apply]
  have hmap : Measure.map coord (μ : Measure (D E)) =
      Measure.map coord (ν : Measure (D E)) := by
    let Q : ∀ I : Finset Time, Measure (I → E) := fun I =>
      Measure.map I.restrict (Measure.map coord (μ : Measure (D E)))
    have hfinite (I : Finset Time) : IsFiniteMeasure (Q I) := by
      dsimp [Q]
      infer_instance
    exact IsProjectiveLimit.unique (P := Q) (fun _ => rfl) (fun I => (hproject I).symm)
  apply Subtype.ext
  apply Measure.ext
  intro A hA
  have hA' : @MeasurableSet (D E) (MeasurableSpace.comap coord _) A := heval A hA
  obtain ⟨B, hB, hBpre⟩ := MeasurableSpace.measurableSet_comap.mp hA'
  rw [← hBpre]
  calc
    (μ : Measure (D E)) (coord ⁻¹' B) = (Measure.map coord (μ : Measure (D E))) B :=
      (Measure.map_apply hcoord hB).symm
    _ = (Measure.map coord (ν : Measure (D E))) B := congrArg (fun m => m B) hmap
    _ = (ν : Measure (D E)) (coord ⁻¹' B) := Measure.map_apply hcoord hB


/-- Joint laws converge when each evaluation time approaches from the right. -/
theorem tendsto_jointLaw_of_tendsto_right (μ : ProbabilityMeasure (D E))
    {k : ℕ} (ts : ℕ → Fin k → Time) (t : Fin k → Time)
    (ht : ∀ i, Tendsto (fun n => ts n i) atTop (𝓝[Set.Ici (t i)] (t i))) :
    Tendsto (fun n => jointLaw μ (ts n)) atTop (𝓝 (jointLaw μ t)) := by
  have hlim := tendstoInDistribution_of_ae_tendsto
    (μ' := (μ : Measure (D E)))
    (X := fun n (x : D E) i => x.1 (ts n i))
    (Z := fun (x : D E) i => x.1 (t i))
    (fun n => (measurable_eval_family (ts n)).aemeasurable)
    (measurable_eval_family t).aemeasurable
    (Filter.Eventually.of_forall fun x => tendsto_pi_nhds.mpr fun i =>
      (x.2.1 (t i)).tendsto.comp (ht i))
  simpa only [jointLaw, ProbabilityMeasure.map] using hlim.tendsto

/-- Joint laws at a dense set of times determine the law of a càdlàg path. -/
theorem eq_of_jointLaw_eq_on_dense {μ ν : ProbabilityMeasure (D E)}
    {S : Set Time} (hS : Dense S)
    (h : ∀ (k : ℕ) (ts : Fin k → Time), (∀ i, ts i ∈ S) →
      jointLaw μ ts = jointLaw ν ts) : μ = ν := by
  classical
  apply eq_of_jointLaw_eq
  intro k t
  have hex (i : Fin k) := hS.exists_seq_strictAnti_tendsto (t i)
  choose u huanti huS hulim using hex
  have hwithin (i : Fin k) :
      Tendsto (fun n => u i n) atTop (𝓝[Set.Ici (t i)] (t i)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hulim i, Eventually.of_forall fun n => ?_⟩
    change t i ≤ u i n
    exact le_of_lt ((huS i n).1)
  have hμ := tendsto_jointLaw_of_tendsto_right μ (fun n i => u i n) t hwithin
  have hν := tendsto_jointLaw_of_tendsto_right ν (fun n i => u i n) t hwithin
  have heq : (fun n => jointLaw μ (fun i => u i n)) =
      (fun n => jointLaw ν (fun i => u i n)) := by
    funext n
    exact h k _ (fun i => (huS i n).2)
  rw [heq] at hμ
  exact tendsto_nhds_unique hμ hν


/-- Compactness and finite-dimensional convergence identify the path-law limit when
each law in the closure has a dense set of almost surely continuous times. -/
theorem tendsto_of_compact_of_jointLaw_tendsto
    {μ : ℕ → ProbabilityMeasure (D E)} {ν : ProbabilityMeasure (D E)}
    (hcompact : IsCompact (closure (Set.range μ))) {S : Set Time}
    (hc : ∀ ρ ∈ closure (Set.range μ), ∃ T : Set Time, Dense T ∧ T ⊆ S ∧
      ∀ t ∈ T, ∀ᵐ x ∂(ρ : Measure (D E)), ContinuousAt x.1 t)
    (h : ∀ (k : ℕ) (ts : Fin k → Time), (∀ i, ts i ∈ S) →
      Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ρ, hρ, ms, hms, hlim⟩ := hcompact.tendsto_subseq
    (x := μ ∘ ns) (fun n => subset_closure ⟨ns n, rfl⟩)
  have heq : ρ = ν := by
    obtain ⟨T, hT, hTS, hcρ⟩ := hc ρ hρ
    apply eq_of_jointLaw_eq_on_dense hT
    intro k ts hts
    have hρlaw := tendsto_jointLaw_of_tendsto_of_ae_continuous hlim ts
      (fun i => hcρ (ts i) (hts i))
    have hνlaw := (h k ts (fun i => hTS (hts i))).comp (hns.comp hms.tendsto_atTop)
    exact tendsto_nhds_unique hρlaw hνlaw
  subst ρ
  exact ⟨ms, hlim⟩

end LatticeProb.Cadlag.HalfLine
