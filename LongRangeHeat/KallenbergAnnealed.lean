import LongRangeHeat.KallenbergContinuity
import LongRangeHeat.InvariancePrinciple
import LongRangeHeat.Statements.Fdd

/-!
# Identification of annealed limits

Relative compactness and convergence of the finite-dimensional distributions
identify the annealed path-law limit.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped Topology NNReal
open LongRange (Edge)

/-- The annealed laws converge if they are relatively compact and their ordered
positive-time joint laws converge. -/
theorem annealed_tendsto_of_compact_of_fdd
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (ν : ProbabilityMeasure (PathSpace d))
    (hcompact : IsCompact (closure (Set.range (fun n => annealedLaw hd P a hP (hε n).1))))
    (hmarg : ∀ t : Time,
      IsTightMeasureSet {Measure.map (fun w : PathSpace d => w.1 t)
        (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)) | n})
    (hfdd : ∀ {k : ℕ} (ts : Fin k → Time), StrictMono ts → (∀ i, 0 < ts i) →
      Tendsto (fun n => jointLaw (annealedLaw hd P a hP (hε n).1) ts) atTop
        (𝓝 (jointLaw ν ts))) :
    Tendsto (fun n => annealedLaw hd P a hP (hε n).1) atTop (𝓝 ν) := by
  apply tendsto_of_compact_of_jointLaw_tendsto_positive hcompact
  intro k ts hts
  apply tendsto_jointLaw_of_productTests
    (jointLaw_tight_of_relativelyCompact _ hcompact hmarg) ?_ ts hts
  intro m ss hmono hpos φ
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hfdd ss hmono hpos))
    (LatticeProb.productTest φ)
  simpa only [LatticeProb.productTest_apply] using h


/-- Proposition 4.3 identifies the annealed limit once the stopping-time
compactness criterion is available. -/
theorem annealed_invariance_of_stopping_compactness
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    (hEK : EthierKurtzRelativeCompactnessStopping)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
    let s : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2)
    Tendsto (fun ε : Set.Ioo (0 : ℝ) (1 / 2) => annealedLaw hd P a hP ε.2.1)
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 (B.map (scaledBrownianPath s))) := by
  dsimp only
  rw [Filter.tendsto_iff_seq_tendsto]
  intro ε hε0
  have hε0' : Tendsto (fun n => ((ε n : Set.Ioo (0 : ℝ) (1 / 2)) : ℝ)) atTop (𝓝 0) :=
    Filter.tendsto_comap_iff.1 hε0
  have hε : ∀ n, ((ε n : Set.Ioo (0 : ℝ) (1 / 2)) : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    fun n => (ε n).2
  apply annealed_tendsto_of_compact_of_fdd hd P a hP hε _
    (annealedLaw_isCompact_closure_range hMSC hNash hDavies hEK hε hε0')
    (fun t => annealedLaw_marginals_isTight hMSC hNash hDavies hε t)
  intro k ts hmono hpos
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Subsingleton (ProbabilityMeasure (Fin 0 → EuclideanSpace ℝ (Fin d))) :=
      subsingleton_probabilityMeasure
    exact tendsto_const_nhds.congr fun _ => Subsingleton.elim _ _
  · rw [jointLaw_map_scaledBrownianPath]
    exact Statements.fdd_convergence hMSC hNash hDavies hd P a hP B hB hk ts hmono
      (fun n => (ε n : ℝ)) hε hε0'

end LongRangeHeat
