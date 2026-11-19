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

end LongRangeHeat
