import LongRange.Support.Prob.Cadlag.HalfLine.RestrictionTight
import LongRange.Support.Prob.Cadlag.HalfLine.Laws

/-!
# Continuity of path evaluations

Evaluation on the Skorokhod half-line path space is continuous at paths which are
continuous at the evaluation time.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory
open scoped Topology

variable {E : Type*} [MetricSpace E]

/-- Evaluation is continuous at every path continuous at the evaluation time;
this is the mapping step in Kallenberg (2002), Theorem 16.10. -/
theorem continuousAt_eval_of_continuousAt_path {x : D E} {t : Time}
    (ht : ContinuousAt x.1 t) : ContinuousAt (fun y : D E => y.1 t) x := by
  change Tendsto (fun y : D E => y.1 t) (𝓝 x) (𝓝 (x.1 t))
  rw [Filter.tendsto_iff_seq_tendsto]
  intro y hy
  exact tendsto_eval_of_tendsto_skorohodDistance (tendsto_iff_dist_tendsto_zero.mp hy) ht

/-- Weak convergence of path laws implies convergence of their joint evaluations at
almost surely continuous times. -/
theorem tendsto_jointLaw_of_tendsto_of_ae_continuous
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : ℕ → ProbabilityMeasure (D E)} {ν : ProbabilityMeasure (D E)}
    (hμ : Tendsto μ atTop (𝓝 ν)) {k : ℕ} (ts : Fin k → Time)
    (hc : ∀ i, ∀ᵐ x ∂(ν : Measure (D E)), ContinuousAt x.1 (ts i)) :
    Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)) := by
  apply ProbabilityMeasure.tendsto_map_of_ae_continuousAt hμ (measurable_eval_family ts)
  filter_upwards [ae_all_iff.mpr hc] with x hx
  exact continuousAt_pi.mpr fun i => continuousAt_eval_of_continuousAt_path (hx i)

end LatticeProb.Cadlag.HalfLine
