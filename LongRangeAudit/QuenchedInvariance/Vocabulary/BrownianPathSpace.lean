import LongRangeAudit.QuenchedInvariance.Vocabulary.ContinuousMapMeasurable

/-! # Independent BrownianPathSpace vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LatticeProb
open MeasureTheory ProbabilityTheory
variable {d : ℕ}

/-- The Euclidean space of dimension `d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A continuous Euclidean path on all nonnegative times. Its measurable structure is the Borel
σ-algebra of the compact-open topology, found from `LatticeProb.continuousMapMeasurableSpace`. -/
abbrev BrownianPath (d : ℕ) := C(ℝ≥0, Euc d)

example (d : ℕ) : MeasurableSpace (BrownianPath d) := inferInstance
example (d : ℕ) : BorelSpace (BrownianPath d) := inferInstance

/-- Standard zero-start Brownian law: a probability measure on Brownian paths under which the
coordinate processes are independent and each is a real Brownian motion. -/
def IsStandardBrownianLaw {d : ℕ} (μ : Measure (BrownianPath d)) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ i : Fin d, IsBrownianReal (fun t ω => ω t i) μ) ∧
  iIndepFun (fun (i : Fin d) (ω : BrownianPath d) => fun t : ℝ≥0 => ω t i) μ

end LatticeProb
end

end LongRangeAudit.QuenchedInvariance
