import LongRangeAudit.QuenchedInvariance.Vocabulary.CadlagLaws

/-! # Independent CadlagChainPathLaw vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# Half-line path laws of jump chains

Regular jump histories define measurable half-line càdlàg paths. Their pushforward laws
have the expected finite-dimensional marginals, and injective state embeddings preserve
raw natural information at each time.
-/

namespace LatticeProb.Cadlag.HalfLine

open MeasureTheory Set TopologicalSpace

noncomputable section

variable {S E : Type*} [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] [MetricSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- A countable-state jump history gives a measurable half-line path. -/
theorem measurable_halfLinePath (ι : S → E) :
    Measurable (fun h : JumpChain.RegularHistory S => h.halfLinePath ι) := by
  apply measurable_iff_measurable_eval.mpr
  exact JumpChain.RegularHistory.measurable_halfLinePath_eval ι (measurable_of_countable ι)

/-- The probability law of the embedded jump-chain path on the half-line. -/
def pathLaw (rates : JumpChain.BoundedRates S) (μ : Measure S)
    [IsProbabilityMeasure μ] (ι : S → E) : ProbabilityMeasure (D E) :=
  ProbabilityMeasure.map
    (⟨rates.regularLaw μ, inferInstance⟩ : ProbabilityMeasure (JumpChain.RegularHistory S))
    (measurable_halfLinePath ι).aemeasurable

end
end LatticeProb.Cadlag.HalfLine

end LongRangeAudit.QuenchedInvariance
