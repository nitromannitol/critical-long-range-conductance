import LongRangeAudit.QuenchedInvariance.Vocabulary.ChenKimKumagaiWang

/-! # Independent ContinuousMapMeasurable vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance
namespace LatticeProb
instance continuousMapMeasurableSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] : MeasurableSpace C(X, Y) := borel _
instance continuousMapBorel {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] : BorelSpace C(X, Y) := ⟨rfl⟩
end LatticeProb
end LongRangeAudit.QuenchedInvariance
