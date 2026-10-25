import LongRangeAudit.QuenchedInvariance.Vocabulary.InitialLaw

/-! # Independent WalkEmbed vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The physical lattice embedded in Euclidean space with its Euclidean metric. -/
def walkEmbed (ε : ℝ) (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (physical ε x)

end LongRange
end

end LongRangeAudit.QuenchedInvariance
