import LongRangeAudit.QuenchedInvariance.Vocabulary.WeightedGraph

/-! # Independent RegularVariation vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LatticeProb
open Filter
open scoped Topology
variable {d : ℕ}

/-- **Regular variation at infinity with index `ρ`**: the ratio limit
`f (λ r) / f r → λ ^ ρ` for every `λ > 0`. -/
def RegularlyVaryingAtTop (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → Tendsto (fun r : ℝ => f (lam * r) / f r) atTop (𝓝 (lam ^ ρ))

end LatticeProb
end

end LongRangeAudit.QuenchedInvariance
