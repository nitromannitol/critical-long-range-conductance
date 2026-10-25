import LongRangeAudit.QuenchedInvariance.Vocabulary.Conductance

/-! # Independent KappaPositivity vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The normalization is nonnegative at nonnegative scales. -/
theorem kappa_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ kappa d ε := by
  unfold kappa
  exact mul_nonneg (pow_nonneg hε _) (Finset.sum_nonneg (fun _ _ =>
    inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)))

end LongRange
end

end LongRangeAudit.QuenchedInvariance
