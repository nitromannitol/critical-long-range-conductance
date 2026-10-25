import LongRangeAudit.QuenchedInvariance.Vocabulary.WalkEmbed

/-! # Independent EpsFilter vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# The positive epsilon filter

Convergence through epsilon values in `(0,1)` is equivalent to convergence along
all sequences of such values tending to zero.
-/

open Filter Set
open scoped Topology

namespace LatticeProb

/-- The carrier of epsilon values strictly between zero and one. -/
abbrev Eps := {ε : ℝ // ε ∈ Ioo 0 1}

/-- Approach zero through epsilon values strictly between zero and one. -/
def epsFilter : Filter Eps := comap Subtype.val (𝓝[Ioo (0 : ℝ) 1] 0)

/-- The epsilon filter inherits a countable basis from the real neighborhood filter. -/
instance : epsFilter.IsCountablyGenerated := by
  unfold epsFilter
  infer_instance

/-- Positive epsilon values accumulate at zero, so the epsilon filter is nontrivial. -/
instance : epsFilter.NeBot := by
  unfold epsFilter
  have : (𝓝[Ioo (0 : ℝ) 1] 0).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
    infer_instance
  exact Filter.comap_coe_neBot_of_le_principal inf_le_right

end LatticeProb
end LongRangeAudit.QuenchedInvariance
