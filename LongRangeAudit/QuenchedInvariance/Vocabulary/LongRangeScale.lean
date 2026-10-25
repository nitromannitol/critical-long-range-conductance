import LongRangeAudit.QuenchedInvariance.Vocabulary.RegularVariation

/-! # Independent LongRangeScale vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# Scale and asymptotic inverse conventions

Scale functions are represented on the reals and constrained on the nonnegative half-line.
Their values on the negative half-line do not enter any graph estimate or limit at infinity.
-/

namespace LatticeProb.Graph.LongRangeKernel

open Filter Topology MeasureTheory

noncomputable section

/-- The integral scale in MSC, with the source's continuous extension at zero. -/
def eta (γ : ℝ) (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then γ * φ 0 else r ^ γ / ∫ s in (0 : ℝ)..r, s ^ (γ - 1) / φ s

/-- Asymptotic inverse means both compositions divided by the identity tend to one. -/
def IsAsymptoticInverse (f g : ℝ → ℝ) : Prop :=
  Tendsto (fun t => f (g t) / t) atTop (𝓝 1) ∧
    Tendsto (fun t => g (f t) / t) atTop (𝓝 1)

/-- The volume profile is positive, continuous, strictly increasing, and doubling. -/
def IsVolumeProfile (V : ℝ → ℝ) : Prop :=
  ContinuousOn V (Set.Ici 0) ∧ StrictMonoOn V (Set.Ici 0) ∧
    (∀ r, 0 ≤ r → 0 < V r) ∧
    ∃ C_D : ℝ, 1 < C_D ∧ ∀ r, 0 < r → V (2 * r) ≤ C_D * V r

/-- The jump scale has the source's range, continuity and positive regular variation index. -/
def IsJumpScale (φ : ℝ → ℝ) : Prop :=
  ContinuousOn φ (Set.Ici 0) ∧ (∀ r, 0 ≤ r → 1 ≤ φ r) ∧
    ∃ β : ℝ, 0 < β ∧ LatticeProb.RegularlyVaryingAtTop φ β

/-- The inverse scale is continuous, nondecreasing, bounded below by one, and asymptotic. -/
def IsInverseScale (γ : ℝ) (φ ζ : ℝ → ℝ) : Prop :=
  ContinuousOn ζ (Set.Ici 0) ∧ MonotoneOn ζ (Set.Ici 0) ∧
    (∀ r, 0 ≤ r → 1 ≤ ζ r) ∧ IsAsymptoticInverse (eta γ φ) ζ

end
end LatticeProb.Graph.LongRangeKernel

end LongRangeAudit.QuenchedInvariance
