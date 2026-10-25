import LatticeProb.Euclidean.Lattice

/-!
# Euclidean diameter of a subset of `ℝ^d`

The paper's `diam U` is taken for the Euclidean distance `|x - y|`.  The carrier `Fin d → ℝ`
carries the sup-norm, so the diameter is computed after transporting the set to
`EuclideanSpace ℝ (Fin d)`.  For bounded sets it bounds every Euclidean distance
`radius (x - y)` between points of the set.
-/

namespace LongRange

open LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The Euclidean diameter `diam U = sup_{x, y ∈ U} |x - y|` (Mathlib's `Metric.diam` in
`EuclideanSpace ℝ (Fin d)`; it is `0` for the empty set). -/
def euclideanDiam (U : Set (Fin d → ℝ)) : ℝ :=
  Metric.diam ((fun x => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))) '' U)

theorem euclideanDiam_nonneg (U : Set (Fin d → ℝ)) : 0 ≤ euclideanDiam U :=
  Metric.diam_nonneg

/-- In a bounded set, the Euclidean distance between two points is at most the diameter. -/
theorem radius_sub_le_euclideanDiam {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {x y : Fin d → ℝ} (hx : x ∈ U) (hy : y ∈ U) : radius (x - y) ≤ euclideanDiam U := by
  have hb : Bornology.IsBounded
      ((fun x => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))) '' U) :=
    (PiLp.lipschitzWith_toLp 2 (fun _ : Fin d => ℝ)).isBounded_image hU
  have h := Metric.dist_le_diam_of_mem hb (Set.mem_image_of_mem _ hx)
    (Set.mem_image_of_mem _ hy)
  rwa [dist_eq_norm, ← WithLp.toLp_sub, ← radius_norm] at h

end

end LongRange
