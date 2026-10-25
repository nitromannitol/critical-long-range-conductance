import LatticeProb.Euclidean.Lattice

/-!
# The critical jump kernel and its logarithmic normalization

Functions on the rescaled lattice `εℤ^d` are indexed by integer sites: the value at the
physical point `εq` is stored at `q : Site d`, and `physical ε q` is that point.  The norm
`|z|` of the paper is the Euclidean radius `radius z = √(∑ z_k²)`, never the sup-norm.

This module defines the jump kernel `J(z) = |z|^{-(d+2)}` (with `J(0) = 0`) and the
normalization `κ_ε = ε^d ∑_{z ∈ εℤ^d ∖ {0}, |z| ≤ 1} |z|^{-d}`.  The finite index set is the
library's `unitBallIndices d ε`, which for `ε > 0` is exactly the set of nonzero `q` with
`|εq| ≤ 1` (`LatticeProb.Euclidean.Lattice.mem_unitBallIndices`).
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The critical jump kernel `J(z) = |z|^{-(d+2)}` on `ℝ^d ∖ {0}`, with `J(0) = 0`, where `|z|`
is the Euclidean radius. -/
def jumpKernel (z : Fin d → ℝ) : ℝ :=
  if z = 0 then 0 else (radius z ^ (d + 2))⁻¹

/-- The normalization `κ_ε = ε^d ∑_{z ∈ εℤ^d ∖ {0}, |z| ≤ 1} |z|^{-d}`, written over the integer
indices `q` of the points `z = εq`. -/
def kappa (d : ℕ) (ε : ℝ) : ℝ :=
  ε ^ d * ∑ q ∈ unitBallIndices d ε, (radius (physical ε q) ^ d)⁻¹

/-- The kernel vanishes at the origin. -/
theorem jumpKernel_zero : jumpKernel (0 : Fin d → ℝ) = 0 := by
  simp [jumpKernel]

/-- Away from the origin the kernel is `|z|^{-(d+2)}`. -/
theorem jumpKernel_of_ne_zero {z : Fin d → ℝ} (hz : z ≠ 0) :
    jumpKernel z = (radius z ^ (d + 2))⁻¹ := by
  simp [jumpKernel, hz]

end

end LongRange
