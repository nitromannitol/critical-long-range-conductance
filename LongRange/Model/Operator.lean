import LongRange.Model.Conductance

/-!
# The rescaled nonlocal operator `L^ε`

For a conductance configuration `a` and `h : εℤ^d → ℝ`,
`L^ε h(x) = (ε^d / κ_ε) ∑_{z ∈ εℤ^d ∖ {0}} a(x/ε, (x+z)/ε) (h(x+z) - h(x)) |z|^{-(d+2)}`.
At the physical point `x = εq` and increment `z = εw`, the conductance `a(x/ε, (x+z)/ε)` is the
value on the edge `{q, q + w}`.  The series is a `tsum` over the countable set of increments;
it converges absolutely when the conductances are bounded and `h` is bounded or affine plus
bounded, which is how the paper uses it.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The rescaled operator `L^ε h` evaluated at the physical point `εq`. -/
def generator (ε : ℝ) (a : Edge d → ℝ) (h : Site d → ℝ) (q : Site d) : ℝ :=
  ε ^ d / kappa d ε * ∑' w : Site d,
    if hw : w = 0 then 0
    else a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w)

end

end LongRange
