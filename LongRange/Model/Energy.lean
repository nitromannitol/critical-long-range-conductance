import LongRange.Model.Conductance

/-!
# The critical energy and the macroscopic bilinear form

For `h : εℤ^d → ℝ` supported in a bounded `U^ε`, the critical seminorm is
`‖h‖²_{H¹_crit(U^ε)} = (ε^{2d} / κ_ε) ∑_{x, z ∈ εℤ^d} J(z) (h(x+z) - h(x))²`
(eq. (e.H1crit)); the formula does not depend on `U`, which only constrains the support.  The
bilinear form of (e.Daeps) is
`D_a^ε(u, v) = (ε^{2d} / 2κ_ε) ∑_{x, z ∈ εℤ^d, z ≠ 0} a(x/ε, (x+z)/ε) J(z)
(u(x+z) - u(x)) (v(x+z) - v(x))`, and `D_a^ε(u) = D_a^ε(u, u)`.  Both double sums are `tsum`s over
pairs `(x, z)` indexed by integer sites.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The squared critical seminorm `‖h‖²_{H¹_crit}` of (e.H1crit). -/
def h1CritSq (ε : ℝ) (h : Site d → ℝ) : ℝ :=
  ε ^ (2 * d) / kappa d ε * ∑' p : Site d × Site d,
    jumpKernel (physical ε p.2) * (h (p.1 + p.2) - h p.1) ^ 2

/-- The macroscopic bilinear form `D_a^ε(u, v)` of (e.Daeps). -/
def bilinForm (ε : ℝ) (a : Edge d → ℝ) (u v : Site d → ℝ) : ℝ :=
  ε ^ (2 * d) / (2 * kappa d ε) * ∑' p : Site d × Site d,
    if hw : p.2 = 0 then 0
    else a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
      (u (p.1 + p.2) - u p.1) * (v (p.1 + p.2) - v p.1)

end

end LongRange
