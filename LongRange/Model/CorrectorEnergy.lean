import LongRange.Model.Energy

/-!
# The first-order corrector functional and its energy `ν(U^ε, p)`

For a slope `p ∈ ℝ^d`, the functional of (e.nu) acts on `w : εℤ^d → ℝ` supported in `U^ε`:
`(ε^{2d} / 2κ_ε) ∑ a(x/ε, (x+z)/ε) J(z) [(p·z + w(x+z) - w(x))² - |p·z|²]`, summed over
`x, z ∈ εℤ^d` with `z ≠ 0` and `x ∈ U^ε` or `x + z ∈ U^ε`.  The slope pairs with the physical
increment `z = εq₂`, so `p · z = linearFn ε p q₂`.  The energy is
`ν(U^ε, p) = -inf_w (functional w)` over `w` supported in `U^ε`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

open Classical in
/-- The corrector functional of (e.nu) evaluated at `w`. -/
def correctorFunctional (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (w : Site d → ℝ) : ℝ :=
  ε ^ (2 * d) / (2 * kappa d ε) * ∑' q : Site d × Site d,
    if hz : q.2 = 0 then 0
    else if q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U then
      a (edgeAdd q.1 q.2 hz) * jumpKernel (physical ε q.2) *
        ((linearFn ε p q.2 + w (q.1 + q.2) - w q.1) ^ 2 - linearFn ε p q.2 ^ 2)
    else 0

/-- The corrector energy `ν(U^ε, p) = -inf_w (functional w)`, the infimum running over the
functions `w` supported in `U^ε`. -/
def correctorEnergy (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ) (p : Fin d → ℝ) : ℝ :=
  -sInf (Set.range fun w : {w : Site d → ℝ // SupportedIn ε U w} =>
    correctorFunctional ε U a p w)

end

end LongRange
