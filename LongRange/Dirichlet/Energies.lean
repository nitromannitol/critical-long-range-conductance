import LongRange.Dirichlet.RandomDefect

/-!
# The nearest-neighbour defect energies of Proposition 3.3

`F_ε(p)` of Step 3 and its short- and long-range parts, as functions of a defect array `D` and a
finite set `S` of observation sites (in applications `S = U^ε`).
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- `ε^(3d+2)/κ_ε · ∑_{x ∈ S} ∑_i (D(x, e_i)² + D(x, −e_i)²)`: the energy `F_ε` of Step 3 for the
defect array `D x z = Σ(x + z, x)`. -/
def nnEnergy (ε : ℝ) (S : Finset (Site d)) (D : Site d → Site d → ℝ) : ℝ :=
  ε ^ (3 * d + 2) / kappa d ε *
    ∑ x ∈ S, ∑ i : Fin d, (D x (unit i) ^ 2 + D x (-unit i) ^ 2)

end

end LongRange.Dirichlet
