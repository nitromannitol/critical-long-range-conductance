import LatticeProb.Euclidean.Lattice

/-!
# Coordinate paths on `ℤ^d` and `εℤ^d`

For sites `v` and `u`, the nearest-neighbour path `γ_{v→u}` starts at `v` and changes the
coordinates one at a time, in the order `0, 1, …, d - 1`, by unit steps toward `u`; it is
recorded as its list of vertices.  An undirected nearest-neighbour edge is an unordered pair
`{x, x + e_i}`, and a path uses an edge when two consecutive vertices form that pair.  On the
scaled lattice `εℤ^d` the path is the image of the integer path under `q ↦ εq`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The vertex of `γ_{v→u}` reached after the coordinates `j < i` have been changed to `u j`
and coordinate `i` has moved `k` unit steps from `v i` toward `u i`. -/
def coordPathPoint (v u : Site d) (i : Fin d) (k : ℕ) : Site d :=
  fun j => if j < i then u j else if j = i then v i + k * Int.sign (u i - v i) else v j

/-- The nearest-neighbour path `γ_{v→u}` from `v` to `u` changing coordinates one at a time in
the order `0, …, d - 1`, as its list of vertices. -/
def coordPath (v u : Site d) : List (Site d) :=
  v :: (List.finRange d).flatMap fun i =>
    (List.range (u i - v i).natAbs).map fun k => coordPathPoint v u i (k + 1)

/-- The undirected edges traversed by a list of vertices: consecutive vertices as unordered
pairs. -/
def pathEdges {α : Type*} (L : List α) : List (Sym2 α) :=
  (L.zip L.tail).map fun p => s(p.1, p.2)

/-- `e` is an undirected nearest-neighbour edge `{x, x + e_i}` of `ℤ^d`. -/
def IsNNEdge (e : Sym2 (Site d)) : Prop :=
  ∃ x : Site d, ∃ i : Fin d, e = s(x, x + unit i)

/-- `e` is an undirected nearest-neighbour edge `{εx, ε(x + e_i)}` of `εℤ^d`. -/
def IsScaledNNEdge (ε : ℝ) (e : Sym2 (Fin d → ℝ)) : Prop :=
  ∃ x : Site d, ∃ i : Fin d, e = s(physical ε x, physical ε (x + unit i))

/-- The path `γ_{v→u}` on `εℤ^d` from the physical point `εv` to the physical point `εu`: the
image of the integer path under `q ↦ εq`. -/
def scaledCoordPath (ε : ℝ) (v u : Site d) : List (Fin d → ℝ) :=
  (coordPath v u).map (physical ε)

end

end LongRange
