import LongRange.Model.Path

/-!
# Translation and length of coordinate paths

The coordinate path from `v` to `u` is the translate by `u` of the reference path
from `v - u` to zero. Its number of consecutive edges is the integer ℓ¹ displacement.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

variable {d : ℕ}

/-- Translating both endpoints translates every intermediate coordinate-path vertex. -/
lemma coordPathPoint_add (v u a : Site d) (i : Fin d) (k : ℕ) :
    coordPathPoint (v + a) (u + a) i k = coordPathPoint v u i k + a := by
  funext j
  simp only [coordPathPoint, Pi.add_apply, add_sub_add_right_eq_sub]
  split_ifs with hji hji
  · rfl
  · subst j
    ring
  · rfl

/-- Translating both endpoints translates the vertex list of the coordinate path. -/
lemma coordPath_add (v u a : Site d) :
    coordPath (v + a) (u + a) = (coordPath v u).map (· + a) := by
  simp only [coordPath, Pi.add_apply, add_sub_add_right_eq_sub, List.map_cons,
    List.map_flatMap, List.map_map, Function.comp_def, coordPathPoint_add]

/-- Every coordinate path is the translate of the reference path for its displacement. -/
lemma coordPath_eq_reference (v u : Site d) :
    coordPath v u = (coordPath (v - u) 0).map (· + u) := by
  simpa only [sub_add_cancel, zero_add] using coordPath_add (v - u) 0 u

/-- Mapping the coordinate-path vertices maps each consecutive unordered edge. -/
lemma pathEdges_map {α β : Type*} (f : α → β) (L : List α) :
    pathEdges (L.map f) = (pathEdges L).map (Sym2.map f) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simpa only [pathEdges, List.map_cons, List.tail_cons, List.zip_cons_cons,
        List.map_map, Sym2.map_mk] using congrArg (List.cons s(f x, f y)) ih

/-- The number of vertices is one more than the ℓ¹ displacement. -/
lemma coordPath_length (v u : Site d) :
    (coordPath v u).length = 1 + ∑ i, (u i - v i).natAbs := by
  simp only [coordPath, List.length_cons, List.length_flatMap, List.length_map,
    List.length_range]
  rw [← List.sum_toFinset _ (List.nodup_finRange d), List.toFinset_finRange]
  omega

/-- The reference coordinate path has exactly the ℓ¹ number of edges. -/
lemma reference_pathEdges_length (z : Site d) :
    (pathEdges (coordPath z 0)).length = ∑ i, (z i).natAbs := by
  simp only [pathEdges, List.length_map, List.length_zip, List.length_tail,
    coordPath_length, Pi.zero_apply, zero_sub, Int.natAbs_neg]
  omega

end LongRange
