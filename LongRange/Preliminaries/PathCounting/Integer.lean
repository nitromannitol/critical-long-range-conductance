import LongRange.Preliminaries.PathCounting.Translation

/-!
# Counting integer translates of a coordinate path

Each reference edge determines at most one translate using a prescribed unordered edge.
Choosing a reference edge gives an injection from qualifying endpoint pairs into the
finite set of reference edges, whose size is bounded by the path length.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

variable {d : ℕ}

/-- An unordered integer edge determines at most one translation onto a fixed edge. -/
lemma reference_edge_translate_injective (a : Sym2 (Site d)) :
    Function.Injective (fun u : Site d => Sym2.map (· + u) a) := by
  induction a using Sym2.inductionOn with
  | _ x y =>
    intro u v h
    change s(x + u, y + u) = s(x + v, y + v) at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨hx, _⟩ | ⟨hx, hy⟩
    · exact add_left_cancel hx
    · funext i
      have hx' := congrFun hx i
      have hy' := congrFun hy i
      simp only [Pi.add_apply] at hx' hy'
      change u i = v i
      omega

/-- The endpoint pairs of a fixed displacement using an edge form a finite set of
cardinality at most the integer ℓ¹ displacement. -/
lemma integer_path_counting (z : Site d) (e : Sym2 (Site d)) :
    {p : Site d × Site d | p.2 - p.1 = z ∧
      e ∈ pathEdges (coordPath p.2 p.1)}.Finite ∧
    Nat.card {p : Site d × Site d | p.2 - p.1 = z ∧
      e ∈ pathEdges (coordPath p.2 p.1)} ≤ ∑ i, (z i).natAbs := by
  classical
  let S := {p : Site d × Site d | p.2 - p.1 = z ∧
    e ∈ pathEdges (coordPath p.2 p.1)}
  let T := (pathEdges (coordPath z 0)).toFinset
  have hex : ∀ p : S, ∃ a : T, Sym2.map (· + p.val.1) a.val = e := by
    intro p
    have hp := p.property.2
    rw [coordPath_eq_reference, p.property.1, pathEdges_map, List.mem_map] at hp
    obtain ⟨a, ha, he⟩ := hp
    exact ⟨⟨a, List.mem_toFinset.mpr ha⟩, he⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro p q hpq
    have he : Sym2.map (· + p.val.1) (f p).val =
        Sym2.map (· + q.val.1) (f p).val := by
      rw [hf p, hpq, hf q]
    have hu := reference_edge_translate_injective (f p).val he
    apply Subtype.ext
    apply Prod.ext hu
    have hp := p.property.1
    have hq := q.property.1
    rw [hu] at hp
    exact sub_left_inj.mp (hp.trans hq.symm)
  letI : Finite S := Finite.of_injective f hinj
  refine ⟨Set.toFinite S, ?_⟩
  calc
    Nat.card S ≤ Nat.card T := Nat.card_le_card_of_injective f hinj
    _ = T.card := Nat.card_eq_finsetCard T
    _ ≤ (pathEdges (coordPath z 0)).length := List.toFinset_card_le _
    _ = ∑ i, (z i).natAbs := reference_pathEdges_length z

end LongRange
