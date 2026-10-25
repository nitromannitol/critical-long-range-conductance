import LongRange.Corrector.Cycle.Path
import LongRange.Model.Lattice

/-!
# Oriented cycles and representatives of lattice edges

A cycle consists of the directed long edge followed by the canonical return path.
The first argument of its integer coefficient is the receiving vertex.
-/

namespace LongRange.Cycle

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Directed edges traversed by a vertex list (consecutive pairs). -/
def dirEdges {α : Type*} (L : List α) : List (α × α) := L.zip L.tail

/-- The closed walk of the cycle for the long edge from `u` to `u + v`: the long edge
followed by the return path `γ_{u+v→u}`. -/
def cycleWalk (u v : Site d) : List (Site d × Site d) :=
  (u, u + v) :: dirEdges (coordPath (u + v) u)

/-- The antisymmetric cycle `C_{u+v,u}(x, y)`: the number of traversals `y → x` minus the
number of traversals `x → y`. -/
def cycle (u v x y : Site d) : ℤ :=
  ((cycleWalk u v).count (y, x) : ℤ) - (cycleWalk u v).count (x, y)

open Classical in
/-- The index set `𝓘_ε` of representatives `(u, v)` of unordered edges touching `U^ε`. -/
def indexSet (ε : ℝ) (U : Set (Fin d → ℝ)) : Set (Site d × Site d) :=
  {p | p.1 ∈ latticeSet ε U ∧ p.2 ≠ 0 ∧
    (p.1 + p.2 ∉ latticeSet ε U ∨ toLex p.1 < toLex (p.1 + p.2))}

/-- Reversing an oriented edge negates its cycle coefficient. -/
theorem cycle_antisymm (u v x y : Site d) : cycle u v x y = -cycle u v y x := by
  unfold cycle
  omega

/-- A cycle has no diagonal coefficient. -/
theorem cycle_self (u v x : Site d) : cycle u v x x = 0 := by
  simp only [cycle, sub_self]

/-- The endpoints of all traversals contain the support at every fixed vertex. -/
def cycleSupport (u v : Site d) : Finset (Site d) :=
  ((cycleWalk u v).map Prod.fst ++ (cycleWalk u v).map Prod.snd).toFinset

/-- Every nonzero coefficient has its second vertex in the finite endpoint set. -/
theorem mem_cycleSupport (u v x y : Site d) (h : cycle u v x y ≠ 0) :
    y ∈ cycleSupport u v := by
  classical
  have hm : (y, x) ∈ cycleWalk u v ∨ (x, y) ∈ cycleWalk u v := by
    by_contra hn
    simp only [not_or] at hn
    apply h
    simp only [cycle, List.count_eq_zero.mpr hn.1, List.count_eq_zero.mpr hn.2,
      Nat.cast_zero, sub_self]
  simp only [cycleSupport, List.mem_toFinset, List.mem_append, List.mem_map]
  rcases hm with hm | hm
  · exact Or.inl ⟨(y, x), hm, rfl⟩
  · exact Or.inr ⟨(x, y), hm, rfl⟩

/-- Each row of the integer cycle has finite support. -/
theorem cycle_support_finite (u v x : Site d) :
    {y | cycle u v x y ≠ 0}.Finite := by
  apply (cycleSupport u v).finite_toSet.subset
  intro y hy
  exact mem_cycleSupport u v x y hy

/-- The coefficients in the divergence sum have finite support. -/
theorem cycle_column_support_finite (u v x : Site d) :
    {y | cycle u v y x ≠ 0}.Finite := by
  apply (cycle_support_finite u v x).subset
  intro y hy hz
  apply hy
  rw [cycle_antisymm, hz, neg_zero]

/-- The sources of the return-path traversals are exactly its vertices except the last. -/
lemma dirEdges_coordPath_fst (v u : Site d) :
    (dirEdges (coordPath v u)).map Prod.fst = (coordPath v u).dropLast := by
  have h : ∀ L : List (Site d), (dirEdges L).map Prod.fst = L.dropLast := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih =>
      cases L with
      | nil => rfl
      | cons b L =>
        simpa only [dirEdges, List.tail_cons, List.zip_cons_cons, List.map_cons,
          List.dropLast_cons_cons] using congrArg (List.cons a) ih
  exact h _

/-- Each vertex is the source of at most one traversal of the cycle walk. -/
lemma cycleWalk_fst_nodup (u v : Site d) : ((cycleWalk u v).map Prod.fst).Nodup := by
  classical
  have hp : coordPath (u + v) u = (coordPath (u + v) u).dropLast ++ [u] := by
    have he := List.dropLast_concat_getLast
      (show coordPath (u + v) u ≠ [] by simp only [coordPath, ne_eq,
        List.cons_ne_nil, not_false_eq_true])
    have hl := coordPath_last (u + v) u
    have hlast : (coordPath (u + v) u).getLast (by simp [coordPath]) = u :=
      (List.getLast_eq_iff_getLast?_eq_some _).mpr hl
    simpa only [hlast] using he.symm
  have hn := coordPath_nodup (u + v) u
  rw [hp, List.nodup_append'] at hn
  simp only [cycleWalk, List.map_cons, dirEdges_coordPath_fst, List.nodup_cons]
  refine ⟨?_, hn.1⟩
  intro hm
  exact List.disjoint_left.mp hn.2.2 hm (by simp only [List.mem_singleton])

/-- Every directed edge occurs at most once in the cycle walk. -/
lemma cycleWalk_count_le_one (u v x y : Site d) :
    (cycleWalk u v).count (x, y) ≤ 1 := by
  exact (List.count_le_count_map (f := Prod.fst)).trans
    ((List.nodup_iff_count_le_one.mp (cycleWalk_fst_nodup u v)) x)

/-- The integer cycle coefficient has absolute value at most one. -/
theorem cycle_abs_le_one (u v x y : Site d) : |cycle u v x y| ≤ 1 := by
  have hxy := cycleWalk_count_le_one u v x y
  have hyx := cycleWalk_count_le_one u v y x
  rw [abs_le]
  unfold cycle
  constructor <;> omega

/-- A nonzero coefficient lies on the long edge or on the canonical return path. -/
theorem cycle_support (u v x y : Site d) (h : cycle u v x y ≠ 0) :
    s(x, y) = s(u, u + v) ∨ s(x, y) ∈ pathEdges (coordPath (u + v) u) := by
  classical
  have hm : (y, x) ∈ cycleWalk u v ∨ (x, y) ∈ cycleWalk u v := by
    by_contra hn
    simp only [not_or] at hn
    apply h
    simp only [cycle, List.count_eq_zero.mpr hn.1, List.count_eq_zero.mpr hn.2,
      Nat.cast_zero, sub_self]
  simp only [cycleWalk, List.mem_cons] at hm
  rcases hm with (he | he) | (he | he)
  · left
    have hsym := congrArg (fun p : Site d × Site d => s(p.1, p.2)) he
    exact (Sym2.eq_swap).trans hsym
  · right
    exact List.mem_map.mpr ⟨(y, x), he, Sym2.eq_swap⟩
  · left
    exact congrArg (fun p : Site d × Site d => s(p.1, p.2)) he
  · right
    exact List.mem_map.mpr ⟨(x, y), he, rfl⟩

/-- The return-path alternative in the support theorem consists of nearest-neighbour edges. -/
theorem cycle_support_isNNEdge (u v x y : Site d)
    (h : s(x, y) ∈ pathEdges (coordPath (u + v) u)) : IsNNEdge s(x, y) :=
  mem_pathEdges_isNNEdge (u + v) u s(x, y) h

/-- A displacement outside the positive and negative unit vectors gives a nonlocal edge. -/
lemma long_edge_not_isNNEdge (u v : Site d)
    (hv : ∀ i : Fin d, v ≠ unit i ∧ v ≠ -unit i) : ¬IsNNEdge s(u, u + v) := by
  rintro ⟨a, i, he⟩
  rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · apply (hv i).1
    rw [ha] at hb
    exact add_left_cancel hb
  · apply (hv i).2
    have heq : u = (u + v) + unit i :=
      ha.trans (congrArg (· + unit i) hb.symm)
    have h : v + unit i = 0 := by
      apply add_left_cancel (a := u)
      simpa only [add_assoc, add_zero] using heq.symm
    exact eq_neg_of_add_eq_zero_left h

/-- On a nonlocal long edge, the cycle carries one unit in the prescribed direction. -/
theorem cycle_long_edge (u v : Site d) (hv : ∀ i : Fin d, v ≠ unit i ∧ v ≠ -unit i)
    (hv0 : v ≠ 0) : cycle u v (u + v) u = 1 := by
  classical
  have hn := long_edge_not_isNNEdge u v hv
  have hret : s(u, u + v) ∉ pathEdges (coordPath (u + v) u) :=
    fun h => hn (mem_pathEdges_isNNEdge _ _ _ h)
  have h₁ : (u, u + v) ∉ dirEdges (coordPath (u + v) u) := by
    intro h
    exact hret (List.mem_map.mpr ⟨(u, u + v), h, rfl⟩)
  have h₂ : (u + v, u) ∉ dirEdges (coordPath (u + v) u) := by
    intro h
    exact hret (List.mem_map.mpr ⟨(u + v, u), h, Sym2.eq_swap⟩)
  have hne : u ≠ u + v := by
    intro h
    exact hv0 (add_left_cancel (h.symm.trans (add_zero u).symm))
  have he : (u, u + v) ≠ (u + v, u) := fun h => hne (congrArg Prod.fst h)
  simp only [cycle, cycleWalk, List.count_cons_self, List.count_eq_zero.mpr h₁,
    List.count_cons_of_ne he, List.count_eq_zero.mpr h₂, Nat.zero_add,
    Nat.cast_one, Nat.cast_zero, sub_zero]

/-- A coordinate path of one edge has exactly its prescribed endpoints. -/
lemma coordPath_eq_pair_of_length (a b : Site d) (hlen : (coordPath a b).length = 2) :
    coordPath a b = [a, b] := by
  obtain ⟨c, hc⟩ : ∃ c, coordPath a b = [a, c] := by
    unfold coordPath at hlen ⊢
    have ht : ((List.finRange d).flatMap fun i =>
        (List.range (b i - a i).natAbs).map
          fun k => coordPathPoint a b i (k + 1)).length = 1 := by
      simp only [List.length_cons] at hlen
      omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp ht
    exact ⟨c, congrArg (List.cons a) hc⟩
  have hl := coordPath_last a b
  rw [hc] at hl
  have he : c = b := by simpa only [List.getLast?_cons_cons,
    List.getLast?_singleton, Option.some.injEq] using hl
  simpa only [he] using hc

/-- A unit displacement gives a return path with a single edge. -/
lemma coordPath_unit (u : Site d) (i : Fin d) :
    coordPath (u + unit i) u = [u + unit i, u] := by
  apply coordPath_eq_pair_of_length
  simp [coordPath_length, unit, Pi.single_apply, apply_ite]

/-- A negative unit displacement also gives a single-edge return path. -/
lemma coordPath_neg_unit (u : Site d) (i : Fin d) :
    coordPath (u + -unit i) u = [u + -unit i, u] := by
  apply coordPath_eq_pair_of_length
  simp [coordPath_length, unit, Pi.single_apply, apply_ite]

/-- The long-edge and return-edge contributions cancel for either unit orientation. -/
theorem cycle_eq_zero_of_unit (u v x y : Site d) (i : Fin d)
    (hv : v = unit i ∨ v = -unit i) : cycle u v x y = 0 := by
  classical
  have hp : coordPath (u + v) u = [u + v, u] := by
    rcases hv with rfl | rfl
    · exact coordPath_unit u i
    · exact coordPath_neg_unit u i
  simp only [cycle, cycleWalk, hp, dirEdges, List.tail_cons, List.zip_cons_cons,
    List.zip_nil_right, List.count_cons, List.count_nil]
  simp only [beq_iff_eq, Prod.mk.injEq]
  have he₁ : ((u, u + v) = (y, x)) ↔ ((u + v, u) = (x, y)) := by
    simp only [Prod.mk.injEq, and_comm]
  have he₂ : ((u + v, u) = (y, x)) ↔ ((u, u + v) = (x, y)) := by
    simp only [Prod.mk.injEq, and_comm]
  simp only [Prod.mk.injEq] at he₁ he₂
  simp only [he₁, he₂]
  omega

/-- The incoming and outgoing vertex lists have the same multiplicities. -/
lemma cycleWalk_count_fst_eq_snd (u v x : Site d) :
    ((cycleWalk u v).map Prod.fst).count x =
      ((cycleWalk u v).map Prod.snd).count x := by
  classical
  have hp : coordPath (u + v) u = (coordPath (u + v) u).dropLast ++ [u] := by
    have he := List.dropLast_concat_getLast
      (show coordPath (u + v) u ≠ [] by simp only [coordPath, ne_eq,
        List.cons_ne_nil, not_false_eq_true])
    have hlast : (coordPath (u + v) u).getLast (by simp [coordPath]) = u :=
      (List.getLast_eq_iff_getLast?_eq_some _).mpr (coordPath_last (u + v) u)
    simpa only [hlast] using he.symm
  have hs : (cycleWalk u v).map Prod.snd = coordPath (u + v) u := by
    have hlen : (coordPath (u + v) u).tail.length ≤ (coordPath (u + v) u).length := by
      simp only [List.length_tail]
      omega
    rw [cycleWalk, List.map_cons, dirEdges, List.map_snd_zip hlen]
    rfl
  rw [hs]
  simp only [cycleWalk, List.map_cons, dirEdges_coordPath_fst]
  conv_rhs => rw [hp, List.count_append]
  simp only [List.count_cons, List.count_nil, Nat.zero_add]

/-- The cycle is divergence free at every lattice vertex. -/
theorem cycle_divergence (u v x : Site d) : ∑' y, (cycle u v y x : ℝ) = 0 := by
  classical
  let S := cycleSupport u v
  have hcount : ∀ W : List (Site d × Site d),
      (∀ p ∈ W, p.1 ∈ S ∧ p.2 ∈ S) →
      (∑ y ∈ S, (W.count (x, y) : ℝ)) = ((W.map Prod.fst).count x : ℝ) ∧
      (∑ y ∈ S, (W.count (y, x) : ℝ)) = ((W.map Prod.snd).count x : ℝ) := by
    intro W
    induction W with
    | nil =>
      intro _
      simp only [List.count_nil, Nat.cast_zero, Finset.sum_const_zero, List.map_nil,
        and_self]
    | cons p W ih =>
      intro hW
      have hp := hW p (List.mem_cons_self ..)
      have ht := ih (fun q hq => hW q (List.mem_cons_of_mem _ hq))
      rcases p with ⟨a, b⟩
      dsimp only at hp
      constructor
      · by_cases ha : a = x
        · subst a
          simp [List.count_cons, Finset.sum_add_distrib, hp.2, ht.1]
        · simp [ha, ht.1]
      · by_cases hb : b = x
        · subst b
          simp [List.count_cons, Finset.sum_add_distrib, hp.1, ht.2]
        · simp [hb, ht.2]
  have hW : ∀ p ∈ cycleWalk u v, p.1 ∈ S ∧ p.2 ∈ S := by
    intro p hp
    constructor
    · exact List.mem_toFinset.mpr (List.mem_append_left _
        (List.mem_map.mpr ⟨p, hp, rfl⟩))
    · exact List.mem_toFinset.mpr (List.mem_append_right _
        (List.mem_map.mpr ⟨p, hp, rfl⟩))
  rw [tsum_eq_sum (s := S) (fun y hy => ?_)]
  · simp only [cycle, Int.cast_sub, Int.cast_natCast, Finset.sum_sub_distrib]
    rw [(hcount _ hW).1, (hcount _ hW).2, cycleWalk_count_fst_eq_snd]
    exact sub_self _
  · have hz : cycle u v x y = 0 := by
      by_contra hz
      exact hy (mem_cycleSupport u v x y hz)
    rw [cycle_antisymm, hz, neg_zero, Int.cast_zero]

/-- Each representative starts inside the lattice set and has nonzero displacement. -/
theorem indexSet_endpoints (ε : ℝ) (U : Set (Fin d → ℝ)) (u v : Site d)
    (h : (u, v) ∈ indexSet ε U) : u ∈ latticeSet ε U ∧ v ≠ 0 :=
  ⟨h.1, h.2.1⟩

/-- Exactly one orientation represents an edge whose first endpoint is in the lattice set. -/
theorem indexSet_exactly_one (ε : ℝ) (U : Set (Fin d → ℝ)) (x z : Site d)
    (hx : x ∈ latticeSet ε U) (hz : z ≠ 0) :
    ((x, z) ∈ indexSet ε U ∧ (x + z, -z) ∉ indexSet ε U) ∨
      ((x, z) ∉ indexSet ε U ∧ (x + z, -z) ∈ indexSet ε U) := by
  classical
  have hne : x ≠ x + z := by
    intro h
    apply hz
    exact (add_left_cancel (h.symm.trans (add_zero x).symm))
  have hlex : toLex x ≠ toLex (x + z) := fun h => hne (toLex_inj.mp h)
  have hf : (x, z) ∈ indexSet ε U ↔
      x + z ∉ latticeSet ε U ∨ toLex x < toLex (x + z) :=
    ⟨fun h => h.2.2, fun h => ⟨hx, hz, h⟩⟩
  have hr : (x + z, -z) ∈ indexSet ε U ↔
      x + z ∈ latticeSet ε U ∧ toLex (x + z) < toLex x := by
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      rcases h.2.2 with hout | hlt
      · exact False.elim (hout (by simpa only [add_neg_cancel_right] using hx))
      · simpa only [add_neg_cancel_right] using hlt
    · rintro ⟨hmem, hlt⟩
      exact ⟨hmem, neg_ne_zero.mpr hz,
        Or.inr (by simpa only [add_neg_cancel_right] using hlt)⟩
  rw [hf, hr]
  by_cases hmem : x + z ∈ latticeSet ε U
  · simp only [hmem, not_true_eq_false, false_or, true_and]
    rcases lt_or_gt_of_ne hlex with h | h
    · exact Or.inl ⟨h, not_lt_of_gt h⟩
    · exact Or.inr ⟨not_lt_of_gt h, h⟩
  · simp only [hmem, not_false_eq_true, true_or, false_and, and_self]

end

end LongRange.Cycle
