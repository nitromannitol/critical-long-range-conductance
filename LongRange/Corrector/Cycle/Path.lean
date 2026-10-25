import LongRange.Preliminaries.PathCounting.Translation

/-!
# Distinct vertices of the canonical return path

Within each coordinate block the moving coordinate changes strictly. Different blocks
are separated by the last moving coordinate, so the canonical path never revisits a vertex.
-/

namespace LongRange.Cycle

open LatticeProb

variable {d : ℕ}

/-- A coordinate block with at least one step has nonzero direction. -/
lemma coordPath_sign_ne_zero (v u : Site d) (i : Fin d) (k : ℕ)
    (hk : k < (u i - v i).natAbs) : Int.sign (u i - v i) ≠ 0 := by
  intro h
  have he : u i - v i = 0 := Int.sign_eq_zero_iff_zero.mp h
  simp only [he, Int.natAbs_zero] at hk
  omega

/-- Every recorded point of a coordinate block has left that coordinate's initial value. -/
lemma coordPathPoint_active_ne (v u : Site d) (i : Fin d) (k : ℕ)
    (hk : k < (u i - v i).natAbs) : coordPathPoint v u i (k + 1) i ≠ v i := by
  have hs := coordPath_sign_ne_zero v u i k hk
  simp only [coordPathPoint, lt_self_iff_false, ↓reduceIte]
  intro h
  have hm : ((k + 1 : ℕ) : ℤ) * Int.sign (u i - v i) = 0 := by omega
  rcases mul_eq_zero.mp hm with h | h
  · omega
  · exact hs h

/-- All vertices of a canonical coordinate path are distinct. -/
theorem coordPath_nodup (v u : Site d) : (coordPath v u).Nodup := by
  classical
  rw [coordPath, List.nodup_cons]
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hi
    have hn := coordPathPoint_active_ne v u i k (List.mem_range.mp hk)
    exact hn (congrFun he i)
  · rw [List.nodup_flatMap]
    constructor
    · intro i _
      apply List.Nodup.map_on _ List.nodup_range
      intro k hk l _ he
      have hs := coordPath_sign_ne_zero v u i k (List.mem_range.mp hk)
      have hi := congrFun he i
      simp only [coordPathPoint, lt_self_iff_false, ↓reduceIte] at hi
      have hm : ((k + 1 : ℕ) : ℤ) = ((l + 1 : ℕ) : ℤ) :=
        mul_right_cancel₀ hs (add_left_cancel hi)
      omega
    · apply (List.nodup_finRange d).imp
      intro i j hij
      rw [Function.onFun, List.disjoint_left]
      intro a ha hb
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      obtain ⟨l, hl, he⟩ := List.mem_map.mp hb
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hn := coordPathPoint_active_ne v u j l (List.mem_range.mp hl)
        apply hn
        have he' := congrFun he j
        simpa only [coordPathPoint, not_lt.mpr (le_of_lt hij), ne_of_gt hij,
          ↓reduceIte] using he'
      · have hn := coordPathPoint_active_ne v u i k (List.mem_range.mp hk)
        apply hn
        have he' := congrFun he i
        simpa only [coordPathPoint, not_lt.mpr (le_of_lt hji), ne_of_gt hji,
          ↓reduceIte] using he'.symm

/-- After the first `n` coordinate blocks, the first `n` coordinates are at their target. -/
def coordPrefixPoint (v u : Site d) (n : ℕ) : Site d :=
  fun j => if j.val < n then u j else v j

/-- The coordinate path truncated after its first `n` coordinate blocks. -/
def coordPrefix (v u : Site d) (n : ℕ) : List (Site d) :=
  v :: ((List.finRange d).take n).flatMap fun i =>
    (List.range (u i - v i).natAbs).map fun k => coordPathPoint v u i (k + 1)

/-- The last point of a completed coordinate block is its target slice. -/
lemma coordPathPoint_end (v u : Site d) (i : Fin d) :
    coordPathPoint v u i (u i - v i).natAbs = coordPrefixPoint v u (i.val + 1) := by
  funext j
  by_cases hji : j < i
  · simp only [coordPathPoint, hji, ↓reduceIte, coordPrefixPoint]
    rw [if_pos (by exact Nat.lt_succ_of_lt hji)]
  · by_cases he : j = i
    · subst j
      simp only [coordPathPoint, lt_self_iff_false, ↓reduceIte, coordPrefixPoint,
        Nat.lt_succ_self]
      have hmul := Int.sign_mul_natAbs (u i - v i)
      rw [mul_comm] at hmul
      omega
    · have hjn : ¬j.val < i.val + 1 := by
        have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
        change ¬j.val < i.val at hji
        omega
      simp only [coordPathPoint, hji, he, ↓reduceIte, coordPrefixPoint, hjn]

/-- The empty step in a coordinate block is the slice before that block. -/
lemma coordPathPoint_zero (v u : Site d) (i : Fin d) :
    coordPathPoint v u i 0 = coordPrefixPoint v u i.val := by
  funext j
  simp only [coordPathPoint, coordPrefixPoint, Nat.cast_zero, zero_mul, add_zero]
  simp only [Fin.lt_def]
  split_ifs <;> simp_all

/-- The last vertex of every coordinate prefix is the corresponding target slice. -/
lemma coordPrefix_last (v u : Site d) (n : ℕ) (hn : n ≤ d) :
    (coordPrefix v u n).getLast? = some (coordPrefixPoint v u n) := by
  induction n with
  | zero =>
    simp only [coordPrefix, List.take_zero, List.flatMap_nil, List.getLast?_singleton,
      Option.some.injEq]
    funext j
    exact (if_neg (Nat.not_lt_zero j.val)).symm
  | succ n ih =>
    have hnd : n < d := by omega
    let i : Fin d := ⟨n, hnd⟩
    have ht : (List.finRange d).take (n + 1) = (List.finRange d).take n ++ [i] := by
      have hi : (List.finRange d)[n]'(by simpa using hnd) = i := by
        apply Fin.ext
        simp only [List.getElem_finRange, Fin.val_cast]
        rfl
      rw [List.take_succ_eq_append_getElem (by simpa using hnd), hi]
    have hp : coordPrefix v u (n + 1) = coordPrefix v u n ++
        (List.range (u i - v i).natAbs).map
          (fun k => coordPathPoint v u i (k + 1)) := by
      simp only [coordPrefix, ht, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.cons_append]
    rw [hp, List.getLast?_append, List.getLast?_map, List.getLast?_range]
    by_cases hz : (u i - v i).natAbs = 0
    · simp only [hz, ↓reduceIte, Option.map_none, Option.none_or]
      rw [ih (by omega)]
      congr 1
      have he : u i = v i := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hz)
      funext j
      simp only [coordPrefixPoint]
      split_ifs with hj hj' hj'
      · rfl
      · omega
      · have hji : j = i := Fin.ext (by change j.val = n; omega)
        subst j
        exact he.symm
      · rfl
    · simp only [hz, ↓reduceIte, Option.map_some, Option.some_or]
      have hk : (u i - v i).natAbs - 1 + 1 = (u i - v i).natAbs := by omega
      rw [hk, coordPathPoint_end]

/-- The canonical return path ends at its prescribed target. -/
theorem coordPath_last (v u : Site d) : (coordPath v u).getLast? = some u := by
  have h := coordPrefix_last v u d le_rfl
  have hp : coordPrefix v u d = coordPath v u := by
    simp only [coordPrefix, coordPath,
      List.take_of_length_le (show (List.finRange d).length ≤ d by
        rw [List.length_finRange])]
  rw [hp] at h
  have he : coordPrefixPoint v u d = u := by
    funext j
    simp only [coordPrefixPoint, j.isLt, ↓reduceIte]
  exact h.trans (congrArg some he)

/-- Consecutive points within a nonempty coordinate block are nearest neighbours. -/
lemma coordPathPoint_adj (v u : Site d) (i : Fin d) (k : ℕ)
    (hs : Int.sign (u i - v i) ≠ 0) :
    (lattice d).Adj (coordPathPoint v u i k) (coordPathPoint v u i (k + 1)) := by
  have hstep : coordPathPoint v u i (k + 1) =
      coordPathPoint v u i k + Int.sign (u i - v i) • unit i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [coordPathPoint, lt_self_iff_false, ↓reduceIte, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, unit, Pi.single_eq_same, mul_one,
        Nat.cast_add, Nat.cast_one]
      ring
    · simp [coordPathPoint, unit, hji]
  rcases Int.sign_trichotomy (u i - v i) with hp | hz | hn
  · exact ⟨i, Or.inl (by simpa only [hp, one_smul] using hstep)⟩
  · exact False.elim (hs hz)
  · refine ⟨i, Or.inr ?_⟩
    rw [hstep, hn, neg_one_smul]
    exact (neg_add_cancel_right _ _).symm

/-- Each coordinate block, including its starting slice, follows nearest-neighbour edges. -/
lemma coordBlock_isChain (v u : Site d) (i : Fin d) :
    (coordPrefixPoint v u i.val ::
      (List.range (u i - v i).natAbs).map
        (fun k => coordPathPoint v u i (k + 1))).IsChain (lattice d).Adj := by
  rw [← coordPathPoint_zero v u i]
  have he : coordPathPoint v u i 0 ::
      (List.range (u i - v i).natAbs).map
        (fun k => coordPathPoint v u i (k + 1)) =
      (List.range ((u i - v i).natAbs + 1)).map (coordPathPoint v u i) := by
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def]
  rw [he, List.isChain_map, List.isChain_range_succ]
  intro k hk
  exact coordPathPoint_adj v u i k (coordPath_sign_ne_zero v u i k hk)

/-- Every prefix follows nearest-neighbour edges. -/
lemma coordPrefix_isChain (v u : Site d) (n : ℕ) (hn : n ≤ d) :
    (coordPrefix v u n).IsChain (lattice d).Adj := by
  induction n with
  | zero => simp only [coordPrefix, List.take_zero, List.flatMap_nil, List.isChain_singleton]
  | succ n ih =>
    have hnd : n < d := by omega
    let i : Fin d := ⟨n, hnd⟩
    have ht : (List.finRange d).take (n + 1) = (List.finRange d).take n ++ [i] := by
      have hi : (List.finRange d)[n]'(by simpa using hnd) = i := by
        apply Fin.ext
        simp only [List.getElem_finRange, Fin.val_cast]
        rfl
      rw [List.take_succ_eq_append_getElem (by simpa using hnd), hi]
    have hp : coordPrefix v u (n + 1) = coordPrefix v u n ++
        (List.range (u i - v i).natAbs).map
          (fun k => coordPathPoint v u i (k + 1)) := by
      simp only [coordPrefix, ht, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.cons_append]
    rw [hp]
    have hb := coordBlock_isChain v u i
    refine (ih (by omega)).append hb.tail ?_
    intro a ha b hbmem
    rw [coordPrefix_last v u n (by omega)] at ha
    have ha' : a = coordPrefixPoint v u n := (Option.mem_some_iff.mp ha).symm
    subst a
    exact hb.rel_head? hbmem

/-- Every consecutive edge of the coordinate path is a nearest-neighbour edge. -/
theorem coordPath_isChain (v u : Site d) : (coordPath v u).IsChain (lattice d).Adj := by
  simpa only [coordPrefix, coordPath,
    List.take_of_length_le (show (List.finRange d).length ≤ d by
        rw [List.length_finRange])] using
    coordPrefix_isChain v u d le_rfl

/-- Every unordered edge of a coordinate path is a nearest-neighbour edge. -/
theorem mem_pathEdges_isNNEdge (v u : Site d) (e : Sym2 (Site d))
    (he : e ∈ pathEdges (coordPath v u)) : IsNNEdge e := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp he
  have hchain := coordPath_isChain v u
  have h : ∀ L : List (Site d), L.IsChain (lattice d).Adj →
      (a, b) ∈ L.zip L.tail → (lattice d).Adj a b := by
    intro L
    induction L with
    | nil => simp only [List.zip_nil_left, List.not_mem_nil, false_implies, implies_true]
    | cons c L ih =>
      cases L with
      | nil => simp only [List.tail_cons, List.zip_nil_right, List.not_mem_nil,
          false_implies, implies_true]
      | cons f L =>
        intro hc hm
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hm
        rcases hm with hm | hm
        · cases hm
          exact hc.rel
        · exact ih hc.tail hm
  obtain ⟨i, hi | hi⟩ := h _ hchain hab
  · exact ⟨a, i, by rw [hi]⟩
  · exact ⟨b, i, by rw [hi, Sym2.eq_swap]⟩

end LongRange.Cycle
