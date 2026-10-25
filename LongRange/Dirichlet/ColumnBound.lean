import LongRange.Dirichlet.Coefficients
import LongRange.Dirichlet.Weights

/-!
# Column bounds for short defect coefficients

Counting traversals of a coordinate cycle bounds the total influence of a representative
on nearest-neighbour defects.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A coordinate path has one more vertex than its integer coordinate length. -/
theorem length_coordPath (v u : Site d) :
    (coordPath v u).length = 1 + ∑ i, (u i - v i).natAbs := by
  simp only [coordPath, List.length_cons, List.length_flatMap, List.length_map,
    List.length_range, ← Fin.sum_univ_def, Nat.add_comm]

/-- The cycle walk adds its long edge to the coordinate return path. -/
theorem length_cycleWalk (u v : Site d) :
    (Cycle.cycleWalk u v).length = 1 + ∑ i, (v i).natAbs := by
  simp only [Cycle.cycleWalk, List.length_cons, Cycle.dirEdges, List.length_zip,
    List.length_tail, length_coordPath]
  have h (i : Fin d) : u i - (u + v) i = -v i := by simp
  simp only [h, Int.natAbs_neg]
  omega

/-- Counts over a finite set cannot exceed the length of the list. -/
lemma sum_list_count_le {α : Type*} [DecidableEq α] (W : List α) (S : Finset α) :
    ∑ q ∈ S, (W.count q : ℝ) ≤ W.length := by
  have h : ∑ q ∈ S, W.count q ≤ W.length := by
    calc
      _ ≤ ∑ q ∈ S ∪ W.toFinset, W.count q :=
        Finset.sum_le_sum_of_subset (Finset.subset_union_left)
      _ = ∑ q ∈ W.toFinset, W.count q := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro q _ hq
        exact List.count_eq_zero.mpr (by simpa only [List.mem_toFinset] using hq)
      _ = _ := by
        simpa only [Multiset.coe_count, List.toFinset_coe, Multiset.coe_card] using
          Multiset.toFinset_sum_count_eq (W : Multiset α)
  exact_mod_cast h

/-- Absolute cycle coefficients sum to at most twice the walk length. -/
theorem sum_abs_cycle_le (u v : Site d) (S : Finset (Site d × Site d)) :
    ∑ q ∈ S, |(Cycle.cycle u v q.1 q.2 : ℝ)| ≤
      2 * (1 + ∑ i, ((v i).natAbs : ℝ)) := by
  classical
  have hs : ∑ q ∈ S, ((Cycle.cycleWalk u v).count q.swap : ℝ) ≤
      (Cycle.cycleWalk u v).length := by
    have h := sum_list_count_le (Cycle.cycleWalk u v) (S.image Prod.swap)
    simpa only [Finset.sum_image Prod.swap_injective.injOn, List.count,
      Bool.beq_eq_decide_eq] using h
  have ht : ∑ q ∈ S, ((Cycle.cycleWalk u v).count q : ℝ) ≤
      (Cycle.cycleWalk u v).length := by
    simpa only [List.count, Bool.beq_eq_decide_eq] using
      sum_list_count_le (Cycle.cycleWalk u v) S
  calc
    _ ≤ ∑ q ∈ S, (((Cycle.cycleWalk u v).count q.swap : ℝ) +
        ((Cycle.cycleWalk u v).count q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q _
      rcases q with ⟨a, b⟩
      have ha : 0 ≤ ((Cycle.cycleWalk u v).count (b, a) : ℝ) := Nat.cast_nonneg _
      have hb : 0 ≤ ((Cycle.cycleWalk u v).count (a, b) : ℝ) := Nat.cast_nonneg _
      have h := abs_sub ((Cycle.cycleWalk u v).count (b, a) : ℝ)
        ((Cycle.cycleWalk u v).count (a, b) : ℝ)
      rw [abs_of_nonneg ha, abs_of_nonneg hb] at h
      simpa only [Cycle.cycle, Int.cast_sub, Int.cast_natCast, Prod.swap,
        List.count, Bool.beq_eq_decide_eq] using h
    _ ≤ 2 * ((Cycle.cycleWalk u v).length : ℝ) := by
      rw [Finset.sum_add_distrib]
      calc
        _ ≤ ((Cycle.cycleWalk u v).length : ℝ) + (Cycle.cycleWalk u v).length :=
          add_le_add hs ht
        _ = _ := by ring
    _ = _ := by rw [length_cycleWalk]; push_cast; rfl

/-- Every nonzero integer displacement has positive coordinate length. -/
lemma one_le_coordinate_length (v : Site d) (hv : v ≠ 0) :
    (1 : ℝ) ≤ ∑ i, ((v i).natAbs : ℝ) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hp : 1 ≤ (v i).natAbs := Nat.one_le_iff_ne_zero.mpr
    (fun h => hi (Int.natAbs_eq_zero.mp h))
  have hpR : (1 : ℝ) ≤ (v i).natAbs := by exact_mod_cast hp
  exact hpR.trans
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg ((v j).natAbs)) (Finset.mem_univ i))

/-- A fixed displacement observes at most the full absolute cycle mass. -/
lemma sum_abs_cycle_translate_le (u v z : Site d) (S : Finset (Site d)) :
    ∑ x ∈ S, |(Cycle.cycle u v (x + z) x : ℝ)| ≤
      2 * (1 + ∑ i, ((v i).natAbs : ℝ)) := by
  classical
  let f := fun x : Site d => (x + z, x)
  have hf : Function.Injective f := fun _ _ h => congrArg Prod.snd h
  have h := sum_abs_cycle_le u v (S.image f)
  simpa only [Finset.sum_image hf.injOn, f] using h

/-- An edge indicator contributes only at the two endpoints of its representative. -/
lemma sum_abs_edge_term_le (ε : ℝ) (U : Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (r : Cycle.indexSet ε U) (z : Site d) (S : Finset (Site d)) :
    (∑ x ∈ S, |(if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
      jumpKernel (physical ε z) * linearFn ε p z else 0 : ℝ)|) ≤
      2 * cycleWeight ε p r.1.2 := by
  classical
  let W := cycleWeight ε p r.1.2
  have hW : 0 ≤ W := cycleWeight_nonneg _ _ _
  have hb (x : Site d) :
      |(if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
        jumpKernel (physical ε z) * linearFn ε p z else 0 : ℝ)| ≤
      (if x = r.1.1 then W else 0) + (if x = r.1.1 + r.1.2 then W else 0) := by
    by_cases he : r.1 = (x, z) ∨ r.1 = (x + z, -z)
    · rw [if_pos he, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
      rcases he with he | he
      · have hx := congrArg Prod.fst he
        have hz := congrArg Prod.snd he
        dsimp only [Prod.fst, Prod.snd] at hx hz
        rw [← hz, if_pos hx.symm]
        change W ≤ W + _
        split_ifs <;> linarith
      · have hx := congrArg Prod.fst he
        have hz := congrArg Prod.snd he
        dsimp only [Prod.fst, Prod.snd] at hx hz
        have hxr : x = r.1.1 + r.1.2 := by rw [hx, hz]; abel
        have hzr : z = -r.1.2 := by rw [hz, neg_neg]
        rw [hzr, physical_neg, jumpKernel_neg, linearFn_neg, abs_neg, if_pos hxr]
        change W ≤ _ + W
        split_ifs <;> linarith
    · rw [if_neg he, abs_zero]
      split_ifs <;> linarith
  calc
    _ ≤ ∑ x ∈ S, ((if x = r.1.1 then W else 0) +
        (if x = r.1.1 + r.1.2 then W else 0)) := Finset.sum_le_sum (fun x _ => hb x)
    _ ≤ 2 * W := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq']
      split_ifs <;> linarith

/-- One displacement column is controlled by its weighted coordinate length. -/
lemma sum_abs_shortCoeff_le (ε : ℝ) (U : Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (r : Cycle.indexSet ε U) (z : Site d) (S : Finset (Site d)) :
    ∑ x ∈ S, |shortCoeff ε U p x z r| ≤
      6 * (cycleWeight ε p r.1.2 * ∑ i, ((r.1.2 i).natAbs : ℝ)) := by
  classical
  let W := cycleWeight ε p r.1.2
  let L := ∑ i, ((r.1.2 i).natAbs : ℝ)
  have hW : 0 ≤ W := cycleWeight_nonneg _ _ _
  have hL : 1 ≤ L := one_le_coordinate_length _ r.2.2.1
  have hc := sum_abs_cycle_translate_le r.1.1 r.1.2 z S
  have hb := sum_abs_edge_term_le ε U p r z S
  have hpoint (x : Site d) : |shortCoeff ε U p x z r| ≤
      W * |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)| +
      |(if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
        jumpKernel (physical ε z) * linearFn ε p z else 0 : ℝ)| := by
    by_cases h : radius (physical ε r.1.2) < 1
    · rw [shortCoeff, if_pos h]
      exact (abs_sub _ _).trans_eq (by
        rw [abs_mul, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
        rfl)
    · rw [shortCoeff, if_neg h, abs_zero]
      exact add_nonneg (mul_nonneg hW (abs_nonneg _)) (abs_nonneg _)
  calc
    _ ≤ ∑ x ∈ S, (W * |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)| +
        |(if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
          jumpKernel (physical ε z) * linearFn ε p z else 0 : ℝ)|) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ ≤ W * (2 * (1 + L)) + 2 * W := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hc hW) hb
    _ ≤ _ := by nlinarith only [mul_nonneg hW (sub_nonneg.mpr hL)]

/-- The influence of one representative on all nearest-neighbour defects has a
uniform critical radial bound. -/
theorem shortCoeff_column_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ U : Set (Fin d → ℝ), ∀ hU : Bornology.IsBounded U,
      ∀ (p : Fin d → ℝ) (r : Cycle.indexSet ε U),
        ∑ x ∈ (latticeSet_finite hε.1 hU).toFinset, ∑ i : Fin d,
          (|shortCoeff ε U p x (unit i) r| + |shortCoeff ε U p x (-unit i) r|) ≤
        C * radius p / ε * (radius (physical ε r.1.2) ^ d)⁻¹ := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨12 * (d : ℝ) ^ 3, by positivity, ?_⟩
  intro ε hε U hU p r
  let S := (latticeSet_finite hε.1 hU).toFinset
  let T := cycleWeight ε p r.1.2 * ∑ i, ((r.1.2 i).natAbs : ℝ)
  have hb : T ≤ (d : ℝ) ^ 2 * radius p / ε *
      (radius (physical ε r.1.2) ^ d)⁻¹ := by
    simpa only [T, Nat.cast_sum] using
      cycleWeight_mul_path_length_le hε.1 p r.1.2 r.2.2.1
  calc
    _ = ∑ i : Fin d, ((∑ x ∈ S, |shortCoeff ε U p x (unit i) r|) +
        ∑ x ∈ S, |shortCoeff ε U p x (-unit i) r|) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib, S]
    _ ≤ ∑ _ : Fin d, (6 * T + 6 * T) := by
      apply Finset.sum_le_sum
      intro i _
      exact add_le_add (sum_abs_shortCoeff_le ε U p r (unit i) S)
        (sum_abs_shortCoeff_le ε U p r (-unit i) S)
    _ = 12 * (d : ℝ) * T := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ 12 * (d : ℝ) * ((d : ℝ) ^ 2 * radius p / ε *
        (radius (physical ε r.1.2) ^ d)⁻¹) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end

end LongRange.Dirichlet
