import LongRange.Corrector.Cycle
import LongRange.Appendix.LatticeCount
import LongRange.Calculus.Green

/-!
# Absolute convergence of comparison-field coefficients

The finite set of starting vertices and the Euclidean first moment of the jump kernel
control the representative series uniformly in the observation edge.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The kernel multiplied by a physical linear slope is absolutely summable. -/
theorem summable_kernel_linear (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (p : Fin d → ℝ) :
    Summable (fun v : Site d => |jumpKernel (physical ε v) * linearFn ε p v|) := by
  refine ((summable_jumpKernel_firstMoment hd hε).mul_left (∑ i, |p i|)).of_norm_bounded
    (fun v => ?_)
  rw [Real.norm_eq_abs, abs_abs, abs_mul,
    abs_of_nonneg (jumpKernel_nonneg _)]
  calc
    _ ≤ jumpKernel (physical ε v) * ((∑ i, |p i|) * radius (physical ε v)) :=
      mul_le_mul_of_nonneg_left (abs_linearFn_le ε p v) (jumpKernel_nonneg _)
    _ = _ := by ring

/-- Bounded conductances give an absolutely summable series of representative weights. -/
theorem summable_representative_weight (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} {A : ℝ} (ha : ∀ e, |a e| ≤ A) (m : ℝ) (p : Fin d → ℝ) :
    Summable (fun r : Cycle.indexSet ε U =>
      |(a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
        jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2|) := by
  classical
  letI : Fintype (latticeSet ε U) := (latticeSet_finite hε hU).fintype
  have hA : 0 ≤ A := (abs_nonneg (a (baseEdge hd))).trans (ha _)
  have hs : Summable (fun q : (latticeSet ε U) × Site d =>
      (A + |m|) * |jumpKernel (physical ε q.2) * linearFn ε p q.2|) := by
    refine (summable_prod_of_nonneg (fun q =>
      mul_nonneg (add_nonneg hA (abs_nonneg _)) (abs_nonneg _))).mpr ?_
    exact ⟨fun _ => (summable_kernel_linear hd hε p).mul_left _,
      summable_of_hasFiniteSupport (Set.toFinite _)⟩
  let f : Cycle.indexSet ε U → (latticeSet ε U) × Site d :=
    fun r => (⟨r.1.1, r.2.1⟩, r.1.2)
  have hf : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun q => q.1.1) h)
      (congrArg (fun q : (latticeSet ε U) × Site d => q.2) h)
  refine (hs.comp_injective hf).of_norm_bounded (fun r => ?_)
  change ‖|(a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
    jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2|‖ ≤ _
  rw [Real.norm_eq_abs, abs_abs, mul_assoc, abs_mul]
  exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add (ha _) le_rfl))
    (abs_nonneg _)

/-- Each comparison-field correction series converges absolutely. -/
theorem summable_field_correction (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} {A : ℝ} (ha : ∀ e, |a e| ≤ A)
    (m : ℝ) (p : Fin d → ℝ) (y x : Site d) :
    Summable (fun r : Cycle.indexSet ε U =>
      |(a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
        jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
          (Cycle.cycle r.1.1 r.1.2 y x : ℝ)|) := by
  refine (summable_representative_weight hd hε hU ha m p).of_norm_bounded (fun r => ?_)
  rw [Real.norm_eq_abs, abs_abs, abs_mul]
  have hc : |(Cycle.cycle r.1.1 r.1.2 y x : ℝ)| ≤ 1 := by
    exact_mod_cast Cycle.cycle_abs_le_one r.1.1 r.1.2 y x
  exact mul_le_of_le_one_right (abs_nonneg _) hc

/-- Summing directed traversal multiplicities over the target counts sources. -/
lemma hasSum_walk_count (W : List (Site d × Site d)) (x : Site d) :
    HasSum (fun y => (W.count (x, y) : ℝ)) ((W.map Prod.fst).count x : ℝ) := by
  classical
  induction W with
  | nil => simpa only [List.count_nil, List.map_nil, Nat.cast_zero] using hasSum_zero
  | cons q W ih =>
    rcases q with ⟨a, b⟩
    by_cases ha : a = x
    · subst a
      convert ih.add (hasSum_ite_eq b (1 : ℝ)) using 1
      · funext y
        by_cases hy : y = b
        · subst y
          simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one]
          rfl
        · have hp : (x, b) ≠ (x, y) := fun h => hy (congrArg Prod.snd h).symm
          simp only [List.count_cons_of_ne hp, if_neg hy, add_zero]
      · simp only [List.map_cons, List.count_cons_self, Nat.cast_add, Nat.cast_one]
    · have hp (y : Site d) : (a, b) ≠ (x, y) := fun h => ha (congrArg Prod.fst h)
      simpa only [List.map_cons, List.count_cons_of_ne ha,
        List.count_cons_of_ne (hp _)] using ih

/-- The absolute cycle flow at each vertex is summable with total mass at most two. -/
lemma cycle_column_abs_tsum_le_two (u v x : Site d) :
    Summable (fun y => |(Cycle.cycle u v y x : ℝ)|) ∧
      ∑' y, |(Cycle.cycle u v y x : ℝ)| ≤ 2 := by
  classical
  have hf := hasSum_walk_count (Cycle.cycleWalk u v) x
  have hs := hasSum_walk_count ((Cycle.cycleWalk u v).map Prod.swap) x
  have hswap (y : Site d) :
      ((Cycle.cycleWalk u v).map Prod.swap).count (x, y) =
        (Cycle.cycleWalk u v).count (y, x) := by
    exact List.count_map_of_injective _ Prod.swap Prod.swap_injective (y, x)
  have hs' : HasSum (fun y => ((Cycle.cycleWalk u v).count (y, x) : ℝ))
      (((Cycle.cycleWalk u v).map Prod.snd).count x : ℝ) := by
    simpa only [hswap, List.map_map, Function.comp_def, Prod.fst_swap] using hs
  have hbound (y : Site d) : |(Cycle.cycle u v y x : ℝ)| ≤
      ((Cycle.cycleWalk u v).count (x, y) : ℝ) +
        ((Cycle.cycleWalk u v).count (y, x) : ℝ) := by
    simpa only [Cycle.cycle, Int.cast_sub, Int.cast_natCast,
      Nat.abs_cast] using
      (abs_sub ((Cycle.cycleWalk u v).count (x, y) : ℝ)
        ((Cycle.cycleWalk u v).count (y, x) : ℝ))
  have habs : Summable (fun y => |(Cycle.cycle u v y x : ℝ)|) :=
    (hf.summable.add hs'.summable).of_nonneg_of_le (fun _ => abs_nonneg _) hbound
  refine ⟨habs, ?_⟩
  calc
    _ ≤ ∑' y, (((Cycle.cycleWalk u v).count (x, y) : ℝ) +
        ((Cycle.cycleWalk u v).count (y, x) : ℝ)) :=
      habs.tsum_le_tsum hbound (hf.summable.add hs'.summable)
    _ = 2 * (((Cycle.cycleWalk u v).map Prod.fst).count x : ℝ) := by
      rw [(hf.add hs').tsum_eq, Cycle.cycleWalk_count_fst_eq_snd]
      ring
    _ ≤ 2 := by
      have hn := List.nodup_iff_count_le_one.mp (Cycle.cycleWalk_fst_nodup u v) x
      have hn' : (((Cycle.cycleWalk u v).map Prod.fst).count x : ℝ) ≤ 1 := by
        exact_mod_cast hn
      linarith

/-- The correction is jointly absolutely summable in representative and observation vertex. -/
theorem summable_field_correction_prod (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} {A : ℝ} (ha : ∀ e, |a e| ≤ A)
    (m : ℝ) (p : Fin d → ℝ) (x : Site d) :
    Summable (fun q : Cycle.indexSet ε U × Site d =>
      |(a (edgeAdd q.1.1.1 q.1.1.2 q.1.2.2.1) - m) *
        jumpKernel (physical ε q.1.1.2) * linearFn ε p q.1.1.2 *
          (Cycle.cycle q.1.1.1 q.1.1.2 q.2 x : ℝ)|) := by
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  constructor
  · intro r
    simpa only [abs_mul] using
      (cycle_column_abs_tsum_le_two r.1.1 r.1.2 x).1.mul_left
        |(a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
          jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2|
  · refine ((summable_representative_weight hd hε hU ha m p).mul_right 2).of_nonneg_of_le
      (fun r => tsum_nonneg (fun _ => abs_nonneg _)) (fun r => ?_)
    let c := (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
      jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2
    change (∑' y : Site d, |c * (Cycle.cycle r.1.1 r.1.2 y x : ℝ)|) ≤ |c| * 2
    simp only [abs_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (cycle_column_abs_tsum_le_two r.1.1 r.1.2 x).2
      (abs_nonneg c)

end

end LongRange.Dirichlet
