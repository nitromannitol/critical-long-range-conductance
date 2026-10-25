import LongRange.Corrector.Cycle
import LongRange.Preliminaries.PathCounting
import LongRange.Appendix.Kappa

/-!
# Deterministic weights of coordinate cycles

The support of a cycle on a nearest-neighbour edge is counted by the canonical
return path. Weighted sums over its translates therefore reduce to radial lattice sums.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A nonzero cycle on a nearest-neighbour edge belongs to the return path, since
unit long edges cancel identically. -/
theorem cycle_mem_pathEdges_of_ne_zero (u v x y : Site d)
    (he : IsNNEdge s(x, y)) (hc : Cycle.cycle u v x y ≠ 0) :
    s(x, y) ∈ pathEdges (coordPath (u + v) u) := by
  classical
  by_cases hv : ∃ i : Fin d, v = unit i ∨ v = -unit i
  · obtain ⟨i, hi⟩ := hv
    exact False.elim (hc (Cycle.cycle_eq_zero_of_unit u v x y i hi))
  · have hn : ∀ i : Fin d, v ≠ unit i ∧ v ≠ -unit i := by
      intro i
      exact ⟨fun h => hv ⟨i, Or.inl h⟩, fun h => hv ⟨i, Or.inr h⟩⟩
    rcases Cycle.cycle_support u v x y hc with h | h
    · exact False.elim (Cycle.long_edge_not_isNNEdge u v hn (h ▸ he))
    · exact h

/-- At fixed displacement, only finitely many cycles use a fixed nearest-neighbour
edge, and their number is at most the integer coordinate path length. -/
theorem cycle_translate_count (v x y : Site d) (he : IsNNEdge s(x, y)) :
    {u : Site d | Cycle.cycle u v x y ≠ 0}.Finite ∧
      Nat.card {u : Site d | Cycle.cycle u v x y ≠ 0} ≤ ∑ i, (v i).natAbs := by
  classical
  let S := {u : Site d | Cycle.cycle u v x y ≠ 0}
  let T := {q : Site d × Site d | q.2 - q.1 = v ∧
    s(x, y) ∈ pathEdges (coordPath q.2 q.1)}
  have hT := integer_path_counting v s(x, y)
  let f : S → T := fun u => ⟨(u.val, u.val + v),
    ⟨by change u.val + v - u.val = v; exact add_sub_cancel_left _ _,
      cycle_mem_pathEdges_of_ne_zero u.val v x y he u.property⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun q : T => q.val.1) h)
  letI : Finite T := hT.1.to_subtype
  letI : Finite S := Finite.of_injective f hf
  exact ⟨Set.toFinite S, (Nat.card_le_card_of_injective f hf).trans hT.2⟩

/-- The coordinate path length is bounded by dimension times the Euclidean radius.
This coarser dimensional constant suffices for the deterministic estimates. -/
theorem path_length_le_dimension_radius (v : Site d) :
    (∑ i, (v i).natAbs : ℝ) ≤ (d : ℝ) * radius (physical 1 v) := by
  calc
    (∑ i, (v i).natAbs : ℝ) = ∑ i, |physical 1 v i| := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [physical, one_mul, Nat.cast_natAbs, Int.cast_abs]
    _ ≤ ∑ _ : Fin d, radius (physical 1 v) :=
      Finset.sum_le_sum (fun i _ => abs_coord_le_radius _ i)
    _ = (d : ℝ) * radius (physical 1 v) := by simp only [Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The physical linear slope is bounded using Euclidean radii and a dimensional
constant, with the physical factor `ε` retained. -/
theorem abs_linearFn_le_dimension_radius (ε : ℝ) (p : Fin d → ℝ) (v : Site d) :
    |linearFn ε p v| ≤ (d : ℝ) * radius p * radius (physical ε v) := by
  calc
    |linearFn ε p v| ≤ ∑ i, |p i * physical ε v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, radius p * radius (physical ε v) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (abs_coord_le_radius p i) (abs_coord_le_radius _ i)
        (abs_nonneg _) (radius_nonneg _)
    _ = (d : ℝ) * radius p * radius (physical ε v) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_assoc]

/-- Absolute real cycle coefficients are at most one. -/
theorem abs_cycle_cast_le_one (u v x y : Site d) :
    |(Cycle.cycle u v x y : ℝ)| ≤ 1 := by
  exact_mod_cast Cycle.cycle_abs_le_one u v x y

/-- A nonnegative weight summed over translates of one displacement is bounded by
the integer path length times that weight. -/
theorem cycle_weight_fiber_bound (v x y : Site d) (he : IsNNEdge s(x, y))
    (w : ℝ) (hw : 0 ≤ w) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun u => w * |(Cycle.cycle u v x y : ℝ)| ^ k) ∧
      ∑' u, w * |(Cycle.cycle u v x y : ℝ)| ^ k ≤ w * ∑ i, (v i).natAbs := by
  classical
  obtain ⟨hfin, hcard⟩ := cycle_translate_count v x y he
  let S := hfin.toFinset
  have hs : (Function.support (fun u => w * |(Cycle.cycle u v x y : ℝ)| ^ k)).Finite := by
    apply hfin.subset
    intro u hu hc
    apply hu
    simp only [hc, Int.cast_zero, abs_zero, zero_pow (by omega : k ≠ 0), mul_zero]
  refine ⟨summable_of_hasFiniteSupport hs, ?_⟩
  rw [tsum_eq_sum (s := S) (fun u hu => ?_)]
  · calc
      ∑ u ∈ S, w * |(Cycle.cycle u v x y : ℝ)| ^ k ≤ ∑ _ ∈ S, w := by
        apply Finset.sum_le_sum
        intro u _
        exact mul_le_of_le_one_right hw
          (pow_le_one₀ (abs_nonneg _) (abs_cycle_cast_le_one u v x y))
      _ = w * (Nat.card {u : Site d | Cycle.cycle u v x y ≠ 0} : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 1
        exact_mod_cast (Set.ncard_eq_toFinset_card _ hfin).symm
      _ ≤ w * ∑ i, (v i).natAbs := mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcard) hw
  · have hc : Cycle.cycle u v x y = 0 := by
      by_contra hc
      exact hu (hfin.mem_toFinset.mpr hc)
    simp only [hc, Int.cast_zero, abs_zero, zero_pow (by omega : k ≠ 0), mul_zero]

/-- Summability of a weighted path-length majorant justifies the double cycle sum
and bounds it without assuming convergence of the desired series. -/
theorem cycle_weight_sum_bound (x y : Site d) (he : IsNNEdge s(x, y))
    (w : Site d → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (hk : 1 ≤ k)
    (hs : Summable (fun v => w v * ∑ i, (v i).natAbs)) :
    Summable (fun q : Site d × Site d => w q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ k) ∧
      ∑' q : Site d × Site d, w q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ k ≤
        ∑' v, w v * ∑ i, (v i).natAbs := by
  let f := fun q : Site d × Site d => w q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ k
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (hw q.2) (pow_nonneg (abs_nonneg _) _)
  have hb := fun v => cycle_weight_fiber_bound v x y he (w v) (hw v) k hk
  have hsf : Summable (fun v => ∑' u, f (u, v)) :=
    Summable.of_nonneg_of_le (fun v => tsum_nonneg (fun u => hf0 (u, v)))
      (fun v => (hb v).2) hs
  have hr : Summable (fun q : Site d × Site d => f (q.2, q.1)) :=
    (summable_prod_of_nonneg (fun q => hf0 (q.2, q.1))).mpr
      ⟨fun v => (hb v).1, hsf⟩
  have hf : Summable f := hr.prod_symm
  refine ⟨hf, ?_⟩
  calc
    ∑' q, f q = ∑' v, ∑' u, f (u, v) := hf.tsum_prod.trans hf.tsum_comm.symm
    _ ≤ ∑' v, w v * ∑ i, (v i).natAbs := hsf.tsum_le_tsum (fun v => (hb v).2) hs

/-- The deterministic absolute coefficient attached to a physical displacement. -/
def cycleWeight (ε : ℝ) (p : Fin d → ℝ) (v : Site d) : ℝ :=
  jumpKernel (physical ε v) * |linearFn ε p v|

/-- Cycle weights are nonnegative. -/
theorem cycleWeight_nonneg (ε : ℝ) (p : Fin d → ℝ) (v : Site d) :
    0 ≤ cycleWeight ε p v := by
  apply mul_nonneg _ (abs_nonneg _)
  unfold jumpKernel
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)

/-- Path counting and the physical slope reduce absolute short-range weights to
the critical radial power. -/
theorem cycleWeight_mul_path_length_le {ε : ℝ} (hε : 0 < ε)
    (p : Fin d → ℝ) (v : Site d) (hv : v ≠ 0) :
    cycleWeight ε p v * ∑ i, (v i).natAbs ≤
      (d : ℝ) ^ 2 * radius p / ε * (radius (physical ε v) ^ d)⁻¹ := by
  have hz : physical ε v ≠ 0 := (physical_eq_zero_iff hε v).not.mpr hv
  have hr := radius_pos hz
  have hp := radius_nonneg p
  have hL : (∑ i, (v i).natAbs : ℝ) ≤
      (d : ℝ) * radius (physical ε v) / ε := by
    rw [radius_physical_eq_mul hε.le]
    convert path_length_le_dimension_radius v using 1
    field_simp [hε.ne']
  have hJ : 0 ≤ jumpKernel (physical ε v) := by
    rw [jumpKernel_of_ne_zero hz]; positivity
  calc
    cycleWeight ε p v * ∑ i, (v i).natAbs ≤
        (jumpKernel (physical ε v) *
          ((d : ℝ) * radius p * radius (physical ε v))) *
            ((d : ℝ) * radius (physical ε v) / ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (abs_linearFn_le_dimension_radius ε p v) hJ)
        (by simpa only [Nat.cast_sum] using hL)
        (by positivity) (by positivity)
    _ = (d : ℝ) ^ 2 * radius p / ε *
        (jumpKernel (physical ε v) * radius (physical ε v) ^ 2) := by ring
    _ = _ := by rw [LatticeSums.kernel_mul_radius_sq hz,
      Real.rpow_neg hr.le, Real.rpow_natCast]

/-- Squared weights have a supercritical radial majorant. The extra factor of
the lattice radius is harmless since a nonzero integer vector has radius at least one. -/
theorem cycleWeight_sq_mul_path_length_le {ε : ℝ} (hε : 0 < ε)
    (p : Fin d → ℝ) (v : Site d) (hv : v ≠ 0) :
    cycleWeight ε p v ^ 2 * ∑ i, (v i).natAbs ≤
      (d : ℝ) ^ 3 * radius p ^ 2 / ε ^ 2 *
        (radius (physical ε v) ^ (2 * d))⁻¹ := by
  have hz : physical ε v ≠ 0 := (physical_eq_zero_iff hε v).not.mpr hv
  have hr := radius_pos hz
  have hp := radius_nonneg p
  have hL : (∑ i, (v i).natAbs : ℝ) ≤
      (d : ℝ) * (radius (physical ε v) / ε) ^ 2 := by
    rw [radius_physical_eq_mul hε.le, mul_div_cancel_left₀ _ hε.ne']
    exact (path_length_le_dimension_radius v).trans
      (mul_le_mul_of_nonneg_left (by
        have h := lattice_radius_ge_one hv
        nlinarith only [h, sq_nonneg (radius (physical 1 v) - 1)])
        (Nat.cast_nonneg d))
  have hJ : 0 ≤ jumpKernel (physical ε v) := by
    rw [jumpKernel_of_ne_zero hz]; positivity
  have hw : cycleWeight ε p v ≤ jumpKernel (physical ε v) *
      ((d : ℝ) * radius p * radius (physical ε v)) :=
    mul_le_mul_of_nonneg_left (abs_linearFn_le_dimension_radius ε p v) hJ
  calc
    cycleWeight ε p v ^ 2 * ∑ i, (v i).natAbs ≤
        (jumpKernel (physical ε v) *
          ((d : ℝ) * radius p * radius (physical ε v))) ^ 2 *
            ((d : ℝ) * (radius (physical ε v) / ε) ^ 2) :=
      mul_le_mul ((sq_le_sq₀ (cycleWeight_nonneg ε p v) (by positivity)).mpr hw)
        (by simpa only [Nat.cast_sum] using hL) (by positivity) (sq_nonneg _)
    _ = _ := by
      rw [jumpKernel_of_ne_zero hz, pow_add,
        show 2 * d = d * 2 by omega, pow_mul]
      field_simp [hr.ne', hε.ne']

/-- A supercritical radial power is summable on the entire punctured lattice,
with its exact scaling factor. -/
theorem punctured_radial_sum_bound (hd : 1 ≤ d) (n : ℕ) (hn : d < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      Summable (fun v : Site d => if v = 0 then 0
        else (radius (physical ε v) ^ n)⁻¹) ∧
      ε ^ n * ∑' v : Site d, (if v = 0 then 0
        else (radius (physical ε v) ^ n)⁻¹) ≤ C := by
  classical
  let C := Euclidean.Shell.shellConstant d *
    ((1 + 1 / ((n : ℝ) - d)) * (4 : ℝ) ^ ((n : ℝ) - d))
  have hnd : (d : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < (n : ℝ) - d := sub_pos.mpr hnd
  have hC : 0 < C := mul_pos (Euclidean.Shell.shellConstant_pos hd)
    (mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num) _))
  let g := fun v : Site d => if v = 0 then (0 : ℝ)
    else (radius (physical 1 v) ^ n)⁻¹
  have heq (v : Site d) : g v = (if 1 ≤ radius (physical 1 v) then
      radius (physical 1 v) ^ (-(n : ℝ)) else 0) := by
    by_cases hv : v = 0
    · subst v
      simp [g, radius, physical]
    · rw [if_pos (lattice_radius_ge_one hv), Real.rpow_neg (radius_nonneg _),
        Real.rpow_natCast]
      exact if_neg hv
  have hb (s : Finset (Site d)) : ∑ v ∈ s, g v ≤ C := by
    simp_rw [heq]
    have h := Euclidean.Estimates.exterior_finset_le hd hnd
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1 / 1) s
    simpa only [Real.one_rpow, one_div_one, mul_one, one_mul] using h
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
  have hg : Summable g := summable_of_sum_le hg0 hb
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have hscale (v : Site d) : (if v = 0 then (0 : ℝ)
      else (radius (physical ε v) ^ n)⁻¹) = (ε ^ n)⁻¹ * g v := by
    by_cases hv : v = 0
    · simp [hv, g]
    · simp only [hv, if_false, g, radius_physical_eq_mul hε.le, mul_pow, mul_inv]
  simp_rw [hscale]
  refine ⟨hg.mul_left _, ?_⟩
  rw [tsum_mul_left, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]
  exact hg.tsum_le_of_sum_le hb

/-- A radial majorant of the path-length weights controls the full double sum. -/
theorem cycle_weight_sum_le_majorant (x y : Site d) (he : IsNNEdge s(x, y))
    (w g : Site d → ℝ) (hw : ∀ v, 0 ≤ w v) (k : ℕ) (hk : 1 ≤ k)
    (hg : Summable g) (hbound : ∀ v, w v * ∑ i, (v i).natAbs ≤ g v) :
    Summable (fun q : Site d × Site d => w q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ k) ∧
      ∑' q : Site d × Site d, w q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ k ≤ ∑' v, g v := by
  have hn : ∀ v, 0 ≤ w v * ∑ i, (v i).natAbs :=
    fun v => mul_nonneg (hw v) (by positivity)
  have hs := Summable.of_nonneg_of_le hn hbound hg
  obtain ⟨hf, hb⟩ := cycle_weight_sum_bound x y he w hw k hk hs
  exact ⟨hf, hb.trans (hs.tsum_le_tsum hbound hg)⟩

/-- Radial square-sum reduction for an arbitrary displacement restriction. -/
theorem cycle_weight_sq_sum_le {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ)
    (x y : Site d) (he : IsNNEdge s(x, y)) (P : Site d → Prop)
    [DecidablePred P]
    (hs : Summable (fun v : Site d => if v ≠ 0 ∧ P v then
      (radius (physical ε v) ^ (2 * d))⁻¹ else 0)) :
    Summable (fun q : Site d × Site d => if q.2 ≠ 0 ∧ P q.2 then
      (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) ∧
      ∑' q : Site d × Site d, (if q.2 ≠ 0 ∧ P q.2 then
        (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) ≤
          (d : ℝ) ^ 3 * radius p ^ 2 / ε ^ 2 *
            ∑' v : Site d, (if v ≠ 0 ∧ P v then
              (radius (physical ε v) ^ (2 * d))⁻¹ else 0) := by
  classical
  let K := (d : ℝ) ^ 3 * radius p ^ 2 / ε ^ 2
  have hb := cycle_weight_sum_le_majorant x y he
    (fun v => if v ≠ 0 ∧ P v then cycleWeight ε p v ^ 2 else 0)
    (fun v => K * (if v ≠ 0 ∧ P v then
      (radius (physical ε v) ^ (2 * d))⁻¹ else 0))
    (by intro v; split_ifs <;> positivity) 2 (by norm_num) (hs.mul_left K)
    (by
      intro v
      by_cases hv : v ≠ 0 ∧ P v
      · simp only [if_pos hv]
        exact cycleWeight_sq_mul_path_length_le hε p v hv.1
      · simp only [if_neg hv, zero_mul, mul_zero, le_refl])
  have heq (q : Site d × Site d) :
      (if q.2 ≠ 0 ∧ P q.2 then cycleWeight ε p q.2 ^ 2 else 0) *
          |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ 2 =
        (if q.2 ≠ 0 ∧ P q.2 then
          (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) := by
    split_ifs <;> simp only [mul_pow, zero_mul]
  simpa only [heq, tsum_mul_left] using hb

/-- The all-scale square sum has the deterministic scaling in Proposition 3.3.
The constant is chosen before the scale, slope, or observed edge. -/
theorem cycle_weight_sq_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (p : Fin d → ℝ) (x y : Site d), IsNNEdge s(x, y) →
        Summable (fun q : Site d × Site d => if q.2 ≠ 0 then
          (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) ∧
        ∑' q : Site d × Site d, (if q.2 ≠ 0 then
          (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) ≤
            C * radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)) := by
  classical
  obtain ⟨A, hA, ha⟩ := punctured_radial_sum_bound hd (2 * d) (by omega)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨(d : ℝ) ^ 3 * A, mul_pos (pow_pos hd0 _) hA, ?_⟩
  intro ε hε p x y he
  obtain ⟨hs, hb⟩ := ha ε hε.1
  have heq (v : Site d) : (if v ≠ 0 then
      (radius (physical ε v) ^ (2 * d))⁻¹ else (0 : ℝ)) =
        (if v = 0 then 0 else (radius (physical ε v) ^ (2 * d))⁻¹) := by
    by_cases hv : v = 0 <;> simp only [hv, ne_eq, not_true_eq_false,
      if_false, if_true, not_false_eq_true]
  have hsum := cycle_weight_sq_sum_le hε.1 p x y he (fun _ => True)
    (by simpa only [and_true, heq] using hs)
  simp only [and_true, heq] at hsum
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  calc
    _ ≤ (d : ℝ) ^ 3 * radius p ^ 2 / ε ^ 2 * (A / ε ^ (2 * d)) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos hε.1 _)).mpr
        (by simpa only [mul_comm] using hb))
        (by positivity)
    _ = _ := by
      rw [show 2 * (d : ℝ) + 2 = ((2 * d + 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hε.1.le, Real.rpow_natCast, pow_add, mul_inv]
      ring

/-- The exterior square sum has the long-range scaling in Proposition 3.3. -/
theorem cycle_weight_sq_tail_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (p : Fin d → ℝ) (x y : Site d), IsNNEdge s(x, y) →
        Summable (fun q : Site d × Site d => if q.2 ≠ 0 ∧
          1 ≤ radius (physical ε q.2) then
            (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) ∧
        ∑' q : Site d × Site d, (if q.2 ≠ 0 ∧ 1 ≤ radius (physical ε q.2) then
          (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)|) ^ 2 else 0) ≤
            C * radius p ^ 2 * ε ^ (-((d : ℝ) + 2)) := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨A, hA, ha⟩ := (lattice_sums d).1 (2 * d) (by positivity)
  refine ⟨(d : ℝ) ^ 3 * A, mul_pos (pow_pos hd0 _) hA, ?_⟩
  intro ε hε p x y he
  obtain ⟨hs, hb⟩ := (ha ε hε).2 (by linarith)
  have heq (v : Site d) : (if v ≠ 0 ∧ 1 ≤ radius (physical ε v) then
      (radius (physical ε v) ^ (2 * d))⁻¹ else (0 : ℝ)) =
        (if 1 ≤ radius (physical ε v) then
          1 / radius (physical ε v) ^ (2 * (d : ℝ)) else 0) := by
    by_cases hv : v = 0
    · subst v
      simp [radius, physical]
    · simp only [hv, ne_eq, not_false_eq_true, true_and, one_div,
        show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_natCast]
  have hsum := cycle_weight_sq_sum_le hε.1 p x y he
    (fun v => 1 ≤ radius (physical ε v)) (by simpa only [heq] using hs)
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  simp_rw [heq]
  calc
    _ ≤ (d : ℝ) ^ 3 * radius p ^ 2 / ε ^ 2 * (A / ε ^ d) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ (pow_pos hε.1 _)).mpr
        (by simpa only [mul_comm] using hb))
        (by positivity)
    _ = _ := by
      rw [show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_neg hε.1.le, Real.rpow_natCast, pow_add, mul_inv]
      ring

/-- The absolute short-range sum is bounded by the critical normalization,
including the additive constant in its logarithmic growth. -/
theorem cycle_weight_short_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (p : Fin d → ℝ) (x y : Site d), IsNNEdge s(x, y) →
        Summable (fun q : Site d × Site d => if ε ≤ radius (physical ε q.2) ∧
          radius (physical ε q.2) < 1 then
            cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| else 0) ∧
        ∑' q : Site d × Site d, (if ε ≤ radius (physical ε q.2) ∧
          radius (physical ε q.2) < 1 then
            cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| else 0) ≤
          C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|) := by
  classical
  obtain ⟨A, hA, ha⟩ := kappa_le d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨(d : ℝ) ^ 2 * A, mul_pos (pow_pos hd0 _) hA, ?_⟩
  intro ε hε p x y he
  have hp := radius_nonneg p
  let K := (d : ℝ) ^ 2 * radius p / ε
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (sq_nonneg _) hp) hε.1.le
  let w := fun v : Site d => if ε ≤ radius (physical ε v) ∧
    radius (physical ε v) < 1 then cycleWeight ε p v else 0
  let g := fun v : Site d => if v ∈ unitBallIndices d ε then
    K * (radius (physical ε v) ^ d)⁻¹ else 0
  have hg : Summable g := by
    have hsupp : (Function.support g).Finite := by
      apply (unitBallIndices d ε).finite_toSet.subset
      intro v hv
      by_contra hn
      exact hv (if_neg hn)
    exact summable_of_hasFiniteSupport hsupp
  have hb (v : Site d) : w v * ∑ i, (v i).natAbs ≤ g v := by
    dsimp [w, g]
    by_cases hv : ε ≤ radius (physical ε v) ∧ radius (physical ε v) < 1
    · have hv0 : v ≠ 0 := by
        intro h
        have hpos := hε.1.trans_le hv.1
        simp [h, physical, radius] at hpos
      have hm : v ∈ unitBallIndices d ε :=
        (mem_unitBallIndices hε.1 v).mpr ⟨hv0, hv.2.le⟩
      rw [if_pos hv, if_pos hm]
      exact cycleWeight_mul_path_length_le hε.1 p v hv0
    · rw [if_neg hv, zero_mul]
      split_ifs
      · exact mul_nonneg hK (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))
      · exact le_rfl
  have hw : ∀ v, 0 ≤ w v := by
    intro v
    dsimp [w]
    split_ifs
    · exact cycleWeight_nonneg ε p v
    · exact le_rfl
  obtain ⟨hs, hsum⟩ := cycle_weight_sum_le_majorant x y he w g hw 1 (by omega) hg hb
  have heq (q : Site d × Site d) : w q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| ^ 1 =
      (if ε ≤ radius (physical ε q.2) ∧ radius (physical ε q.2) < 1 then
        cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 x y : ℝ)| else 0) := by
    dsimp [w]
    split_ifs <;> simp only [pow_one, zero_mul]
  simp only [heq] at hs hsum
  refine ⟨hs, hsum.trans ?_⟩
  have hg_sum : ∑' v, g v = K * (kappa d ε / ε ^ d) := by
    rw [tsum_eq_sum (s := unitBallIndices d ε) (fun v hv => if_neg hv)]
    simp only [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum, kappa]
    congr 1
    field_simp [hε.1.ne']
  rw [hg_sum]
  calc
    K * (kappa d ε / ε ^ d) ≤ K * (A * (1 + |Real.log ε|) / ε ^ d) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (ha ε hε) (pow_nonneg hε.1.le _))
        hK
    _ = _ := by
      rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_neg hε.1.le, Real.rpow_natCast, pow_succ ε d, mul_inv]
      dsimp [K]
      ring

end

end LongRange
