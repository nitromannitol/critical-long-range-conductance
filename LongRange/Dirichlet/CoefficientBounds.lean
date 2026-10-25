import LongRange.Dirichlet.Coefficients
import LongRange.Dirichlet.Weights

/-!
# Size bounds for flux-defect coefficients

Cycle-weight estimates control the coefficients on nearest-neighbour observation edges.
All radii in these estimates are Euclidean.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Either coordinate orientation gives a nearest-neighbour observation edge. -/
lemma isNNEdge_add_unit (x z : Site d) (i : Fin d)
    (hz : z = unit i ∨ z = -unit i) : IsNNEdge s(x + z, x) := by
  rcases hz with rfl | rfl
  · exact ⟨x, i, Sym2.eq_swap⟩
  · refine ⟨x - unit i, i, ?_⟩
    simp only [sub_eq_add_neg, neg_add_cancel_right]

/-- A coordinate unit displacement has physical radius equal to the scale. -/
lemma radius_physical_unit_orientation {ε : ℝ} (hε : 0 ≤ ε) (z : Site d)
    (i : Fin d) (hz : z = unit i ∨ z = -unit i) :
    radius (physical ε z) = ε := by
  rw [radius_physical_eq_mul hε]
  have hr : radius (physical 1 z) = 1 := by
    rcases hz with rfl | rfl <;> simp [radius, physical, unit, Pi.single_apply]
  rw [hr, mul_one]

/-- Absolute cycle coefficients agree with the nonnegative cycle-weight summand. -/
lemma abs_cycle_coefficient (ε : ℝ) (p : Fin d → ℝ) (u v x y : Site d) :
    |jumpKernel (physical ε v) * linearFn ε p v * (Cycle.cycle u v x y : ℝ)| =
      cycleWeight ε p v * |(Cycle.cycle u v x y : ℝ)| := by
  have hJ : 0 ≤ jumpKernel (physical ε v) := by
    unfold jumpKernel
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
  rw [abs_mul, abs_mul, abs_of_nonneg hJ]
  rfl

/-- On a long representative the edge-supported subtraction vanishes. -/
lemma longCoeff_eq_cycle {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (U : Set (Fin d → ℝ)) (p : Fin d → ℝ) (x z : Site d) (i : Fin d)
    (hz : z = unit i ∨ z = -unit i) (r : Cycle.indexSet ε U) :
    longCoeff ε U p x z r = if 1 ≤ radius (physical ε r.1.2) then
      jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
        (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ) else 0 := by
  classical
  unfold longCoeff
  split_ifs with hr
  · have hn : ¬(r.1 = (x, z) ∨ r.1 = (x + z, -z)) := by
      rintro (he | he)
      · have hv := congrArg Prod.snd he
        rw [hv, radius_physical_unit_orientation hε.1.le z i hz] at hr
        exact (not_le.mpr hε.2) hr
      · have hv := congrArg Prod.snd he
        have hnz : -z = unit i ∨ -z = -unit i := by
          rcases hz with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (neg_neg _)
        rw [hv, radius_physical_unit_orientation hε.1.le (-z) i hnz] at hr
        exact (not_le.mpr hε.2) hr
    simp only [defectCoeff, if_neg hn, sub_zero]
  · rfl

/-- Long coefficients inherit the exterior cycle square-sum bound, including summability. -/
theorem longCoeff_sq_sum_bound_with_summable (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ (p : Fin d → ℝ) (x z : Site d) (i : Fin d),
      (z = unit i ∨ z = -unit i) →
      Summable (fun r => longCoeff ε U p x z r ^ 2) ∧
      ∑' r, longCoeff ε U p x z r ^ 2 ≤
        C * radius p ^ 2 * ε ^ (-((d : ℝ) + 2)) := by
  classical
  obtain ⟨C, hC, hb⟩ := cycle_weight_sq_tail_sum_bound hd
  refine ⟨C, hC, ?_⟩
  intro ε hε U _ p x z i hz
  obtain ⟨hs, ht⟩ := hb ε hε p (x + z) x (isNNEdge_add_unit x z i hz)
  let f := fun q : Site d × Site d => if q.2 ≠ 0 ∧
    1 ≤ radius (physical ε q.2) then
      (cycleWeight ε p q.2 * |(Cycle.cycle q.1 q.2 (x + z) x : ℝ)|) ^ 2 else 0
  have he (r : Cycle.indexSet ε U) : longCoeff ε U p x z r ^ 2 = f r.1 := by
    rw [longCoeff_eq_cycle hε U p x z i hz r]
    dsimp only [f]
    simp only [r.2.2.1, ne_eq, not_false_eq_true, true_and]
    split_ifs
    · rw [← abs_cycle_coefficient, sq_abs]
    · norm_num
  have hs' : Summable (fun r : Cycle.indexSet ε U => longCoeff ε U p x z r ^ 2) := by
    have hsub : Summable (fun r : Cycle.indexSet ε U => f r.1) :=
      hs.subtype (Cycle.indexSet ε U)
    exact hsub.congr (fun r => (he r).symm)
  refine ⟨hs', ?_⟩
  simp_rw [he]
  exact (Summable.tsum_subtype_le f (Cycle.indexSet ε U)
    (by intro q; dsimp [f]; split_ifs <;> positivity) hs).trans ht

/-- The exterior coefficient square sum has the long-range scaling. -/
theorem longCoeff_sq_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ (p : Fin d → ℝ) (x z : Site d) (i : Fin d),
      (z = unit i ∨ z = -unit i) →
      ∑' r, longCoeff ε U p x z r ^ 2 ≤
        C * radius p ^ 2 * ε ^ (-((d : ℝ) + 2)) := by
  obtain ⟨C, hC, hb⟩ := longCoeff_sq_sum_bound_with_summable hd
  exact ⟨C, hC, fun ε hε U hU p x z i hz => (hb ε hε U hU p x z i hz).2⟩

/-- A constant supported on two edge orientations has mass at most twice its size. -/
lemma edge_indicator_tsum_le (ε : ℝ) (U : Set (Fin d → ℝ)) (x z : Site d)
    (b : ℝ) (hb : 0 ≤ b) :
    ∑' r : Cycle.indexSet ε U,
      (if r.1 = (x, z) ∨ r.1 = (x + z, -z) then b else 0) ≤ 2 * b := by
  classical
  let f := fun q : Site d × Site d => if q = (x, z) ∨ q = (x + z, -z)
    then b else 0
  have hs : Summable f := summable_of_hasFiniteSupport (by
    apply ((Set.finite_singleton (x + z, -z)).insert (x, z)).subset
    intro q hq
    by_contra hn
    apply hq
    exact if_neg (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hn))
  have hsum : ∑' q, f q ≤ 2 * b := by
    rw [tsum_eq_sum (s := {(x, z), (x + z, -z)}) (by
      intro q hq
      exact if_neg (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hq))]
    by_cases he : (x, z) = (x + z, -z)
    · simp only [he, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
        Finset.sum_singleton, f, or_self, if_true]
      linarith
    · rw [Finset.sum_pair he]
      simp only [f, true_or, or_true, if_true]
      ring_nf
      exact le_rfl
  exact (Summable.tsum_subtype_le f (Cycle.indexSet ε U)
    (by intro q; dsimp [f]; split_ifs <;> positivity) hs).trans hsum

/-- The physical slope on either coordinate orientation is bounded by the Euclidean slope. -/
lemma abs_linearFn_unit_le {ε : ℝ} (hε : 0 ≤ ε) (p : Fin d → ℝ)
    (z : Site d) (i : Fin d) (hz : z = unit i ∨ z = -unit i) :
    |linearFn ε p z| ≤ ε * radius p := by
  have he : |linearFn ε p z| = ε * |p i| := by
    rcases hz with rfl | rfl <;>
      simp [linearFn, physical, unit, Pi.single_apply, Finset.sum_ite_eq',
        mul_comm, abs_mul, abs_of_nonneg hε]
  rw [he]
  exact mul_le_mul_of_nonneg_left (abs_coord_le_radius p i) hε

/-- The nearest-neighbour self coefficient has its exact physical scaling bound. -/
lemma abs_self_coefficient_le {ε : ℝ} (hε : 0 < ε) (p : Fin d → ℝ)
    (z : Site d) (i : Fin d) (hz : z = unit i ∨ z = -unit i) :
    |jumpKernel (physical ε z) * linearFn ε p z| ≤
      radius p * ε ^ (-((d : ℝ) + 1)) := by
  have hr := radius_physical_unit_orientation hε.le z i hz
  have hz0 : physical ε z ≠ 0 := by
    intro he
    have hh : radius (physical ε z) = 0 := by simp [he, radius]
    linarith
  rw [abs_mul, jumpKernel_of_ne_zero hz0, hr,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _))]
  calc
    _ ≤ (ε ^ (d + 2))⁻¹ * (ε * radius p) :=
      mul_le_mul_of_nonneg_left (abs_linearFn_unit_le hε.le p z i hz)
        (inv_nonneg.mpr (pow_nonneg hε.le _))
    _ = _ := by
      rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by push_cast; rfl,
        Real.rpow_neg hε.le, Real.rpow_natCast]
      rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
      field_simp [hε.ne']

/-- Restricting the short cycle sum to representatives preserves its absolute bound. -/
lemma short_cycle_sum_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ (U : Set (Fin d → ℝ)) (p : Fin d → ℝ) (x z : Site d) (i : Fin d),
      (z = unit i ∨ z = -unit i) →
      Summable (fun r : Cycle.indexSet ε U =>
        if radius (physical ε r.1.2) < 1 then
          cycleWeight ε p r.1.2 * |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)| else 0) ∧
      ∑' r : Cycle.indexSet ε U, (if radius (physical ε r.1.2) < 1 then
        cycleWeight ε p r.1.2 * |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)| else 0) ≤
          C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|) := by
  classical
  obtain ⟨C, hC, hb⟩ := cycle_weight_short_sum_bound hd
  refine ⟨C, hC, ?_⟩
  intro ε hε U p x z i hz
  obtain ⟨hs, ht⟩ := hb ε hε p (x + z) x (isNNEdge_add_unit x z i hz)
  have hr (r : Cycle.indexSet ε U) : ε ≤ radius (physical ε r.1.2) := by
    rw [radius_physical_eq_mul hε.1.le]
    exact le_mul_of_one_le_right hε.1.le (lattice_radius_ge_one r.2.2.1)
  have hs' := hs.subtype (Cycle.indexSet ε U)
  simp only [Function.comp_def, hr, true_and] at hs'
  refine ⟨hs', ?_⟩
  have ht' := Summable.tsum_subtype_le _ (Cycle.indexSet ε U)
    (by
      intro q
      split_ifs
      · exact mul_nonneg (cycleWeight_nonneg _ _ _) (abs_nonneg _)
      · exact le_rfl) hs
  simp only [hr, true_and] at ht'
  exact ht'.trans ht

/-- The short coefficient has critical growth with the corrected logarithmic factor. -/
theorem shortCoeff_abs_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ (p : Fin d → ℝ) (x z : Site d) (i : Fin d),
      (z = unit i ∨ z = -unit i) →
      ∑' r, |shortCoeff ε U p x z r| ≤
        C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|) := by
  classical
  obtain ⟨C, hC, hb⟩ := short_cycle_sum_le hd
  refine ⟨C + 2, by linarith, ?_⟩
  intro ε hε U hU p x z i hz
  obtain ⟨hs, ht⟩ := hb ε hε U p x z i hz
  let A := fun r : Cycle.indexSet ε U => if radius (physical ε r.1.2) < 1 then
    cycleWeight ε p r.1.2 * |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)| else 0
  let B := fun r : Cycle.indexSet ε U =>
    if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
      |jumpKernel (physical ε z) * linearFn ε p z| else 0
  have hsB : Summable B := summable_edge_indicator ε U x z _
  have hpoint (r : Cycle.indexSet ε U) : |shortCoeff ε U p x z r| ≤ A r + B r := by
    dsimp only [shortCoeff, A, B]
    split_ifs with hr he he
    · simpa only [defectCoeff, if_pos he, abs_cycle_coefficient] using
        abs_sub (jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
          (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ))
          (jumpKernel (physical ε z) * linearFn ε p z)
    · simp only [defectCoeff, if_neg he, sub_zero, abs_cycle_coefficient, add_zero,
        le_refl]
    · simp only [abs_zero, zero_add, abs_nonneg]
    · simp only [abs_zero, add_zero, le_refl]
  have hB := edge_indicator_tsum_le ε U x z
    |jumpKernel (physical ε z) * linearFn ε p z| (abs_nonneg _)
  have hbself := abs_self_coefficient_le hε.1 p z i hz
  have hn : 0 ≤ radius p * ε ^ (-((d : ℝ) + 1)) :=
    mul_nonneg (radius_nonneg _) (Real.rpow_nonneg hε.1.le _)
  calc
    _ ≤ ∑' r, (A r + B r) :=
      (summable_shortCoeff hd hε.1 hU p x z).abs.tsum_le_tsum hpoint (hs.add hsB)
    _ = (∑' r, A r) + ∑' r, B r := hs.tsum_add hsB
    _ ≤ C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|) +
        2 * (radius p * ε ^ (-((d : ℝ) + 1))) :=
      add_le_add ht (hB.trans (mul_le_mul_of_nonneg_left hbself (by norm_num)))
    _ ≤ _ := by
      have hm : 2 * (radius p * ε ^ (-((d : ℝ) + 1))) ≤
          2 * (radius p * ε ^ (-((d : ℝ) + 1))) * (1 + |Real.log ε|) :=
        le_mul_of_one_le_right (mul_nonneg (by norm_num) hn)
          (by simpa only [le_add_iff_nonneg_right] using abs_nonneg (Real.log ε))
      calc
        _ ≤ C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|) +
            2 * (radius p * ε ^ (-((d : ℝ) + 1))) * (1 + |Real.log ε|) :=
          add_le_add_right hm _
        _ = _ := by ring

/-- The full defect square sum and its summability follow from the cycle square majorant. -/
theorem defectCoeff_sq_sum_bound_with_summable (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ (p : Fin d → ℝ) (x z : Site d) (i : Fin d),
      (z = unit i ∨ z = -unit i) →
      Summable (fun r => defectCoeff ε U p x z r ^ 2) ∧
      ∑' r, defectCoeff ε U p x z r ^ 2 ≤
        C * radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)) := by
  classical
  obtain ⟨C, hC, hb⟩ := cycle_weight_sq_sum_bound hd
  refine ⟨2 * C + 4, by linarith, ?_⟩
  intro ε hε U _ p x z i hz
  obtain ⟨hs, ht⟩ := hb ε hε p (x + z) x (isNNEdge_add_unit x z i hz)
  let A := fun r : Cycle.indexSet ε U =>
    (cycleWeight ε p r.1.2 * |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)|) ^ 2
  let B := fun r : Cycle.indexSet ε U =>
    if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
      |jumpKernel (physical ε z) * linearFn ε p z| ^ 2 else 0
  have hsA : Summable A := by
    have hh := hs.subtype (Cycle.indexSet ε U)
    apply hh.congr
    intro r
    exact if_pos r.2.2.1
  have hA : ∑' r, A r ≤ C * radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)) := by
    have hh := Summable.tsum_subtype_le _ (Cycle.indexSet ε U)
      (by intro q; split_ifs <;> positivity) hs
    calc
      _ = ∑' r : Cycle.indexSet ε U, (if r.1.2 ≠ 0 then
          (cycleWeight ε p r.1.2 *
            |(Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)|) ^ 2 else 0) :=
        tsum_congr (fun r => (if_pos r.2.2.1).symm)
      _ ≤ _ := hh.trans ht
  have hsB : Summable B := summable_edge_indicator ε U x z _
  have hpoint (r : Cycle.indexSet ε U) : defectCoeff ε U p x z r ^ 2 ≤
      2 * A r + 2 * B r := by
    have halg (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
      nlinarith only [sq_nonneg (a + b)]
    have he := halg
      (jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
        (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ))
      (if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
        jumpKernel (physical ε z) * linearFn ε p z else 0)
    dsimp only [defectCoeff, A, B]
    rw [← abs_cycle_coefficient, sq_abs]
    split_ifs at he ⊢ <;> simpa only [sq_abs, zero_pow (by decide : 2 ≠ 0)] using he
  have hsum := (hsA.mul_left 2).add (hsB.mul_left 2)
  have hsD : Summable (fun r => defectCoeff ε U p x z r ^ 2) :=
    Summable.of_nonneg_of_le (fun r => sq_nonneg _) hpoint hsum
  refine ⟨hsD, ?_⟩
  have hbself := abs_self_coefficient_le hε.1 p z i hz
  have hpw : (radius p * ε ^ (-((d : ℝ) + 1))) ^ 2 =
      radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hε.1.le]
    congr 2
    ring
  have hB : ∑' r, B r ≤ 2 * (radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2))) := by
    calc
      _ ≤ 2 * |jumpKernel (physical ε z) * linearFn ε p z| ^ 2 :=
        edge_indicator_tsum_le ε U x z _ (sq_nonneg _)
      _ ≤ 2 * (radius p * ε ^ (-((d : ℝ) + 1))) ^ 2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg (radius_nonneg _)
            (Real.rpow_nonneg hε.1.le _))).mpr hbself) (by norm_num)
      _ = _ := by rw [hpw]
  calc
    _ ≤ ∑' r, (2 * A r + 2 * B r) := hsD.tsum_le_tsum hpoint hsum
    _ = 2 * (∑' r, A r) + 2 * ∑' r, B r := by
      rw [(hsA.mul_left 2).tsum_add (hsB.mul_left 2), tsum_mul_left, tsum_mul_left]
    _ ≤ 2 * (C * radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2))) +
        2 * (2 * (radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)))) :=
      add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
        (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = _ := by ring

/-- The full coefficient square sum has the all-scale deterministic normalization. -/
theorem defectCoeff_sq_sum_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ (p : Fin d → ℝ) (x z : Site d) (i : Fin d),
      (z = unit i ∨ z = -unit i) →
      ∑' r, defectCoeff ε U p x z r ^ 2 ≤
        C * radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)) := by
  obtain ⟨C, hC, hb⟩ := defectCoeff_sq_sum_bound_with_summable hd
  exact ⟨C, hC, fun ε hε U hU p x z i hz => (hb ε hε U hU p x z i hz).2⟩

end

end LongRange.Dirichlet
