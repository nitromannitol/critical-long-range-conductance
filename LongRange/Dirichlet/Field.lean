import LongRange.Dirichlet.FieldSummable

/-!
# The solenoidal comparison field

The comparison field uses an arbitrary real background coefficient and the physical linear
slope. Its correction is the source-oriented series over unique unordered-edge representatives.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The comparison field `g_p(y, x)` of (e.gp.def) with background coefficient `m`. -/
def gpField (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ) (m : ℝ) (p : Fin d → ℝ)
    (y x : Site d) : ℝ :=
  m * jumpKernel (physical ε (y - x)) * linearFn ε p (y - x) +
    ∑' r : Cycle.indexSet ε U, (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
      jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
        (Cycle.cycle r.1.1 r.1.2 y x : ℝ)

/-- Reversing a physical linear increment reverses its slope. -/
theorem linearFn_neg (ε : ℝ) (p : Fin d → ℝ) (v : Site d) :
    linearFn ε p (-v) = -linearFn ε p v := by
  simp only [linearFn, physical_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- The comparison field is antisymmetric. -/
theorem gpField_antisymm (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ)
    (m : ℝ) (p : Fin d → ℝ) (y x : Site d) :
    gpField ε U a m p y x = -gpField ε U a m p x y := by
  have hb : x - y = -(y - x) := (neg_sub y x).symm
  simp only [gpField, hb, physical_neg, jumpKernel_neg, linearFn_neg]
  have hc : (∑' r : Cycle.indexSet ε U,
      (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) * jumpKernel (physical ε r.1.2) *
        linearFn ε p r.1.2 * (Cycle.cycle r.1.1 r.1.2 y x : ℝ)) =
      -(∑' r : Cycle.indexSet ε U,
      (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) * jumpKernel (physical ε r.1.2) *
        linearFn ε p r.1.2 * (Cycle.cycle r.1.1 r.1.2 x y : ℝ)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro r
    rw [Cycle.cycle_antisymm r.1.1 r.1.2 y x, Int.cast_neg, mul_neg]
  rw [hc]
  ring

/-- Constant conductances equal to the background leave exactly the background field. -/
theorem gpField_const (ε : ℝ) (U : Set (Fin d → ℝ)) (m : ℝ) (p : Fin d → ℝ)
    (y x : Site d) :
    gpField ε U (fun _ => m) m p y x =
      m * jumpKernel (physical ε (y - x)) * linearFn ε p (y - x) := by
  simp only [gpField, sub_self, zero_mul, tsum_zero, add_zero]

/-- The flux defect is the background defect plus the complete cycle correction series. -/
theorem gpField_sub_conductance (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ)
    (m : ℝ) (p : Fin d → ℝ) (x z : Site d) (hz : z ≠ 0) :
    gpField ε U a m p (x + z) x -
        a (edgeAdd x z hz) * jumpKernel (physical ε z) * linearFn ε p z =
      (m - a (edgeAdd x z hz)) * jumpKernel (physical ε z) * linearFn ε p z +
        ∑' r : Cycle.indexSet ε U, (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
          jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
            (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ) := by
  rw [gpField, add_sub_cancel_left]
  ring

/-- Every unit-displacement representative contributes zero on every observation edge. -/
theorem field_correction_unit_eq_zero (ε : ℝ) (U : Set (Fin d → ℝ))
    (a : Edge d → ℝ) (m : ℝ) (p : Fin d → ℝ) (r : Cycle.indexSet ε U)
    (i : Fin d) (hv : r.1.2 = unit i ∨ r.1.2 = -unit i) (y x : Site d) :
    (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) * jumpKernel (physical ε r.1.2) *
      linearFn ε p r.1.2 * (Cycle.cycle r.1.1 r.1.2 y x : ℝ) = 0 := by
  rw [Cycle.cycle_eq_zero_of_unit r.1.1 r.1.2 y x i hv, Int.cast_zero, mul_zero]

/-- The background field has zero divergence by reversal of its physical increment. -/
theorem background_divergence (ε m : ℝ) (p : Fin d → ℝ) :
    ∑' w : Site d, m * jumpKernel (physical ε w) * linearFn ε p w = 0 := by
  have h := (Equiv.neg (Site d)).tsum_eq
    (fun w => m * jumpKernel (physical ε w) * linearFn ε p w)
  simp only [Equiv.neg_apply, physical_neg, jumpKernel_neg, linearFn_neg,
    mul_neg, tsum_neg] at h
  linarith

/-- The comparison field is summable in the incoming increment at every lattice vertex. -/
theorem summable_gpField (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} {A : ℝ} (ha : ∀ e, |a e| ≤ A)
    (m : ℝ) (p : Fin d → ℝ) (x : Site d) :
    Summable (fun w : Site d => gpField ε U a m p (x + w) x) := by
  have hb : Summable (fun w : Site d =>
      m * jumpKernel (physical ε w) * linearFn ε p w) := by
    have hs : Summable (fun w : Site d =>
        jumpKernel (physical ε w) * linearFn ε p w) := by
      apply Summable.of_norm
      simpa only [Real.norm_eq_abs] using summable_kernel_linear hd hε p
    simpa only [mul_assoc] using hs.mul_left m
  have hs : Summable (fun q : Cycle.indexSet ε U × Site d =>
      (a (edgeAdd q.1.1.1 q.1.1.2 q.1.2.2.1) - m) *
        jumpKernel (physical ε q.1.1.2) * linearFn ε p q.1.1.2 *
          (Cycle.cycle q.1.1.1 q.1.1.2 q.2 x : ℝ)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using summable_field_correction_prod hd hε hU ha m p x
  have hc := hs.prod_symm.prod.comp_injective (Equiv.addLeft x).injective
  simpa only [gpField, add_sub_cancel_left, Equiv.coe_addLeft, Function.comp_def,
    Prod.swap_prod_mk] using hb.add hc

/-- Absolute convergence allows the divergence-free cycle identity to pass to the field. -/
theorem gpField_divergence (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} {A : ℝ} (ha : ∀ e, |a e| ≤ A)
    (m : ℝ) (p : Fin d → ℝ) (x : Site d) :
    ∑' w : Site d, gpField ε U a m p (x + w) x = 0 := by
  have hb : Summable (fun w : Site d =>
      m * jumpKernel (physical ε w) * linearFn ε p w) := by
    have hs : Summable (fun w : Site d =>
        jumpKernel (physical ε w) * linearFn ε p w) := by
      apply Summable.of_norm
      simpa only [Real.norm_eq_abs] using summable_kernel_linear hd hε p
    simpa only [mul_assoc] using hs.mul_left m
  have hs : Summable (fun q : Cycle.indexSet ε U × Site d =>
      (a (edgeAdd q.1.1.1 q.1.1.2 q.1.2.2.1) - m) *
        jumpKernel (physical ε q.1.1.2) * linearFn ε p q.1.1.2 *
          (Cycle.cycle q.1.1.1 q.1.1.2 q.2 x : ℝ)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using summable_field_correction_prod hd hε hU ha m p x
  simp only [gpField, add_sub_cancel_left]
  have hc : Summable (fun w : Site d =>
      ∑' r : Cycle.indexSet ε U, (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
        jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
          (Cycle.cycle r.1.1 r.1.2 (x + w) x : ℝ)) := by
    have ht := hs.prod_symm.prod.comp_injective (Equiv.addLeft x).injective
    simpa only [Equiv.coe_addLeft, Function.comp_def, Prod.swap_prod_mk] using ht
  rw [hb.tsum_add hc, background_divergence, zero_add]
  have ht := Summable.tsum_comm (f := fun (r : Cycle.indexSet ε U) (y : Site d) =>
    (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
      jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
        (Cycle.cycle r.1.1 r.1.2 y x : ℝ)) hs
  calc
    _ = ∑' y : Site d, ∑' r : Cycle.indexSet ε U,
        (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
          jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
            (Cycle.cycle r.1.1 r.1.2 y x : ℝ) := by
      simpa only [Equiv.coe_addLeft] using (Equiv.addLeft x).tsum_eq (fun y =>
        ∑' r : Cycle.indexSet ε U, (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
          jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
            (Cycle.cycle r.1.1 r.1.2 y x : ℝ))
    _ = _ := ht
    _ = 0 := by
      simp only [tsum_mul_left, Cycle.cycle_divergence, mul_zero, tsum_zero]

/-- Distinct representatives correspond to distinct unordered edges. -/
lemma indexSet_edge_injective (ε : ℝ) (U : Set (Fin d → ℝ))
    (r s : Cycle.indexSet ε U)
    (he : s(r.1.1, r.1.1 + r.1.2) = s(s.1.1, s.1.1 + s.1.2)) : r = s := by
  apply Subtype.ext
  rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hv' : r.1.2 = s.1.2 := by
      apply add_left_cancel (a := s.1.1)
      simpa only [hu] using hv
    exact Prod.ext hu hv'
  · exfalso
    have hv' : s.1.2 = -r.1.2 := by
      have h : r.1.1 = (r.1.1 + r.1.2) + s.1.2 :=
        hu.trans (congrArg (· + s.1.2) hv.symm)
      have hh : r.1.2 + s.1.2 = 0 := by
        apply add_left_cancel (a := r.1.1)
        simpa only [add_assoc, add_zero] using h.symm
      exact eq_neg_of_add_eq_zero_right hh
    have hs : (r.1.1 + r.1.2, -r.1.2) ∈ Cycle.indexSet ε U := by
      have heq : s.1 = (r.1.1 + r.1.2, -r.1.2) := Prod.ext hv.symm hv'
      exact heq ▸ s.2
    rcases Cycle.indexSet_exactly_one ε U r.1.1 r.1.2 r.2.1 r.2.2.1 with h | h
    · exact h.2 hs
    · exact h.1 r.2

/-- On a nonlocal representative edge the correction series consists of its own term. -/
lemma field_correction_long_edge (ε : ℝ) (U : Set (Fin d → ℝ))
    (a : Edge d → ℝ) (m : ℝ) (p : Fin d → ℝ)
    (r : Cycle.indexSet ε U)
    (hv : ∀ i : Fin d, r.1.2 ≠ unit i ∧ r.1.2 ≠ -unit i) :
    (∑' s : Cycle.indexSet ε U, (a (edgeAdd s.1.1 s.1.2 s.2.2.1) - m) *
      jumpKernel (physical ε s.1.2) * linearFn ε p s.1.2 *
        (Cycle.cycle s.1.1 s.1.2 (r.1.1 + r.1.2) r.1.1 : ℝ)) =
      (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
        jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 := by
  classical
  rw [tsum_eq_single r]
  · rw [Cycle.cycle_long_edge _ _ hv r.2.2.1, Int.cast_one, mul_one]
  · intro s hsr
    have hc : Cycle.cycle s.1.1 s.1.2 (r.1.1 + r.1.2) r.1.1 = 0 := by
      by_contra hn
      rcases Cycle.cycle_support _ _ _ _ hn with he | he
      · apply hsr
        apply indexSet_edge_injective ε U
        exact he.symm.trans Sym2.eq_swap
      · exact Cycle.long_edge_not_isNNEdge r.1.1 r.1.2 hv
          (by rw [Sym2.eq_swap]; exact Cycle.cycle_support_isNNEdge _ _ _ _ he)
    rw [hc, Int.cast_zero, mul_zero]

/-- The field agrees with the conductance flux on every non-nearest-neighbour edge. -/
theorem gpField_nonnearest (ε : ℝ) (U : Set (Fin d → ℝ))
    (a : Edge d → ℝ) (m : ℝ) (p : Fin d → ℝ) (x z : Site d)
    (hx : x ∈ latticeSet ε U) (hz : z ≠ 0)
    (hzn : ∀ i : Fin d, z ≠ unit i ∧ z ≠ -unit i) :
    gpField ε U a m p (x + z) x =
      a (edgeAdd x z hz) * jumpKernel (physical ε z) * linearFn ε p z := by
  rcases Cycle.indexSet_exactly_one ε U x z hx hz with h | h
  · let r : Cycle.indexSet ε U := ⟨(x, z), h.1⟩
    have hc := field_correction_long_edge ε U a m p r hzn
    change (∑' s : Cycle.indexSet ε U, (a (edgeAdd s.1.1 s.1.2 s.2.2.1) - m) *
      jumpKernel (physical ε s.1.2) * linearFn ε p s.1.2 *
        (Cycle.cycle s.1.1 s.1.2 (x + z) x : ℝ)) = _ at hc
    rw [gpField, add_sub_cancel_left, hc]
    dsimp only [r]
    ring
  · have hneg : ∀ i : Fin d, -z ≠ unit i ∧ -z ≠ -unit i := by
      intro i
      constructor
      · intro he
        exact (hzn i).2 (neg_eq_iff_eq_neg.mp he)
      · exact fun he => (hzn i).1 (neg_injective he)
    have hrev := gpField_antisymm ε U a m p (x + z) x
    let r : Cycle.indexSet ε U := ⟨(x + z, -z), h.2⟩
    have hc := field_correction_long_edge ε U a m p r hneg
    have he' : gpField ε U a m p (r.1.1 + r.1.2) r.1.1 =
        a (edgeAdd r.1.1 r.1.2 r.2.2.1) *
          jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 := by
      rw [gpField, add_sub_cancel_left, hc]
      ring
    have he : gpField ε U a m p x (x + z) =
        a (edgeAdd (x + z) (-z) (neg_ne_zero.mpr hz)) *
          jumpKernel (physical ε (-z)) * linearFn ε p (-z) := by
      simpa only [r, add_neg_cancel_right] using he'
    rw [hrev, he, edgeAdd_reverse x z hz, physical_neg, jumpKernel_neg, linearFn_neg]
    ring

end

end LongRange.Dirichlet
