import LongRange.Model.Operator
import LongRange.Calculus.Summability
import LongRange.Calculus.BilinForm
import LatticeProb.Prob.JumpChain.Rates

/-!
# Bounded rates for the rescaled walk

The symmetric conductances and Euclidean jump kernel define summable jump rates.
Their generator agrees with the rescaled nonlocal operator on bounded functions.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The jump rates of the walk with generator `L^ε`: `x → y` at rate
`ε^d/κ_ε · a{x,y} J(ε(y − x))`. -/
noncomputable def walkRate (ε : ℝ) (a : Edge d → ℝ) (x y : Site d) : ℝ :=
  if h : y - x = 0 then 0 else
    ε ^ d / kappa d ε * a (edgeAdd x (y - x) h) * jumpKernel (physical ε (y - x))

/-- Unordered conductances and the even kernel make the walk rates symmetric. -/
theorem walkRate_symm (ε : ℝ) (a : Edge d → ℝ) (x y : Site d) :
    walkRate ε a x y = walkRate ε a y x := by
  by_cases hxy : y - x = 0
  · have hy : y = x := sub_eq_zero.mp hxy
    subst y
    simp only [walkRate, sub_self, dite_true]
  · have hneg : x - y = -(y - x) := by abel
    have hedge := edgeAdd_reverse x (y - x) hxy
    rw [add_sub_cancel] at hedge
    simp only [walkRate, hxy, hneg, neg_ne_zero.mpr hxy, dite_false,
      physical_neg, jumpKernel_neg, hedge]

/-- Each rate is nonnegative under uniform ellipticity. -/
theorem walkRate_nonneg {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) :
    0 ≤ walkRate ε a x y := by
  unfold walkRate
  split
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg
      (div_nonneg (pow_nonneg hε.le _) (kappa_nonneg hε.le))
      (hlam.le.trans (ha _).1)) (jumpKernel_nonneg _)

/-- The translated kernel dominates each outgoing rate. -/
theorem walkRate_le {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) :
    walkRate ε a x y ≤
      (ε ^ d / kappa d ε * lam⁻¹) * jumpKernel (physical ε (y - x)) := by
  have hc : 0 ≤ ε ^ d / kappa d ε :=
    div_nonneg (pow_nonneg hε.le _) (kappa_nonneg hε.le)
  unfold walkRate
  split
  · exact mul_nonneg (mul_nonneg hc (inv_nonneg.mpr hlam.le)) (jumpKernel_nonneg _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha _).2 hc)
      (jumpKernel_nonneg _)

/-- The rescaled walk has a uniform finite bound on its total jump rate. -/
noncomputable def walkRates (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    LatticeProb.JumpChain.BoundedRates (Site d) := by
  have hc : 0 ≤ ε ^ d / kappa d ε * lam⁻¹ :=
    mul_nonneg (div_nonneg (pow_nonneg hε.le _) (kappa_nonneg hε.le))
      (inv_nonneg.mpr hlam.le)
  have hdom (x : Site d) : Summable (fun y : Site d =>
      (ε ^ d / kappa d ε * lam⁻¹) * jumpKernel (physical ε (y - x))) := by
    apply (Equiv.summable_iff (Equiv.addLeft x)).mp
    simpa only [Function.comp_def, Equiv.coe_addLeft, add_sub_cancel_left] using
      (summable_jumpKernel hd hε).mul_left (ε ^ d / kappa d ε * lam⁻¹)
  have hs (x : Site d) : Summable (walkRate ε a x) :=
    (hdom x).of_nonneg_of_le (walkRate_nonneg hε hlam ha x)
      (walkRate_le hε hlam ha x)
  refine { q := walkRate ε a
           q_nonneg := walkRate_nonneg hε hlam ha
           q_self := ?_
           summable := hs
           R := ε ^ d / kappa d ε * lam⁻¹ *
             ∑' w : Site d, jumpKernel (physical ε w) + 1
           R_pos := ?_
           total_le := ?_ }
  · intro x
    simp only [walkRate, sub_self, dite_true]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg hc (tsum_nonneg (fun _ => jumpKernel_nonneg _))) zero_lt_one
  · intro x
    have ht := (Equiv.addLeft x).tsum_eq (fun y : Site d =>
      (ε ^ d / kappa d ε * lam⁻¹) * jumpKernel (physical ε (y - x)))
    simp only [Equiv.coe_addLeft, add_sub_cancel_left, tsum_mul_left] at ht
    have hb := (hs x).tsum_le_tsum (walkRate_le hε hlam ha x) (hdom x)
    rw [tsum_mul_left, ← ht] at hb
    exact hb.trans (le_add_of_nonneg_right zero_le_one)

/-- Reindexing destinations by their increments identifies the walk generator with `L^ε`
(as an identity of `tsum`s; no summability is needed). -/
theorem generator_eq_walkRate_tsum (ε : ℝ) (a : Edge d → ℝ) (h : Site d → ℝ) (x : Site d) :
    generator ε a h x = ∑' y, walkRate ε a x y * (h y - h x) := by
  rw [← (Equiv.addLeft x).tsum_eq (fun y => walkRate ε a x y * (h y - h x))]
  unfold generator
  rw [← tsum_mul_left]
  apply tsum_congr
  intro w
  simp only [Equiv.coe_addLeft, walkRate, add_sub_cancel_left]
  by_cases hw : w = 0 <;> simp only [hw, dite_true, dite_false] <;> ring

end

end LongRange
