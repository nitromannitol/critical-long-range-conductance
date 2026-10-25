import LongRangeAudit.QuenchedInvariance.Vocabulary.KernelSummability

/-! # Independent WalkRates vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The jump rates of the walk with generator `L^ε`: `x → y` at rate
`ε^d/κ_ε · a{x,y} J(ε(y − x))`. -/
noncomputable def walkRate (ε : ℝ) (a : Edge d → ℝ) (x y : Site d) : ℝ :=
  if h : y - x = 0 then 0 else
    ε ^ d / kappa d ε * a (edgeAdd x (y - x) h) * jumpKernel (physical ε (y - x))

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

end LongRange
end

end LongRangeAudit.QuenchedInvariance
