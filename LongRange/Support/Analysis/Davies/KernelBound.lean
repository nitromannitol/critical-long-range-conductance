import LongRange.Support.Analysis.Davies.TwistKernel

/-!
# Squaring finite twisted-semigroup bounds

Duality and the semigroup law turn a two-to-infinity estimate into a kernel bound.
-/

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- A two-to-infinity estimate bounds the two-norm of each twisted-kernel row. -/
theorem twistKernel_row_sqrt_le {ψ : ι → ℝ} {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hbound : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → ∀ i,
      F.twist ψ f s i ≤ K * Real.sqrt (∑ j, f j ^ 2)) (i : ι) :
    Real.sqrt (∑ j, F.twistKernel ψ s i j ^ 2) ≤ K := by
  let u : ι → ℝ := fun j ↦ F.twistKernel ψ s i j
  have hu : ∀ j, 0 ≤ u j := fun j ↦ F.twistKernel_nonneg ψ hs i j
  have h := hbound u hu i
  rw [F.twist_eq_sum] at h
  have he : (∑ j, F.twistKernel ψ s i j * u j) = ∑ j, u j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [u]
    ring
  rw [he] at h
  have hsq : (Real.sqrt (∑ j, u j ^ 2)) ^ 2 = ∑ j, u j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg (u j))
  have hr0 := Real.sqrt_nonneg (∑ j, u j ^ 2)
  change Real.sqrt (∑ j, u j ^ 2) ≤ K
  by_cases hz : Real.sqrt (∑ j, u j ^ 2) = 0
  · linarith
  · have hp : 0 < Real.sqrt (∑ j, u j ^ 2) := lt_of_le_of_ne hr0 (Ne.symm hz)
    nlinarith

/-- Duality and semigroup composition square a two-to-infinity estimate. -/
theorem twistKernel_le_sq {ψ : ι → ℝ} {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hbound : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → ∀ i,
      F.twist ψ f s i ≤ K * Real.sqrt (∑ j, f j ^ 2))
    (hboundNeg : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → ∀ i,
      F.twist (-ψ) f s i ≤ K * Real.sqrt (∑ j, f j ^ 2)) (i j : ι) :
    F.twistKernel ψ (s + s) i j ≤ K ^ 2 := by
  have hrow := F.twistKernel_row_sqrt_le hs hK hbound i
  have hcol : Real.sqrt (∑ k, F.twistKernel ψ s k j ^ 2) ≤ K := by
    simpa only [F.twistKernel_neg_flip] using F.twistKernel_row_sqrt_le hs hK hboundNeg j
  calc
    F.twistKernel ψ (s + s) i j =
        ∑ k, F.twistKernel ψ s i k * F.twistKernel ψ s k j := F.twistKernel_add ψ s s i j
    _ ≤ Real.sqrt (∑ k, F.twistKernel ψ s i k ^ 2) *
        Real.sqrt (∑ k, F.twistKernel ψ s k j ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ K ^ 2 := by
      simpa only [sq] using mul_le_mul hrow hcol (Real.sqrt_nonneg _) hK

end
end LatticeProb.Davies.FiniteJumpForm
