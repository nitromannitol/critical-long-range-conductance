import LongRange.Poincare.Summability
import LongRange.Poincare.Mass

/-!
# Restricting the energy to a triadic shell

Absolute convergence permits summing first over displacements. The forward box lies inside
the shell, so its weighted displacement energy is bounded by the shell energy.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The exact summand of the sup-norm shell energy, with the Euclidean jump kernel. -/
def shellTerm (ε : ℝ) (k : ℕ) (h : Site d → ℝ) (p : Site d × Site d) : ℝ :=
  if ε * 3 ^ k ≤ ‖physical ε p.2‖ ∧ ‖physical ε p.2‖ < ε * 3 ^ (k + 1) then
    jumpKernel (physical ε p.2) * (h (p.1 + p.2) - h p.1) ^ 2
  else 0

/-- Shell energy summands are nonnegative. -/
theorem shellTerm_nonneg (ε : ℝ) (k : ℕ) (h : Site d → ℝ) (p : Site d × Site d) :
    0 ≤ shellTerm ε k h p := by
  unfold shellTerm
  split
  · exact mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)
  · exact le_rfl

/-- The weighted displacement energies on the half-slab are bounded by the shell energy. -/
theorem forwardBox_energy_le {d k : ℕ} {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin (d + 1) → ℝ)}
    (hU : Bornology.IsBounded U) {h : Site (d + 1) → ℝ} (hh : SupportedIn ε U h) :
    (∑ z ∈ forwardBox d k, jumpKernel (physical ε z) *
      ∑' x, (h (x + z) - h x) ^ 2) ≤ ∑' p, shellTerm ε k h p := by
  have hs : Summable (shellTerm ε k h) := summable_single_scale (d + 1)
    (by omega) hε hU hh k
  have he : (∑ z ∈ forwardBox d k, jumpKernel (physical ε z) *
      ∑' x, (h (x + z) - h x) ^ 2) =
      ∑ z ∈ forwardBox d k, ∑' x, shellTerm ε k h (x, z) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [← tsum_mul_left]
    apply tsum_congr
    intro x
    exact (if_pos (forwardBox_shell hε.1 hz)).symm
  have hswap := (Equiv.prodComm (Site (d + 1)) (Site (d + 1))).tsum_eq
    (shellTerm ε k h)
  simp only [Equiv.prodComm_apply] at hswap
  rw [he, ← hswap, hs.prod_symm.tsum_prod]
  exact hs.prod_symm.prod.sum_le_tsum _ (fun z _ =>
    tsum_nonneg (fun x => shellTerm_nonneg ε k h (x, z)))

end

end LongRange.Poincare
