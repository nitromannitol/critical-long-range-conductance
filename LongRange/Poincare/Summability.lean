import LongRange.Poincare.Support
import LongRange.Calculus.BilinForm

/-!
# Summability of the critical energy

The stage's absolute convergence theorem applies to bounded-domain supported functions.
Restricting its nonnegative pair energy to any printed sup-norm shell preserves summability;
the jump kernel in the summand remains Euclidean.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Every triadic-shell energy sum is summable for bounded-domain support. -/
theorem summable_single_scale (d : ℕ) (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {h : Site d → ℝ} (hh : SupportedIn ε U h) (k : ℕ) :
    Summable (fun p : Site d × Site d =>
      if ε * 3 ^ k ≤ ‖physical ε p.2‖ ∧ ‖physical ε p.2‖ < ε * 3 ^ (k + 1) then
        jumpKernel (physical ε p.2) * (h (p.1 + p.2) - h p.1) ^ 2
      else 0) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (summable_h1CritSq hd hε.1 (hh.hasFiniteSupport hε.1 hU))
  · intro p
    split
    · exact mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)
    · exact le_rfl
  · intro p
    split
    · exact le_rfl
    · exact mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)

end

end LongRange
