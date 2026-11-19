import LongRange.HeatKernel.CriticalSpectralScalar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Spectral comparison for iterated contractions

Continuous functional calculus lifts the scalar multiplier bound to symmetric
contractions in a star-ordered C-star algebra.
-/

open scoped CStarAlgebra

namespace LatticeProb.Graph.LongRangeKernel

/-- Iterating a self-adjoint contraction multiplies its defect by at most the time. -/
theorem one_sub_pow_le_nat_smul_one_sub {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (ha : IsSelfAdjoint a)
    (hnorm : ‖a‖ ≤ 1) (n : ℕ) :
    1 - a ^ n ≤ (n : ℝ) • (1 - a) := by
  let _ := IsStarNormal.instContinuousFunctionalCalculus (A := A)
  let _ := IsSelfAdjoint.instContinuousFunctionalCalculus (A := A)
  have h : cfc (fun t : ℝ => 1 - t ^ n) a ≤
      cfc (fun t : ℝ => (n : ℝ) * (1 - t)) a := by
    apply (cfc_le_iff _ _ a (by fun_prop) (by fun_prop) ha).2
    intro t ht
    apply one_sub_pow_le_nat_mul_one_sub _ n
    simpa only [Real.norm_eq_abs] using
      (quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ a ht)).trans hnorm
  rw [cfc_sub (fun _ : ℝ => 1) (fun t => t ^ n) a (by fun_prop) (by fun_prop),
    cfc_const_one ℝ a ha, cfc_pow_id a n ha] at h
  rw [cfc_const_mul (n : ℝ) (fun t => 1 - t) a (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun t => t) a (by fun_prop) (by fun_prop),
    cfc_const_one ℝ a ha, cfc_id' ℝ a ha] at h
  exact h

end LatticeProb.Graph.LongRangeKernel
