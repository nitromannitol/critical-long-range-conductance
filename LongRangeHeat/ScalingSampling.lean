import LongRangeHeat.Defs
import LatticeProb.Walk.RiemannLattice

/-!
# Sampling compactly supported functions

The lattice norm of a sampled continuous, compactly supported function converges to its
continuum norm as the spacing tends to zero.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- The squared lattice norm of a sampled function converges to its square integral. -/
theorem tendsto_latticeNormSq_sample {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε : ℝ => latticeNormSq ε (fun q => f (physical ε q)))
      (𝓝[>] 0) (𝓝 (∫ x, f x ^ 2)) := by
  have hs : HasCompactSupport (fun x => f x ^ 2) := by
    have heq : (fun x => f x ^ 2) = f * f := by
      funext x
      exact sq (f x)
    rw [heq]
    exact hfc.mul_right
  have ht := (LatticeProb.Walk.tendsto_latticeSum_mul_rpow (hf.pow 2) hs).comp
    tendsto_inv_nhdsGT_zero
  simp only [Pi.pow_apply] at ht
  convert ht using 1
  funext ε
  simp only [Function.comp_apply, one_div, inv_inv, div_inv_eq_mul, latticeNormSq]
  rw [mul_comm]
  congr 1
  apply tsum_congr
  intro q
  congr 1
  apply congrArg f
  funext i
  simp only [physical]
  exact mul_comm _ _

/-- The lattice norm of a sampled function converges to its continuum norm. -/
theorem tendsto_latticeNorm_sample {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun ε : ℝ => latticeNorm ε (fun q => f (physical ε q)))
      (𝓝[>] 0) (𝓝 (Real.sqrt (∫ x, f x ^ 2))) := by
  exact (Real.continuous_sqrt.tendsto _).comp (tendsto_latticeNormSq_sample hf hfc)

end
end LongRangeHeat
