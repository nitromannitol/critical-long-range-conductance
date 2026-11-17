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


/-- A nonzero continuous compactly supported function has positive square integral. -/
theorem integral_sq_pos_of_ne_zero {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {x : Fin d → ℝ} (hx : f x ≠ 0) :
    0 < ∫ y, f y ^ 2 := by
  have hs : HasCompactSupport (fun y => f y ^ 2) := by
    have heq : (fun y => f y ^ 2) = f * f := by
      funext y
      exact sq (f y)
    rw [heq]
    exact hfc.mul_right
  exact (hf.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero hs
    (fun y => sq_nonneg _) (pow_ne_zero 2 hx)


/-- A nonzero continuous compactly supported function has a positive sampled norm at small mesh. -/
theorem eventually_latticeNorm_sample_pos {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {x : Fin d → ℝ} (hx : f x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0,
      c ≤ latticeNorm ε (fun q => f (physical ε q)) := by
  have hp : 0 < Real.sqrt (∫ y, f y ^ 2) :=
    Real.sqrt_pos.2 (integral_sq_pos_of_ne_zero hf hfc hx)
  refine ⟨Real.sqrt (∫ y, f y ^ 2) / 2, by positivity, ?_⟩
  filter_upwards [(tendsto_latticeNorm_sample hf hfc).eventually
    (eventually_gt_nhds (half_lt_self hp))] with ε hε
  exact hε.le

end
end LongRangeHeat
