import LongRangeHeat.KallenbergCadlagLimit
import LongRangeHeat.KallenbergFiniteHorizon

/-!
# Uniform convergence and the half-line Skorokhod metric

Locally uniform convergence implies convergence in the half-line Skorokhod
metric, and its limit is a càdlàg path when the state space is complete.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped Topology

/-- Locally uniform convergence implies convergence in the half-line path metric. -/
theorem tendsto_of_tendstoUniformlyOn {E : Type*} [MetricSpace E]
    {x : ℕ → D E} {y : D E}
    (h : ∀ T : Time, TendstoUniformlyOn (fun n => (x n).1) y.1 atTop (Iic T)) :
    Tendsto x atTop (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 4 := by positivity
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he))
  let T : Time := ⟨max R 0, le_max_right _ _⟩
  have htail : Real.exp (-(T : ℝ)) < ε / 4 := hR _ (le_max_left _ _)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h T) (ε / 4) he] with n hn
  have hb : dist (x n) y ≤ ε / 4 + Real.exp (-(T : ℝ)) :=
    dist_le_of_finite_horizon (x n) y T he.le (fun t ht => by
      rw [dist_comm]
      exact (hn t ht).le)
  linarith

/-- A locally uniform limit into a complete space defines a càdlàg path and
is the limit in the half-line path metric. -/
theorem exists_tendsto_of_tendstoUniformlyOn_paths {E : Type*} [MetricSpace E] [CompleteSpace E]
    {x : ℕ → D E} {y : Time → E}
    (h : ∀ T : Time, TendstoUniformlyOn (fun n => (x n).1) y atTop (Iic T)) :
    ∃ z : D E, z.1 = y ∧ Tendsto x atTop (𝓝 z) := by
  let z : D E := ⟨y, IsCadlag.of_tendstoUniformlyOn (fun n => (x n).2) h⟩
  exact ⟨z, rfl, tendsto_of_tendstoUniformlyOn h⟩

end LatticeProb.Cadlag.HalfLine
