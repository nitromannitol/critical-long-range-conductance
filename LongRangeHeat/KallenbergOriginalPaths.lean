import LongRangeHeat.KallenbergTransformedPaths
import LongRangeHeat.KallenbergChangeTail
import LongRangeHeat.KallenbergTimeChangeContinuity

/-!
# Convergence of time-aligned paths

Locally uniform convergence after time alignment yields convergence of the
original paths when the distortions of the changes are summable.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Summable distortions and aligned discrepancies provide a path-space limit. -/
theorem exists_tendsto_of_summable_timeChanges {E : Type*} [MetricSpace E]
    [CompleteSpace E] (x : ℕ → D E) (l : ℕ → Lambda)
    (hg : (∑' n, gamma (l n).1) ≠ ∞)
    (hd : Summable fun n =>
      (integratedDiscrepancy (x n) (x (n + 1)) (l n).1.symm).toReal) :
    ∃ y : D E, Tendsto x atTop (𝓝 y) := by
  obtain ⟨L, hL⟩ := exists_lambda_tendstoUniformlyOn_changePrefix l hg
  obtain ⟨z, hz⟩ := exists_tendstoUniformlyOn_transformedPaths x l hg hd
  let C : ℝ := (∑' n, gamma (l n).1).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hbound (n : ℕ) : gamma (changePrefix l n).1 ≤ ENNReal.ofReal C := by
    rw [show ENNReal.ofReal C = ∑' n, gamma (l n).1 from ENNReal.ofReal_toReal hg]
    exact (gamma_changePrefix_le l n).trans (ENNReal.sum_le_tsum _)
  have htime (n : ℕ) (t : Time) :
      (((changePrefix l n).1 t : Time) : ℝ) ≤ Real.exp C * (t : ℝ) := by
    have h := coe_symm_le_exp_mul (changePrefix l n).symm hC (by
      simpa only [Lambda.gamma_symm] using hbound n) t
    simpa only [Lambda.symm, OrderIso.symm_symm] using h
  let r : ℕ → Lambda := fun n => (L.trans (changePrefix l n).symm).symm
  have hr : Tendsto (fun n => gamma (r n).1) atTop (𝓝 0) := by
    simpa only [r, Lambda.gamma_symm] using tendsto_gamma_relativeLimit l L hg hL
  let y : D E := z.comp L.1
  have hy : Tendsto (fun n => y.comp (r n).1) atTop (𝓝 y) :=
    tendsto_comp_of_tendsto_gamma y r hr
  have halign : Tendsto (fun n => dist (x n) (y.comp (r n).1)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he : 0 < ε / 4 := by positivity
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he))
    let T : Time := ⟨max R 0, le_max_right _ _⟩
    let U : Time := ⟨Real.exp C * (T : ℝ), mul_nonneg (Real.exp_pos C).le T.2⟩
    have htail : Real.exp (-(T : ℝ)) < ε / 4 := hR _ (le_max_left _ _)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hz U) (ε / 4) he] with n hn
    have hb : dist (x n) (y.comp (r n).1) ≤ ε / 4 + Real.exp (-(T : ℝ)) := by
      apply dist_le_of_finite_horizon _ _ T he.le
      intro t ht
      have htU : (changePrefix l n).1 t ≤ U := by
        change (((changePrefix l n).1 t : Time) : ℝ) ≤ (U : ℝ)
        exact (htime n t).trans (mul_le_mul_of_nonneg_left
          (show (t : ℝ) ≤ T from ht) (Real.exp_pos C).le)
      have h := hn ((changePrefix l n).1 t) (mem_Iic.mpr htU)
      have heq : (y.comp (r n).1).1 t = z.1 ((changePrefix l n).1 t) := by
        simp only [y, r, D.comp, Function.comp_apply, Lambda.symm, Lambda.trans,
          OrderIso.symm_trans, OrderIso.trans_apply, OrderIso.apply_symm_apply, OrderIso.symm_symm]
      have heq' : ((x n).comp (changePrefix l n).1.symm).1
          ((changePrefix l n).1 t) = (x n).1 t := by
        simp only [D.comp, Function.comp_apply, OrderIso.symm_apply_apply]
      rw [heq, ← heq']
      exact (by simpa only [dist_comm] using h.le)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
      (show dist (x n) (y.comp (r n).1) < ε by linarith)
  refine ⟨y, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp halign (ε / 2) (half_pos hε),
    Metric.tendsto_nhds.mp hy (ε / 2) (half_pos hε)] with n hn1 hn2
  have hn1' : dist (x n) (y.comp (r n).1) < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hn1
  linarith [dist_triangle (x n) (y.comp (r n).1) y]

end

end LatticeProb.Cadlag.HalfLine
