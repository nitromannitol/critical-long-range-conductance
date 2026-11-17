import LongRangeHeat.KallenbergChangeLimit
import LongRangeHeat.KallenbergDiscrepancyLower
import LongRange.Support.Prob.Cadlag.HalfLine.Paths

/-!
# Time-aligned paths

Uniform distortion bounds control the inverse times used to align paths.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal Topology

noncomputable section

/-- A uniform distortion bound bounds the inverse time change. -/
theorem coe_symm_le_exp_mul (l : Lambda) {C : ℝ} (hC : 0 ≤ C)
    (hbound : gamma l.1 ≤ ENNReal.ofReal C) (t : Time) :
    ((l.1.symm t : Time) : ℝ) ≤ Real.exp C * (t : ℝ) := by
  have hg : (gamma l.1.symm).toReal ≤ C := by
    rw [gamma_symm]
    simpa only [ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hl := (lipschitzWith_of_gamma l.1.symm (by rw [gamma_symm]; exact ne_of_lt l.2.2)).dist_le_mul t 0
  have ht : 0 ≤ (t : ℝ) := t.2
  have hs : 0 ≤ ((l.1.symm t : Time) : ℝ) := (l.1.symm t).2
  simp only [LambdaPrime.map_zero, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
    abs_of_nonneg hs, abs_of_nonneg ht] at hl
  exact hl.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hg) ht)

/-- Summable time-change distortions and aligned discrepancies yield a
locally uniform limit of the transformed paths. -/
theorem exists_tendstoUniformlyOn_transformedPaths {E : Type*} [MetricSpace E]
    [CompleteSpace E] (x : ℕ → D E) (l : ℕ → Lambda)
    (hg : (∑' n, gamma (l n).1) ≠ ∞)
    (hd : Summable fun n =>
      (integratedDiscrepancy (x n) (x (n + 1)) (l n).1.symm).toReal) :
    ∃ z : D E, ∀ T : Time,
      TendstoUniformlyOn (fun n => ((x n).comp (changePrefix l n).1.symm).1)
        z.1 atTop (Iic T) := by
  suffices h : ∃ z : D E,
      (∀ T : Time, TendstoUniformlyOn
        (fun n => ((x n).comp (changePrefix l n).1.symm).1) z.1 atTop (Iic T)) ∧
      Tendsto (fun n => (x n).comp (changePrefix l n).1.symm) atTop (𝓝 z) by
    obtain ⟨z, hz, _⟩ := h
    exact ⟨z, hz⟩
  apply exists_tendsto_of_uniformCauchySeqOn_paths
  intro T
  let C : ℝ := (∑' n, gamma (l n).1).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hbound (n : ℕ) : gamma (changePrefix l n).1 ≤ ENNReal.ofReal C := by
    rw [show ENNReal.ofReal C = ∑' n, gamma (l n).1 from ENNReal.ofReal_toReal hg]
    exact (gamma_changePrefix_le l n).trans (ENNReal.sum_le_tsum _)
  let U : Time := ⟨Real.exp C * (T : ℝ), mul_nonneg (Real.exp_pos C).le T.2⟩
  have htime (n : ℕ) (t : Time) (ht : t ≤ T) :
      (changePrefix l n).1.symm t ≤ U := by
    change (((changePrefix l n).1.symm t : Time) : ℝ) ≤ (U : ℝ)
    exact (coe_symm_le_exp_mul _ hC (hbound n) t).trans
      (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ T from ht) (Real.exp_pos C).le)
  have hsmall : ∀ᶠ n in atTop,
      (integratedDiscrepancy (x n) (x (n + 1)) (l n).1.symm).toReal <
        Real.exp (-(U : ℝ)) :=
    hd.tendsto_atTop_zero.eventually (Iio_mem_nhds (Real.exp_pos _))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  have hc : UniformCauchySeqOn
      (fun n => ((x (n + N)).comp (changePrefix l (n + N)).1.symm).1) atTop (Iic T) := by
    apply uniformCauchySeqOn_of_summable_dist
      (((summable_nat_add_iff N).mpr hd).mul_left (Real.exp (U : ℝ)))
    intro n t ht
    have h1 := htime (n + N) t (mem_Iic.mp ht)
    have h2 := htime (n + N + 1) t (mem_Iic.mp ht)
    have ha := dist_le_of_integratedDiscrepancy_lt (x (n + N)) (x (n + N + 1))
      (l (n + N)).1.symm U ((changePrefix l (n + N)).1.symm t) h1 ?_ (hN _ (by omega))
    · simpa only [D.comp, Function.comp_apply, Nat.add_right_comm n 1 N,
        changePrefix, Lambda.trans, OrderIso.symm_trans, OrderIso.trans_apply] using ha
    · simpa only [changePrefix, Lambda.trans, OrderIso.symm_trans, OrderIso.trans_apply] using h2
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.uniformCauchySeqOn_iff.mp hc ε hε
  refine ⟨M + N, fun m hm n hn t ht => ?_⟩
  have hm' : N ≤ m := by omega
  have hn' : N ≤ n := by omega
  have hmM : M ≤ m - N := by omega
  have hnM : M ≤ n - N := by omega
  simpa only [Nat.sub_add_cancel hm', Nat.sub_add_cancel hn'] using
    hM (m - N) hmM (n - N) hnM t ht

end

end LatticeProb.Cadlag.HalfLine
