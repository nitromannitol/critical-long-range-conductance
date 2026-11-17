import LongRangeHeat.PathConvergence
import LongRangeHeat.PathScaling

/-!
# Convergence under space and time scaling

Space-time scalings converge uniformly on bounded intervals at continuous limiting paths.
-/

namespace LongRangeHeat

open Set Filter MeasureTheory LatticeProb.Cadlag.HalfLine
open scoped Topology NNReal ENNReal

noncomputable section

/-- Jointly converging scaling parameters and paths give locally uniform convergence at a
continuous limiting path. -/
theorem eventually_uniform_scaledPath {d : ℕ} {x : ℕ → PathSpace d} {y : PathSpace d}
    (hy : Continuous y.1) (hx : Tendsto x atTop (𝓝 y))
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    {c : ℕ → {c : ℝ≥0 // 0 < c}} (hc : Tendsto c atTop (𝓝 ⟨1, zero_lt_one⟩))
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ≤ T, dist ((scaledPath (b n) (c n) (x n)).1 t) (B • y.1 t) < ε := by
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, ∃ t : ℝ≥0, t ≤ T ∧
      ε ≤ dist ((scaledPath (b n) (c n) (x n)).1 t) (B • y.1 t) := by
    simpa only [not_eventually, not_forall, not_lt, exists_prop] using hbad
  obtain ⟨k, hk, hbad⟩ := extraction_of_frequently_atTop hfreq
  choose t ht hdist using hbad
  have hmem : ∀ n, t n ∈ Icc (0 : ℝ≥0) T := fun n => ⟨zero_le, ht n⟩
  obtain ⟨v, hv, l, hl, hlim⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).isSeqCompact
    (fun n => hmem n)
  have hkl : Tendsto (fun n => k (l n)) atTop atTop := hk.tendsto_atTop.comp hl.tendsto_atTop
  have hc' : Tendsto (fun n => (c (k (l n))).1) atTop (𝓝 (1 : ℝ≥0)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hc.comp hkl)
  have htime : Tendsto (fun n => (c (k (l n))).1 * t (l n)) atTop (𝓝 v) := by
    simpa only [one_mul, Function.comp_def] using hc'.mul hlim
  have hvalue := tendsto_varying_eval hy (hx.comp hkl) htime
  have hscaled := (hb.comp hkl).smul hvalue
  have hytime := hy.continuousAt.tendsto.comp hlim
  have htarget := tendsto_const_nhds.smul hytime (c := B)
  have hzero : Tendsto (fun n => dist (b (k (l n)) • (x (k (l n))).1
      ((c (k (l n))).1 * t (l n))) (B • y.1 (t (l n)))) atTop (𝓝 0) := by
    simpa only [dist_self, Function.comp_def] using hscaled.dist htarget
  have hsmall := (Metric.tendsto_nhds.mp hzero) ε hε
  obtain ⟨n, hn⟩ := hsmall.exists
  have hfail := hdist (l n)
  change ε ≤ dist (b (k (l n)) • (x (k (l n))).1
    ((c (k (l n))).1 * t (l n))) (B • y.1 (t (l n))) at hfail
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hn
  exact (not_lt_of_ge hfail) hn

/-- Space-time scaling is sequentially continuous at continuous paths when the limiting clock
factor is one. -/
theorem tendsto_scaledPath {d : ℕ} {x : ℕ → PathSpace d} {y : PathSpace d}
    (hy : Continuous y.1) (hx : Tendsto x atTop (𝓝 y))
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    {c : ℕ → {c : ℝ≥0 // 0 < c}} (hc : Tendsto c atTop (𝓝 ⟨1, zero_lt_one⟩)) :
    Tendsto (fun n => scaledPath (b n) (c n) (x n)) atTop
      (𝓝 (scaledPath B ⟨1, zero_lt_one⟩ y)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hhalf))
  let M : Time := ⟨max R 0, le_max_right _ _⟩
  have htail : Real.exp (-(M : ℝ)) < ε / 2 := hR _ (le_max_left _ _)
  filter_upwards [eventually_uniform_scaledPath hy hx hb hc M hhalf] with n hn
  have hs : (⨆ t ≤ M, q ((scaledPath (b n) (c n) (x n)).1 t)
      ((scaledPath B ⟨1, zero_lt_one⟩ y).1 t)) ≤ ENNReal.ofReal (ε / 2) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply (min_le_left _ _).trans
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hpoint := (hn t ht).le
    simpa only [scaledPath, transformPath_apply, dilation, OrderIso.mulLeft₀_apply, one_mul]
      using hpoint
  have hbound := dist_le_uniform (scaledPath (b n) (c n) (x n))
    (scaledPath B ⟨1, zero_lt_one⟩ y) M
  have hsreal := ENNReal.toReal_le_of_le_ofReal hhalf.le hs
  exact hbound.trans_lt (by linarith)

/-- Joint scaling is continuous at every continuous path with unit clock factor. -/
theorem continuousAt_scaledPath {d : ℕ} (B : ℝ) (y : PathSpace d) (hy : Continuous y.1) :
    ContinuousAt (fun p : (ℝ × {c : ℝ≥0 // 0 < c}) × PathSpace d =>
      scaledPath p.1.1 p.1.2 p.2) ((B, ⟨1, zero_lt_one⟩), y) := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro p hp
  exact tendsto_scaledPath hy (continuous_snd.continuousAt.tendsto.comp hp)
    (continuous_fst.continuousAt.tendsto.comp
      (continuous_fst.continuousAt.tendsto.comp hp))
    (continuous_snd.continuousAt.tendsto.comp
      (continuous_fst.continuousAt.tendsto.comp hp))

end
end LongRangeHeat
