import LongRange.Support.Prob.Cadlag.HalfLine.Paths
import LongRange.Support.Prob.Cadlag.HalfLine.Convergence
import LongRange.Support.Prob.Cadlag.HalfLine.Metric
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Continuity under time changes

Small time-change distortions preserve half-line càdlàg paths in the
Skorokhod metric.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- Truncation at a point above the smaller endpoint cannot increase the
distance from the other endpoint. -/
theorem dist_min_le_dist_of_min_le (a b c : Time) (h : min b c ≤ a) :
    dist (min a b) c ≤ dist b c := by
  have hr : min (b : ℝ) (c : ℝ) ≤ (a : ℝ) := h
  simp only [NNReal.dist_eq, NNReal.coe_min, abs_le]
  simp only [min_def] at *
  split_ifs at * <;> constructor <;> linarith [le_abs_self ((b : ℝ) - c),
    neg_le_abs ((b : ℝ) - c)]

/-- At continuity points, the stopped discrepancy of a time-changed path
vanishes as the distortion tends to zero. -/
theorem tendsto_discrepancy_comp_self {E : Type*} [MetricSpace E] (y : D E)
    (l : ℕ → Lambda) (hg : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0))
    (u : Time) (hu : ContinuousAt y.1 u) :
    Tendsto (fun n => discrepancy (y.comp (l n).1) y (l n).1 u) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · filter_upwards [] with n
    rw [htop]
    exact le_top
  let e : ℝ := ε.toReal / 4
  have he : 0 < e := by
    dsimp only [e]
    exact div_pos (ENNReal.toReal_pos (ne_of_gt hε) htop) (by norm_num)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hu e he
  have htime := Metric.tendsto_nhds.mp (tendsto_timeChange_of_gamma hg u) δ hδ
  filter_upwards [htime] with n hn
  unfold discrepancy
  apply iSup_le
  intro t
  change q (y.1 ((l n).1 (min t u))) (y.1 (min ((l n).1 t) u)) ≤ ε
  rw [show min t u = t ⊓ u from rfl, OrderIso.map_inf]; change q (y.1 (min ((l n).1 t) ((l n).1 u))) (y.1 (min ((l n).1 t) u)) ≤ ε
  by_cases ht : (l n).1 t ≤ min ((l n).1 u) u
  · rw [min_eq_left (ht.trans (min_le_left _ _)),
      min_eq_left (ht.trans (min_le_right _ _)), q_self]
    exact zero_le
  · have ht' : min ((l n).1 u) u ≤ (l n).1 t := le_of_not_ge ht
    have h1 : dist (min ((l n).1 t) ((l n).1 u)) u < δ :=
      (dist_min_le_dist_of_min_le _ _ _ ht').trans_lt hn
    have h2 : dist (min ((l n).1 t) u) u < δ := by
      have hb : dist (min ((l n).1 t) u) u ≤ dist ((l n).1 u) u := by
        rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_min]
        have hr : min (((l n).1 u : Time) : ℝ) (u : ℝ) ≤ (((l n).1 t : Time) : ℝ) := ht'
        rw [abs_of_nonpos (sub_nonpos.mpr (min_le_right _ _))]
        have habs := neg_le_abs ((((l n).1 u : Time) : ℝ) - u)
        simp only [min_def] at hr ⊢
        split_ifs at hr ⊢ <;> linarith [abs_nonneg ((((l n).1 u : Time) : ℝ) - u), le_abs_self ((((l n).1 u : Time) : ℝ) - u)]
      exact hb.trans_lt hn
    have hd : dist (y.1 (min ((l n).1 t) ((l n).1 u)))
        (y.1 (min ((l n).1 t) u)) ≤ 2 * e := by
      have htri := dist_triangle (y.1 (min ((l n).1 t) ((l n).1 u))) (y.1 u)
        (y.1 (min ((l n).1 t) u))
      have ha := hcont h1
      have hb := hcont h2
      rw [dist_comm (y.1 u)] at htri
      linarith
    calc
      _ ≤ ENNReal.ofReal (2 * e) := (min_le_left _ _).trans (by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hd)
      _ ≤ ε := by
        rw [← ENNReal.ofReal_toReal htop]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [e]
        linarith [ENNReal.toReal_nonneg (a := ε)]

/-- Small distortions make the integrated discrepancy of a time-changed path
vanish. -/
theorem tendsto_integratedDiscrepancy_comp_self {E : Type*} [MetricSpace E] (y : D E)
    (l : ℕ → Lambda) (hg : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0)) :
    Tendsto (fun n => integratedDiscrepancy (y.comp (l n).1) y (l n).1)
      atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun n u => ENNReal.ofReal (Real.exp (-u)) *
    discrepancy (y.comp (l n).1) y (l n).1 u.toNNReal
  let B : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-u))
  have hmeas (n : ℕ) : Measurable (F n) :=
    measurable_integratedDiscrepancy_integrand _ _ _
  have hbound (n : ℕ) : F n ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] B := by
    filter_upwards [] with u
    exact (mul_le_mul_right (discrepancy_le_one _ _ _ _) _).trans_eq (mul_one _)
  have hfin : (∫⁻ u : ℝ in Ioi 0, B u) ≠ ∞ := by
    rw [exponential_mass]
    exact ENNReal.one_ne_top
  have hae := (y.2.countable_discontinuities.image (fun s : Time => (s : ℝ))).ae_notMem
    volume
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n => F n u) atTop (𝓝 0) := by
    filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with u hu hu0
    have hc : ContinuousAt y.1 u.toNNReal := by
      by_contra hnot
      exact hu ⟨u.toNNReal, hnot, Real.coe_toNNReal u hu0.le⟩
    simpa only [F, mul_zero] using
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (-u)))
        (tendsto_discrepancy_comp_self y l hg u.toNNReal hc) (Or.inr ENNReal.ofReal_ne_top)
  have hd := tendsto_lintegral_of_dominated_convergence B hmeas hbound hfin hlim
  simpa only [F, integratedDiscrepancy, lintegral_zero] using hd

/-- Composition with time changes whose distortions vanish converges to the
original path in the half-line Skorokhod metric. -/
theorem tendsto_comp_of_tendsto_gamma {E : Type*} [MetricSpace E] (y : D E)
    (l : ℕ → Lambda) (hg : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0)) :
    Tendsto (fun n => y.comp (l n).1) atTop (𝓝 y) := by
  have hi := tendsto_integratedDiscrepancy_comp_self y l hg
  have hm : Tendsto (fun n => max (gamma (l n).1)
      (integratedDiscrepancy (y.comp (l n).1) y (l n).1)) atTop (𝓝 0) := by
    simpa only [max_self] using hg.max hi
  have hd : Tendsto (fun n => skorohodDistanceExtended (y.comp (l n).1) y)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun _ => bot_le) (fun n => iInf_le _ (l n))
  apply Metric.tendsto_nhds.mpr
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hd
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hr ε hε] with n hn
  simpa only [Function.comp_def, ENNReal.toReal_zero, Real.dist_eq, sub_zero,
    abs_of_nonneg ENNReal.toReal_nonneg, dist_eq_skorohodDistance, skorohodDistance] using hn

end

end LatticeProb.Cadlag.HalfLine
