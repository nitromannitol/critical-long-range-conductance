import LongRange.Support.Prob.Cadlag.HalfLine.Restriction

/-!
# Uniform convergence at continuous paths

Skorokhod convergence to a continuous half-line path is uniform on every bounded interval.
-/

namespace LongRangeHeat

open Set Filter LatticeProb.Cadlag LatticeProb.Cadlag.HalfLine
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- On a compact interval, a path near a continuous path in J1 is uniformly near it. -/
theorem exists_uniform_control {T : ℝ} (x : C(Icc (0 : ℝ) T, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : LatticeProb.Cadlag.D T E,
      skorokhodDist y (LatticeProb.Cadlag.ofContinuous x) < δ →
        ∀ t, dist (y.1 t) (x t) < ε := by
  obtain ⟨η, hη, hx⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous x.continuous) (ε / 2) (half_pos hε)
  let δ := min η (ε / 4) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by
    have := min_le_left η (ε / 4)
    dsimp [δ]
    linarith
  have hδε : δ < ε / 4 := by
    have := min_le_right η (ε / 4)
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro y hy t
  obtain ⟨r, ⟨_, l, hl, hyx⟩, hr⟩ := exists_admissibleBounds_lt hy
  have ht : dist (l.symm t) t < η := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    have htime := hl (l.symm t)
    rw [l.apply_symm_apply] at htime
    exact htime.trans_lt (hr.trans hδη)
  have hsp : dist (y.1 t) (x (l.symm t)) ≤ r := by
    simpa only [LatticeProb.Cadlag.ofContinuous_apply, l.apply_symm_apply, dist_eq_norm] using
      hyx (l.symm t)
  have hc := hx ht
  have htriangle := dist_triangle (y.1 t) (x (l.symm t)) (x t)
  linarith

/-- Convergence in the half-line Skorokhod topology to a continuous path is uniform on
any closed bounded interval. -/
theorem eventually_uniform_of_tendsto {x : ℕ → LatticeProb.Cadlag.HalfLine.D E}
    {y : LatticeProb.Cadlag.HalfLine.D E} (hy : Continuous y.1)
    (h : Tendsto x atTop (𝓝 y)) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ≤ T, dist ((x n).1 t) (y.1 t) < ε := by
  let U : ℝ := (T : ℝ) + 1
  have hU : 0 < U := by dsimp [U]; positivity
  let z : C(Icc (0 : ℝ) U, E) := ⟨y.1 ∘ intervalTime, hy.comp (continuous_intervalTime U)⟩
  obtain ⟨δ, hδ, hcontrol⟩ := exists_uniform_control z hε
  have hrestrict : Tendsto (fun n => restrict U (x n)) atTop (𝓝 (restrict U y)) :=
    (continuousAt_restrict hU hy.continuousAt).tendsto.comp h
  have hz : restrict U y = LatticeProb.Cadlag.ofContinuous z := by
    apply Subtype.ext
    rfl
  rw [hz] at hrestrict
  have hdist := (Metric.tendsto_nhds.mp hrestrict) δ hδ
  filter_upwards [hdist] with n hn t ht
  let s : Icc (0 : ℝ) U := ⟨t, t.2, by
    dsimp [U]
    have := NNReal.coe_le_coe.mpr ht
    linarith⟩
  have hs := hcontrol (restrict U (x n)) hn s
  exact hs

/-- Evaluation at a converging sequence of times is continuous when the limiting path is. -/
theorem tendsto_varying_eval {x : ℕ → LatticeProb.Cadlag.HalfLine.D E}
    {y : LatticeProb.Cadlag.HalfLine.D E} (hy : Continuous y.1)
    (h : Tendsto x atTop (𝓝 y)) {t : ℝ≥0} {u : ℕ → ℝ≥0}
    (hu : Tendsto u atTop (𝓝 t)) :
    Tendsto (fun n => (x n).1 (u n)) atTop (𝓝 (y.1 t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have huB : ∀ᶠ n in atTop, u n ≤ t + 1 :=
    (hu.eventually (Iio_mem_nhds (show t < t + 1 by simp))).mono fun _ hn => hn.le
  have h1 := eventually_uniform_of_tendsto hy h (t + 1) (half_pos hε)
  have h2 := Metric.tendsto_nhds.mp ((hy.continuousAt.tendsto).comp hu) (ε / 2) (half_pos hε)
  filter_upwards [huB, h1, h2] with n hn hn1 hn2
  dsimp only [Function.comp_def] at hn2
  have htri := dist_triangle ((x n).1 (u n)) (y.1 (u n)) (y.1 t)
  have := hn1 (u n) hn
  linarith

end
end LongRangeHeat
