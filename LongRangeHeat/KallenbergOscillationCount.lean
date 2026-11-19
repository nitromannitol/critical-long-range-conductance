import LongRangeHeat.KallenbergHitEstimate
import LongRangeHeat.KallenbergHolder

/-!
# Number of path oscillations

The exponential bound for sums of waiting times bounds the probability of
many oscillations before a fixed horizon.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal

variable {E Ω : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

/-- A uniform short-gap bound controls the probability of many oscillations. -/
theorem measure_oscillationTime_lt_le
    (P : ProbabilityMeasure Ω) (Y : Ω → D E) (hY : Measurable Y)
    (T t : Time) (ht : t < T) (ζ c : ℝ) (hc : 0 < c) (p : ℝ≥0∞)
    (hgap : ∀ k, (P : Measure Ω) {w | oscillationTime Y T ζ (k + 1) w < T ∧
      (oscillationTime Y T ζ (k + 1) w : ℝ) ≤
        (oscillationTime Y T ζ k w : ℝ) + c} ≤ p)
    {m : ℕ} (hm : 0 < m) :
    (P : Measure Ω) {w | oscillationTime Y T ζ m w < t} ≤
      ENNReal.ofReal (Real.exp (t : ℝ)) *
        (ENNReal.ofReal (Real.exp (-(m : ℝ) * c)) + p) := by
  classical
  let α : ℕ → Ω → Time := oscillationTime Y T ζ
  have hα (k : ℕ) : Measurable (α k) :=
    (weakNaturalStopping_oscillationTime Y T ζ k).measurable hY
  have hmono (w : Ω) : Monotone (fun k => α k w) :=
    monotone_nat_of_le_succ (fun k => oscillationTime_le_succ Y T ζ k w)
  let ξ : Fin m → Ω → ℝ := fun i w =>
    if α (i.val + 1) w < T then (α (i.val + 1) w : ℝ) - (α i.val w : ℝ) else c
  have hξ (i : Fin m) : Measurable (ξ i) := by
    dsimp only [ξ]
    exact Measurable.ite (measurableSet_lt (hα (i.val + 1)) measurable_const)
      ((NNReal.continuous_coe.measurable.comp (hα (i.val + 1))).sub
        (NNReal.continuous_coe.measurable.comp (hα i.val))) measurable_const
  have hξ0 (i : Fin m) (w : Ω) : 0 ≤ ξ i w := by
    dsimp only [ξ]
    split
    · have hh : (α i.val w : ℝ) ≤ (α (i.val + 1) w : ℝ) := by
        exact_mod_cast hmono w (Nat.le_succ i.val)
      linarith
    · exact hc.le
  have hp (i : Fin m) : (P : Measure Ω) {w | ξ i w < c} ≤ p := by
    refine (measure_mono ?_).trans (hgap i.val)
    intro w hw
    change (if α (i.val + 1) w < T then
      (α (i.val + 1) w : ℝ) - (α i.val w : ℝ) else c) < c at hw
    split at hw
    next hlt => exact ⟨hlt, by linarith⟩
    next => exact (lt_irrefl c hw).elim
  have hsub : {w | α m w < t} ⊆ {w | ∑ i, ξ i w ≤ (t : ℝ)} := by
    intro w hw
    have hu (i : Fin m) : α (i.val + 1) w < T := by
      exact (hmono w (Nat.succ_le_of_lt i.isLt)).trans_lt (hw.trans ht)
    have hsum : (∑ i : Fin m, ξ i w) = (α m w : ℝ) := by
      have hξeq : (∑ i : Fin m, ξ i w) =
          ∑ i : Fin m, ((α (i.val + 1) w : ℝ) - (α i.val w : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [ξ, ite_eq_left (hu i)]
      calc
        _ = ∑ i : Fin m, ((α (i.val + 1) w : ℝ) - (α i.val w : ℝ)) := hξeq
        _ = ∑ i ∈ Finset.range m, ((α (i + 1) w : ℝ) - (α i w : ℝ)) :=
          Fin.sum_univ_eq_sum_range (fun j => (α (j + 1) w : ℝ) - (α j w : ℝ)) m
        _ = _ := by
          simpa only [α, oscillationTime, NNReal.coe_zero, sub_zero] using
            (Finset.sum_range_sub (fun j => (α j w : ℝ)) m)
    change (∑ i, ξ i w) ≤ (t : ℝ)
    rw [hsum]
    exact (NNReal.coe_lt_coe.mpr hw).le
  exact (measure_mono hsub).trans (measure_sum_le_of_lower_tail
    (P : Measure Ω) hm ξ hξ hξ0 (t : ℝ) c p hp)


variable {Ωs : ℕ → Type} [m : ∀ n, MeasurableSpace (Ωs n)]

/-- Uniform control of short oscillation gaps makes the number of oscillations
before a fixed time tight. -/
theorem exists_eventually_measure_oscillationTime_lt
    (P : ∀ n, ProbabilityMeasure (Ωs n)) (Y : ∀ n, Ωs n → D E)
    (hY : ∀ n, Measurable (Y n)) (T t : Time) (ht : t < T) (ζ : ℝ)
    (hgap : ∀ p : ℝ≥0∞, 0 < p → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ k : ℕ,
        (P n : Measure (Ωs n)) {w | oscillationTime (Y n) T ζ (k + 1) w < T ∧
          (oscillationTime (Y n) T ζ (k + 1) w : ℝ) ≤
            (oscillationTime (Y n) T ζ k w : ℝ) + δ} < p)
    {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ k N : ℕ, ∀ n, N ≤ n →
      (P n : Measure (Ωs n)) {w | oscillationTime (Y n) T ζ k w < t} < β := by
  obtain ⟨r, _, hr', hrβ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hβ
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr'
  let C : ℝ := Real.exp (t : ℝ)
  have hC : 0 < C := Real.exp_pos _
  let q : ℝ := r / (4 * C)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨δ, hδ, N, hN⟩ := hgap (ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq)
  let c : ℝ := δ / 2
  have hc : 0 < c := half_pos hδ
  have harg : Tendsto (fun k : ℕ => -(k : ℝ) * c) atTop atBot := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
      |>.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)
    simpa only [neg_mul, mul_neg, mul_comm] using hh
  have hlim : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ) * c)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  obtain ⟨k, hk, hkq⟩ := ((eventually_ge_atTop 1).and
    (hlim.eventually (Iio_mem_nhds hq))).exists
  refine ⟨k, N, ?_⟩
  intro n hn
  have hgap' (j : ℕ) : (P n : Measure (Ωs n))
      {w | oscillationTime (Y n) T ζ (j + 1) w < T ∧
        (oscillationTime (Y n) T ζ (j + 1) w : ℝ) ≤
          (oscillationTime (Y n) T ζ j w : ℝ) + c} ≤ ENNReal.ofReal q := by
    refine (measure_mono ?_).trans (hN n hn j).le
    intro w hw
    exact ⟨hw.1, by dsimp [c] at hw; linarith [hw.2]⟩
  have hcount := measure_oscillationTime_lt_le (P n) (Y n) (hY n) T t ht ζ c hc
    (ENNReal.ofReal q) hgap' hk
  calc
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(k : ℝ) * c)) + ENNReal.ofReal q) := hcount
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal q + ENNReal.ofReal q) := by
      gcongr
    _ = ENNReal.ofReal (r / 2) := by
      rw [← ENNReal.ofReal_add hq.le hq.le, ← ENNReal.ofReal_mul hC.le]
      congr 1
      dsimp [q]
      field_simp
      ring
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)
    _ < β := hrβ


/-- Aldous' sequential condition controls the number of oscillations before a
fixed time. -/
theorem exists_eventually_measure_oscillationTime_lt_of_optional_increment
    (P : ∀ n, ProbabilityMeasure (Ωs n)) (Y : ∀ n, Ωs n → D E)
    (hY : ∀ n, Measurable (Y n)) (T t : Time) (hT : 0 < T) (ht : t < T)
    {ζ : ℝ} (hζ : 0 < ζ)
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : (n : ℕ) → Ωs n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ωs n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ k N : ℕ, ∀ n, N ≤ n →
      (P n : Measure (Ωs n)) {w | oscillationTime (Y n) T ζ k w < t} < β := by
  apply exists_eventually_measure_oscillationTime_lt P Y hY T t ht ζ ?_ hβ
  intro p hp
  apply exists_pos_eventually_oscillation_gap_le P Y hY hζ ?_ hp
  intro ε hε
  exact exists_pos_eventually_uniform_weak_paired_expectation P Y hY h
    (show 0 < (T : ℝ) by exact_mod_cast hT) hε

end LatticeProb.Cadlag.HalfLine
