import LongRangeHeat.KallenbergStopping

/-!
# Uniform control at optional times

Sequential stopped-increment convergence gives a uniform tail bound over all
bounded stopping times and small deterministic increments.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory External
open scoped Topology ENNReal

variable {E : Type} [MetricSpace E] [MeasurableSpace E]
  {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]

/-- A bounded stopping time for the raw natural filtration. -/
def naturalStopping {Ω : Type} (Y : Ω → D E) (H : ℝ) (τ : Ω → Time) : Prop :=
  (∀ w, (τ w : ℝ) ≤ H) ∧
    ∀ t : Time, MeasurableSet[naturalSigma Y t] {w | τ w ≤ t}

/-- Zero is a stopping time for every nonnegative horizon. -/
theorem naturalStopping_zero {Ω : Type} (Y : Ω → D E) {H : ℝ} (hH : 0 ≤ H) :
    naturalStopping Y H (fun _ => 0) :=
  ⟨fun _ => hH, fun t => by simp only [zero_le, Set.ofPred_true, MeasurableSet.univ]⟩

/-- Full-sequence convergence is inherited by bounded stopping times along a subsequence. -/
theorem tendsto_subsequence_optional_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    {H η : ℝ} (hH : 0 < H)
    (h : ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (τ : (k : ℕ) → Ω (φ k) → Time)
    (hτ : ∀ k, naturalStopping (Y (φ k)) H (τ k))
    (u : ℕ → Time) (hu : Tendsto (fun k => (u k : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun k => (P (φ k) : Measure (Ω (φ k)))
      {w | η ≤ dist ((Y (φ k) w).1 (τ k w + u k)) ((Y (φ k) w).1 (τ k w))})
      atTop (𝓝 0) := by
  classical
  let τ' : (n : ℕ) → Ω n → Time := fun n =>
    if hn : n ∈ Set.range φ then hn.choose_spec ▸ τ hn.choose else fun _ => 0
  let u' : ℕ → Time := fun n =>
    if hn : n ∈ Set.range φ then u hn.choose else 0
  have hcast {i j : ℕ} (e : i = j) (t : Ω i → Time)
      (ht : naturalStopping (Y i) H t) : naturalStopping (Y j) H (e ▸ t) := by
    cases e
    exact ht
  have htransport (a b : ℕ) (e : φ a = φ b) (hab : a = b) :
      (e ▸ τ a) = τ b := by
    subst b
    rfl
  have hτ' (n : ℕ) : naturalStopping (Y n) H (τ' n) := by
    dsimp [τ']
    split
    next hn => exact hcast hn.choose_spec _ (hτ hn.choose)
    next => exact naturalStopping_zero _ hH.le
  have hτ'φ (k : ℕ) : τ' (φ k) = τ k := by
    dsimp [τ']
    split
    next hn => exact htransport _ _ hn.choose_spec (hφ.injective hn.choose_spec)
    next hn => exact (hn ⟨k, rfl⟩).elim
  have hu'φ (k : ℕ) : u' (φ k) = u k := by
    dsimp [u']
    split
    next hn => rw [hφ.injective hn.choose_spec]
    next hn => exact (hn ⟨k, rfl⟩).elim
  have hu' : Tendsto (fun n => (u' n : ℝ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hu ε hε
    refine ⟨φ K, fun n hn => ?_⟩
    dsimp [u']
    split
    next hn' =>
      apply hK
      apply hφ.le_iff_le.mp
      rw [hn'.choose_spec]
      exact hn
    next => simpa using hε
  have hh := (h τ' hτ' u' hu').comp hφ.tendsto_atTop
  change Tendsto (fun k => (P (φ k) : Measure (Ω (φ k)))
    {w | η ≤ dist ((Y (φ k) w).1 (τ' (φ k) w + u' (φ k)))
      ((Y (φ k) w).1 (τ' (φ k) w))}) atTop (𝓝 0) at hh
  simpa only [hτ'φ, hu'φ] using hh


/-- Sequential convergence at bounded optional times yields a uniform late-index
bound over all such times and sufficiently small nonnegative increments. -/
theorem exists_pos_eventually_uniform_optional_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    {H η : ℝ} (hH : 0 < H)
    (h : ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ τ : Ω n → Time, naturalStopping (Y n) H τ →
      ∀ u : Time, (u : ℝ) ≤ δ →
        (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ w + u)) ((Y n w).1 (τ w))} < ε := by
  let S (n : ℕ) := (Ω n → Time) × Time
  let scale : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hscale : Tendsto scale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let q (k n : ℕ) (s : S n) : Prop :=
    naturalStopping (Y n) H s.1 ∧ (s.2 : ℝ) ≤ scale k
  let p (n : ℕ) (s : S n) : ℝ≥0∞ :=
    (P n : Measure (Ω n))
      {w | η ≤ dist ((Y n w).1 (s.1 w + s.2)) ((Y n w).1 (s.1 w))}
  obtain ⟨k, N, hN⟩ := exists_eventually_uniform_of_tendsto_admissible_diagonal q p
    (fun φ hφ σ hσ => by
      have hu : Tendsto (fun k => ((σ k).2 : ℝ)) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
          (fun k => (σ k).2.2) (fun k => (hσ k).2)
      exact tendsto_subsequence_optional_increment P Y hH h φ hφ
        (fun k => (σ k).1) (fun k => (hσ k).1) (fun k => (σ k).2) hu) hε
  refine ⟨scale k, by dsimp [scale]; positivity, N, ?_⟩
  intro n hn τ hτ u hu
  exact hN n hn (τ, u) ⟨hτ, hu⟩


/-- Positive time steps suffice for the uniform optional-time increment bound. -/
theorem exists_pos_eventually_uniform_optional_increment_of_positive
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    {H η : ℝ} (hH : 0 < H) (hη : 0 < η)
    (h : ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ τ : Ω n → Time, naturalStopping (Y n) H τ →
      ∀ u : Time, (u : ℝ) ≤ δ →
        (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ w + u)) ((Y n w).1 (τ w))} < ε := by
  apply exists_pos_eventually_uniform_optional_increment P Y hH ?_ hε
  intro τ hτ u hu
  let v : ℕ → Time := fun n => if u n = 0 then 1 / (n + 1 : Time) else u n
  have hvpos (n : ℕ) : 0 < v n := by
    dsimp [v]
    split
    · positivity
    · exact pos_iff_ne_zero.mpr ‹u n ≠ 0›
  have hv : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => (u n : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [add_zero] using hu.add tendsto_one_div_add_atTop_nhds_zero_nat
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · intro n
      exact (v n).2
    · intro n
      dsimp [v]
      split
      · simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
        linarith [(u n).2]
      · have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
        linarith
  have hlim := h τ hτ v hvpos hv
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε'
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hlim ε hε'] with n hn
  by_cases hz : u n = 0
  · have hempty : {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, hz, add_zero, dist_self, Set.mem_empty_iff_false,
        iff_false, not_le]
      exact hη
    rw [hempty, measure_empty]
    exact zero_le
  · simpa only [v, ite_eq_right hz] using hn


/-- Sequential optional-time convergence implies uniform control of the expected
truncated increment. -/
theorem exists_pos_eventually_uniform_optional_expectation
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    {H : ℝ} (hH : 0 < H)
    (h : ∀ η : ℝ, 0 < η → ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ τ : Ω n → Time, naturalStopping (Y n) H τ →
      ∀ u : Time, (u : ℝ) ≤ δ →
        (∫⁻ w, ENNReal.ofReal (min (dist ((Y n w).1 (τ w + u))
          ((Y n w).1 (τ w))) 1) ∂(P n : Measure (Ω n))) < ε := by
  obtain ⟨r, _, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr2 : 0 < r / 2 := half_pos (ENNReal.ofReal_pos.mp hrpos)
  obtain ⟨δ, hδ, N, hN⟩ :=
    exists_pos_eventually_uniform_optional_increment_of_positive P Y hH hr2 (h (r / 2) hr2)
      (ENNReal.ofReal_pos.mpr hr2)
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn τ hτ u hu
  have htail := hN n hn τ hτ u hu
  calc
    _ ≤ ENNReal.ofReal (r / 2) +
        (P n : Measure (Ω n))
          {w | r / 2 ≤ dist ((Y n w).1 (τ w + u)) ((Y n w).1 (τ w))} :=
      lintegral_truncated_dist_le (P n) (fun w => (Y n w).1 (τ w + u))
        (fun w => (Y n w).1 (τ w)) (r / 2)
    _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
      ENNReal.add_lt_add_left ENNReal.ofReal_ne_top htail
    _ = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add hr2.le hr2.le]
      congr 1
      ring
    _ < ε := hrε

end LatticeProb.Cadlag.HalfLine
