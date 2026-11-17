import LongRange.Support.Prob.Cadlag.HalfLine.AldousHalfLine

/-!
# Stopping increments along vanishing time steps

A uniform stopping-increment condition implies convergence in probability along any
sequence of bounded discrete stopping times and deterministic time steps tending to zero.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory External
open scoped Topology ENNReal

/-- Sequential control of admissible choices gives a uniform bound for a sufficiently
small window and all sufficiently late indices. -/
theorem exists_eventually_uniform_of_tendsto_admissible_diagonal
    {S : ℕ → Type*} (q : (k n : ℕ) → S n → Prop) (p : (n : ℕ) → S n → ℝ≥0∞)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ σ : (k : ℕ) → S (φ k),
      (∀ k, q k (φ k) (σ k)) → Tendsto (fun k => p (φ k) (σ k)) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ k N : ℕ, ∀ n, N ≤ n → ∀ s : S n, q k n s → p n s < ε := by
  classical
  by_contra hc
  push Not at hc
  choose next hnext hwitness using hc
  let φ : ℕ → ℕ := fun k =>
    Nat.rec (next 0 0) (fun j previous => next (j + 1) (previous + 1)) k
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact lt_of_lt_of_le (Nat.lt_succ_self (φ k)) (hnext (k + 1) (φ k + 1))
  have hbad : ∀ k, ∃ s : S (φ k), q k (φ k) s ∧ ε ≤ p (φ k) s := by
    intro k
    cases k with
    | zero => exact hwitness 0 0
    | succ k => exact hwitness (k + 1) (φ k + 1)
  choose σ hσ using hbad
  have hlim := h φ hφ σ (fun k => (hσ k).1)
  obtain ⟨k, hk⟩ := (hlim.eventually (Iio_mem_nhds hε)).exists
  exact (not_lt_of_ge (hσ k).2) hk

variable {E : Type} [MetricSpace E] [MeasurableSpace E]
  {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]

/-- Stopping-increment convergence along every subsequence gives uniform control over
bounded discrete stopping times and sufficiently small deterministic increments. -/
theorem exists_pos_eventually_uniform_stopping_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    {H η : ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ τ : (k : ℕ) → Ω (φ k) → Time,
      (∀ k, discreteNaturalStopping (Y (φ k)) H (τ k)) →
      ∀ u : ℕ → Time, Tendsto (fun k => (u k : ℝ)) atTop (𝓝 0) →
        Tendsto (fun k => (P (φ k) : Measure (Ω (φ k)))
          {w | η ≤ dist ((Y (φ k) w).1 (τ k w + u k))
            ((Y (φ k) w).1 (τ k w))}) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ τ : Ω n → Time, discreteNaturalStopping (Y n) H τ →
      ∀ u : Time, (u : ℝ) ≤ δ →
        (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ w + u)) ((Y n w).1 (τ w))} < ε := by
  let S (n : ℕ) := (Ω n → Time) × Time
  let scale : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hscale : Tendsto scale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let q (k n : ℕ) (s : S n) : Prop :=
    discreteNaturalStopping (Y n) H s.1 ∧ (s.2 : ℝ) ≤ scale k
  let p (n : ℕ) (s : S n) : ℝ≥0∞ :=
    (P n : Measure (Ω n))
      {w | η ≤ dist ((Y n w).1 (s.1 w + s.2)) ((Y n w).1 (s.1 w))}
  obtain ⟨k, N, hN⟩ := exists_eventually_uniform_of_tendsto_admissible_diagonal q p
    (fun φ hφ σ hσ => by
      have hu : Tendsto (fun k => ((σ k).2 : ℝ)) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
          (fun k => (σ k).2.2) (fun k => (hσ k).2)
      exact h φ hφ (fun k => (σ k).1) (fun k => (hσ k).1)
        (fun k => (σ k).2) hu) hε
  refine ⟨scale k, by dsimp [scale]; positivity, N, ?_⟩
  intro n hn τ hτ u hu
  exact hN n hn (τ, u) ⟨hτ, hu⟩

/-- The full-sequence stopping-increment condition remains valid on subsequences. -/
theorem tendsto_subsequence_stopping_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    {H η : ℝ} (hH : 0 < H)
    (h : ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, discreteNaturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (τ : (k : ℕ) → Ω (φ k) → Time)
    (hτ : ∀ k, discreteNaturalStopping (Y (φ k)) H (τ k))
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
      (ht : discreteNaturalStopping (Y i) H t) :
      discreteNaturalStopping (Y j) H (e ▸ t) := by
    cases e
    exact ht
  have htransport (a b : ℕ) (e : φ a = φ b) (hab : a = b) :
      (e ▸ τ a) = τ b := by
    subst b
    rfl
  have hτ' (n : ℕ) : discreteNaturalStopping (Y n) H (τ' n) := by
    dsimp [τ']
    split
    next hn =>
      exact hcast hn.choose_spec _ (hτ hn.choose)
    next => exact discreteNaturalStopping_zero _ hH.le
  have hτ'φ (k : ℕ) : τ' (φ k) = τ k := by
    dsimp [τ']
    split
    next hn =>
      have heq : hn.choose = k := hφ.injective hn.choose_spec
      exact htransport _ _ hn.choose_spec heq
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

/-- Sequential stopped-increment convergence along every subsequence implies the
uniform stopping-increment condition. -/
theorem stoppingIncrementCondition_of_subsequence_stopping_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ τ : (k : ℕ) → Ω (φ k) → Time,
      (∀ k, discreteNaturalStopping (Y (φ k)) H (τ k)) →
      ∀ u : ℕ → Time, Tendsto (fun k => (u k : ℝ)) atTop (𝓝 0) →
        Tendsto (fun k => (P (φ k) : Measure (Ω (φ k)))
          {w | η ≤ dist ((Y (φ k) w).1 (τ k w + u k))
            ((Y (φ k) w).1 (τ k w))}) atTop (𝓝 0)) :
    stoppingIncrementCondition P Y := by
  intro H hH η hη τ hτ
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ :=
    exists_pos_eventually_uniform_stopping_increment P Y (h H hH η hη) hε
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with d hd
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  refine iSup_le fun u => iSup_le fun hu => ?_
  exact (hN n hn (τ n) (hτ n) u (hu.trans hd.le)).le

/-- Convergence of stopped increments along every admissible sequence implies the
uniform stopping-increment condition. -/
theorem stoppingIncrementCondition_of_stopping_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, discreteNaturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0)) :
    stoppingIncrementCondition P Y := by
  apply stoppingIncrementCondition_of_subsequence_stopping_increment P Y
  intro H hH η hη φ hφ τ hτ u hu
  exact tendsto_subsequence_stopping_increment P Y hH (h H hH η hη) φ hφ τ hτ u hu

/-- The uniform stopped-increment bound yields the sequential condition in
Kallenberg (2002), Lemma 16.12. -/
theorem tendsto_stopping_increment_of_stoppingIncrementCondition
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (h : stoppingIncrementCondition P Y) {H : ℝ} (hH : 0 < H)
    (τ : (n : ℕ) → Ω n → Time)
    (hτ : ∀ n, discreteNaturalStopping (Y n) H (τ n))
    (u : ℕ → Time) (hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (P n : Measure (Ω n))
      {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, _, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  obtain ⟨δ, hδ, N, hN⟩ :=
    exists_pos_eventually_stopping_increment_bound P Y h hH hη hrpos
  have huδ : ∀ᶠ n in atTop, (u n : ℝ) ≤ δ := (hu.eventually (Iio_mem_nhds hδ)).mono fun _ hn => hn.le
  filter_upwards [eventually_ge_atTop N, huδ] with n hn hun
  exact ((hN n hn (τ n) (hτ n) (u n) hun).trans_lt hrε).le

end LatticeProb.Cadlag.HalfLine
