import LongRangeHeat.KallenbergModulusProbability

/-!
# Oscillations under a fixed law

A single càdlàg law has vanishing probabilities of many oscillations and of
very short gaps before a fixed cap.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal

variable {E Ω : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

/-- Under one law, the probability of the kth oscillation occurring before the
cap tends to zero. -/
theorem tendsto_measure_oscillationTime_lt_cap
    (P : ProbabilityMeasure Ω) (Y : Ω → D E) (hY : Measurable Y)
    (T : Time) {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun k => (P : Measure Ω) {w | oscillationTime Y T ζ k w < T}) atTop (𝓝 0) := by
  let A : ℕ → Set Ω := fun k => {w | oscillationTime Y T ζ k w < T}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurableSet_lt ((weakNaturalStopping_oscillationTime Y T ζ k).measurable hY) measurable_const
  have hanti : Antitone A := by
    intro i j hij w hw
    have hm : Monotone (fun k => oscillationTime Y T ζ k w) :=
      monotone_nat_of_le_succ (fun k => oscillationTime_le_succ Y T ζ k w)
    exact (hm hij).trans_lt hw
  have hempty : (⋂ k, A k) = ∅ := by
    ext w
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨k, hk⟩ := exists_le_oscillationTime Y T T le_rfl hζ w
    exact ⟨k, not_lt_of_ge hk⟩
  have hlim := tendsto_measure_iInter_atTop (μ := (P : Measure Ω))
    (fun k => (hA k).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hempty, measure_empty] using hlim


/-- Under one law, the probability of a very short fixed oscillation gap before
the cap tends to zero. -/
theorem tendsto_measure_oscillation_gap
    (P : ProbabilityMeasure Ω) (Y : Ω → D E) (hY : Measurable Y)
    (T : Time) {ζ : ℝ} (hζ : 0 < ζ) (j : ℕ) :
    Tendsto (fun k : ℕ => (P : Measure Ω) {w | oscillationTime Y T ζ (j + 1) w < T ∧
      (oscillationTime Y T ζ (j + 1) w : ℝ) ≤
        (oscillationTime Y T ζ j w : ℝ) + 1 / ((k : ℝ) + 1)}) atTop (𝓝 0) := by
  let α := oscillationTime Y T ζ
  have hα (i : ℕ) : Measurable (α i) := (weakNaturalStopping_oscillationTime Y T ζ i).measurable hY
  let d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdanti : Antitone d := by
    intro i k hik
    dsimp [d]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hik 1)
  let A : ℕ → Set Ω := fun k => {w | α (j + 1) w < T ∧
    (α (j + 1) w : ℝ) ≤ (α j w : ℝ) + d k}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_lt (hα (j + 1)) measurable_const).inter
      (measurableSet_le (NNReal.continuous_coe.measurable.comp (hα (j + 1)))
        ((NNReal.continuous_coe.measurable.comp (hα j)).add_const (d k)))
  have hanti : Antitone A := by
    intro i k hik w hw
    exact ⟨hw.1, by have hh := hdanti hik; linarith [hw.2]⟩
  have hempty : (⋂ k, A k) = ∅ := by
    ext w
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hall
    have hnext : α (j + 1) w < T := (hall 0).1
    have hprev : α j w < T := (oscillationTime_le_succ Y T ζ j w).trans_lt hnext
    have hstrict := lt_nextOscillationTime Y (oscillationTime Y T ζ j) T hζ w hprev
    have hdiff : 0 < (α (j + 1) w : ℝ) - (α j w : ℝ) := by
      have hh : (α j w : ℝ) < (α (j + 1) w : ℝ) := by exact_mod_cast hstrict
      linarith
    obtain ⟨k, hk⟩ := (hd.eventually (Iio_mem_nhds hdiff)).exists
    exact (not_le_of_gt (by linarith : (α j w : ℝ) + d k < (α (j + 1) w : ℝ))) (hall k).2
  have hlim := tendsto_measure_iInter_atTop (μ := (P : Measure Ω))
    (fun k => (hA k).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hempty, measure_empty, A, d, α] using hlim


/-- Under one law, short gaps are uniformly unlikely over all oscillation
indices. -/
theorem exists_pos_uniform_oscillation_gap
    (P : ProbabilityMeasure Ω) (Y : Ω → D E) (hY : Measurable Y)
    (T : Time) {ζ : ℝ} (hζ : 0 < ζ) {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ,
      (P : Measure Ω) {w | oscillationTime Y T ζ (j + 1) w < T ∧
        (oscillationTime Y T ζ (j + 1) w : ℝ) ≤
          (oscillationTime Y T ζ j w : ℝ) + δ} < p := by
  obtain ⟨m, hm⟩ := ((tendsto_measure_oscillationTime_lt_cap P Y hY T hζ).eventually
    (Iio_mem_nhds hp)).exists
  have hall : ∀ᶠ k : ℕ in atTop, ∀ j ∈ Finset.range m,
      (P : Measure Ω) {w | oscillationTime Y T ζ (j + 1) w < T ∧
        (oscillationTime Y T ζ (j + 1) w : ℝ) ≤
          (oscillationTime Y T ζ j w : ℝ) + 1 / ((k : ℝ) + 1)} < p := by
    apply (Finset.eventually_all _).mpr
    intro j hj
    exact (tendsto_measure_oscillation_gap P Y hY T hζ j).eventually (Iio_mem_nhds hp)
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
  intro j
  by_cases hj : j < m
  · exact hk j (Finset.mem_range.mpr hj)
  · refine (measure_mono ?_).trans_lt hm
    intro w hw
    have hmono : Monotone (fun l => oscillationTime Y T ζ l w) :=
      monotone_nat_of_le_succ (fun l => oscillationTime_le_succ Y T ζ l w)
    exact (hmono (by omega : m ≤ j + 1)).trans_lt hw.1


/-- Every càdlàg law has high-probability small-oscillation partitions at
sufficiently small scales. -/
theorem exists_pos_measure_no_oscillation_partition_lt
    (P : ProbabilityMeasure Ω) (Y : Ω → D E) (hY : Measurable Y)
    (t : Time) (ht : 0 < t) {η : ℝ} (hη : 0 < η) {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ δ : ℝ, 0 < δ ∧
      (P : Measure Ω) {w | ¬ HasOscillationPartition (Y w) t δ η} < p := by
  let T : Time := t + 1
  let ζ : ℝ := η / 2
  have hζ : 0 < ζ := half_pos hη
  have htT : t < T := lt_add_of_pos_right _ zero_lt_one
  have hcount : ∀ q : ℝ≥0∞, 0 < q → ∃ k N : ℕ, ∀ _n, N ≤ _n →
      (P : Measure Ω) {w | oscillationTime Y T ζ k w < t} < q := by
    intro q hq
    obtain ⟨k, hk⟩ := ((tendsto_measure_oscillationTime_lt_cap P Y hY T hζ).eventually
      (Iio_mem_nhds hq)).exists
    refine ⟨k, 0, fun _ _ => ?_⟩
    exact (measure_mono (fun w hw => hw.trans htT)).trans_lt hk
  have hgap : ∀ q : ℝ≥0∞, 0 < q → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ _n, N ≤ _n → ∀ k : ℕ,
        (P : Measure Ω) {w | oscillationTime Y T ζ (k + 1) w < T ∧
          (oscillationTime Y T ζ (k + 1) w : ℝ) ≤
            (oscillationTime Y T ζ k w : ℝ) + δ} < q := by
    intro q hq
    obtain ⟨δ, hδ, hδq⟩ := exists_pos_uniform_oscillation_gap P Y hY T hζ hq
    exact ⟨δ, hδ, 0, fun _ _ => hδq⟩
  obtain ⟨δ, hδ, N, hδp⟩ := exists_pos_eventually_oscillation_partition
    (fun _ : ℕ => P) (fun _ => Y) T t ht htT hζ hcount hgap hp
  refine ⟨δ, hδ, ?_⟩
  simpa only [ζ, show 2 * (η / 2) = η by ring] using hδp N le_rfl


variable {Ωs : ℕ → Type} [ms : ∀ n, MeasurableSpace (Ωs n)]

/-- Individual càdlàg laws extend an eventual partition bound to every index. -/
theorem exists_pos_uniform_oscillation_partition
    (P : ∀ n, ProbabilityMeasure (Ωs n)) (Y : ∀ n, Ωs n → D E)
    (hY : ∀ n, Measurable (Y n)) (t : Time) (ht : 0 < t)
    {η : ℝ} (hη : 0 < η) {p : ℝ≥0∞} (hp : 0 < p)
    (hasym : ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (P n : Measure (Ωs n)) {w | ¬ HasOscillationPartition (Y n w) t δ η} < p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      (P n : Measure (Ωs n)) {w | ¬ HasOscillationPartition (Y n w) t δ η} < p := by
  classical
  obtain ⟨δ₀, hδ₀, N, hN⟩ := hasym
  choose d hd hbound using fun n =>
    exists_pos_measure_no_oscillation_partition_lt (P n) (Y n) (hY n) t ht hη hp
  let S : Finset ℝ := insert δ₀ ((Finset.range N).image d)
  have hS : S.Nonempty := ⟨δ₀, Finset.mem_insert_self _ _⟩
  let δ := S.min' hS
  have hδ : 0 < δ := by
    apply (Finset.lt_min'_iff S hS).mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hδ₀
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hr
      exact hd n
  refine ⟨δ, hδ, ?_⟩
  intro n
  by_cases hn : n < N
  · have hδd : δ ≤ d n := Finset.min'_le S (d n)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩))
    refine (measure_mono ?_).trans_lt (hbound n)
    intro w hw hgood
    exact hw (hgood.mono hδd)
  · have hδ₀' : δ ≤ δ₀ := Finset.min'_le S δ₀ (Finset.mem_insert_self _ _)
    refine (measure_mono ?_).trans_lt (hN n (le_of_not_gt hn))
    intro w hw hgood
    exact hw (hgood.mono hδ₀')


/-- Aldous' sequential condition gives a partition bound uniform over the
entire sequence of laws. -/
theorem exists_pos_uniform_oscillation_partition_of_optional_increment
    (P : ∀ n, ProbabilityMeasure (Ωs n)) (Y : ∀ n, Ωs n → D E)
    (hY : ∀ n, Measurable (Y n)) (t : Time) (ht : 0 < t)
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : (n : ℕ) → Ωs n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ωs n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      (P n : Measure (Ωs n)) {w | ¬ HasOscillationPartition (Y n w) t δ η} < p := by
  apply exists_pos_uniform_oscillation_partition P Y hY t ht hη hp
  let T : Time := t + 1
  have htT : t < T := lt_add_of_pos_right _ zero_lt_one
  have hζ : 0 < η / 2 := half_pos hη
  have hh := exists_pos_eventually_oscillation_partition_of_optional_increment P Y hY
    T t ht htT hζ h hp
  simpa only [show 2 * (η / 2) = η by ring] using hh

end LatticeProb.Cadlag.HalfLine
