import LongRangeHeat.KallenbergModulus
import LongRangeHeat.KallenbergOscillationCount

/-!
# Probability of large path oscillations

Tightness of the number of oscillations and short-gap control yield partitions
with small oscillation and uniformly positive nonterminal interval lengths.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

variable {E : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
  {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]

omit [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Uniform gap and oscillation-count bounds give small probability of lacking
an oscillation partition. -/
theorem exists_pos_eventually_oscillation_partition
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (T t : Time) (ht0 : 0 < t) (ht : t < T) {ζ : ℝ} (hζ : 0 < ζ)
    (hcount : ∀ p : ℝ≥0∞, 0 < p → ∃ k N : ℕ, ∀ n, N ≤ n →
      (P n : Measure (Ω n)) {w | oscillationTime (Y n) T ζ k w < t} < p)
    (hgap : ∀ p : ℝ≥0∞, 0 < p → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ k : ℕ,
        (P n : Measure (Ω n)) {w | oscillationTime (Y n) T ζ (k + 1) w < T ∧
          (oscillationTime (Y n) T ζ (k + 1) w : ℝ) ≤
            (oscillationTime (Y n) T ζ k w : ℝ) + δ} < p)
    {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (P n : Measure (Ω n)) {w | ¬ HasOscillationPartition (Y n w) t δ (2 * ζ)} < β := by
  obtain ⟨r, _, hr', hrβ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hβ
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr'
  have hr4 : 0 < r / 4 := by linarith
  obtain ⟨k, N₁, hN₁⟩ := hcount (ENNReal.ofReal (r / 4)) (ENNReal.ofReal_pos.mpr hr4)
  let q : ℝ := r / (4 * (k + 1 : ℝ))
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨δ, hδ, N₂, hN₂⟩ := hgap (ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq)
  refine ⟨δ, hδ, max N₁ N₂, ?_⟩
  intro n hn
  let A : Set (Ω n) := {w | oscillationTime (Y n) T ζ k w < t}
  let B (j : ℕ) : Set (Ω n) := {w | oscillationTime (Y n) T ζ (j + 1) w < T ∧
    (oscillationTime (Y n) T ζ (j + 1) w : ℝ) ≤
      (oscillationTime (Y n) T ζ j w : ℝ) + δ}
  have hsub : {w | ¬ HasOscillationPartition (Y n w) t δ (2 * ζ)} ⊆
      A ∪ ⋃ j ∈ Finset.range k, B j := by
    intro w hw
    by_cases hstop : oscillationTime (Y n) T ζ k w < t
    · exact Or.inl hstop
    · right
      by_contra hbad
      have hm : t ≤ oscillationTime (Y n) T ζ k w := le_of_not_gt hstop
      apply hw
      apply hasOscillationPartition_of_oscillation_gaps (Y n) T t ht0 hζ.le hδ k w hm
      intro j hj hnext
      by_contra hshort
      have hbe : w ∈ B j := ⟨hnext.trans ht, by linarith [not_le.mp hshort]⟩
      exact hbad (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr hj, hbe⟩⟩)
  have hA : (P n : Measure (Ω n)) A ≤ ENNReal.ofReal (r / 4) :=
    (hN₁ n (le_trans (le_max_left N₁ N₂) hn)).le
  have hB : (P n : Measure (Ω n)) (⋃ j ∈ Finset.range k, B j) ≤
      ENNReal.ofReal (r / 4) := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, (P n : Measure (Ω n)) (B j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range k, ENNReal.ofReal q := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hN₂ n (le_trans (le_max_right N₁ N₂) hn) j).le
      _ = (k : ℝ≥0∞) * ENNReal.ofReal q := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal ((k : ℝ) * q) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (r / 4) := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [q]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hden : 0 < 4 * ((k : ℝ) + 1) := by positivity
        have hh : ((k : ℝ) * r) / (4 * ((k : ℝ) + 1)) ≤ r / 4 :=
          (div_le_iff₀ hden).mpr (by nlinarith)
        convert hh using 1; ring
  calc
    _ ≤ (P n : Measure (Ω n)) A + (P n : Measure (Ω n)) (⋃ j ∈ Finset.range k, B j) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) := add_le_add hA hB
    _ = ENNReal.ofReal (r / 2) := by
      rw [← ENNReal.ofReal_add hr4.le hr4.le]
      congr 1
      ring
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)
    _ < β := hrβ


/-- Aldous' sequential condition gives high-probability oscillation partitions
at sufficiently small scales. -/
theorem exists_pos_eventually_oscillation_partition_of_optional_increment
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (hY : ∀ n, Measurable (Y n)) (T t : Time) (ht0 : 0 < t) (ht : t < T)
    {ζ : ℝ} (hζ : 0 < ζ)
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (P n : Measure (Ω n)) {w | ¬ HasOscillationPartition (Y n w) t δ (2 * ζ)} < β := by
  have hT : 0 < T := ht0.trans ht
  apply exists_pos_eventually_oscillation_partition P Y T t ht0 ht hζ ?_ ?_ hβ
  · intro p hp
    exact exists_eventually_measure_oscillationTime_lt_of_optional_increment P Y hY T t hT ht hζ h hp
  · intro p hp
    apply exists_pos_eventually_oscillation_gap_le P Y hY hζ ?_ hp
    intro ε hε
    exact exists_pos_eventually_uniform_weak_paired_expectation P Y hY h
      (show 0 < (T : ℝ) by exact_mod_cast hT) hε


/-- Aldous' sequential condition gives the truncated modified-modulus bound (9) of
Kallenberg (2002), Theorem 16.11, for the lower Lebesgue integral `∫⁻`, which is the
expectation in (9) whenever the modulus is measurable. -/
theorem exists_pos_eventually_truncatedModulus_lintegral
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (hY : ∀ n, Measurable (Y n)) (t : Time) (ht : 0 < t)
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ d : ℝ, d ≤ δ →
      (∫⁻ w, truncatedModifiedModulus (Y n w) t d ∂(P n : Measure (Ω n))) < ε := by
  obtain ⟨r, _, hr', hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr'
  have hr2 : 0 < r / 2 := by linarith
  have hr8 : 0 < r / 8 := by linarith
  let T : Time := t + 1
  have htT : t < T := lt_add_of_pos_right _ zero_lt_one
  obtain ⟨δ, hδ, N, hN⟩ :=
    exists_pos_eventually_oscillation_partition_of_optional_increment P Y hY T t ht htT hr8 h
      (ENNReal.ofReal_pos.mpr hr2)
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn d hd
  let f : Ω n → ℝ≥0∞ := fun w => truncatedModifiedModulus (Y n w) t d
  let A : Set (Ω n) := {w | ENNReal.ofReal (r / 2) ≤ f w}
  have hsub : A ⊆ {w | ¬ HasOscillationPartition (Y n w) t δ (2 * (r / 8))} := by
    intro w hw hp
    have hp' := truncatedModifiedModulus_le_of_partition (by positivity) (hp.mono hd)
    have hlt : ENNReal.ofReal (2 * (r / 8)) < ENNReal.ofReal (r / 2) :=
      (ENNReal.ofReal_lt_ofReal_iff hr2).mpr (by linarith)
    exact (not_lt_of_ge hw) (hp'.trans_lt hlt)
  have hA : (P n : Measure (Ω n)) A < ENNReal.ofReal (r / 2) :=
    (measure_mono hsub).trans_lt (hN n hn)
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal (r / 2) + A.indicator (fun _ => (1 : ℝ≥0∞)) w
        ∂(P n : Measure (Ω n)) := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ A
      · simp only [Set.indicator_of_mem hw]
        exact (min_le_right _ _).trans (le_add_self : (1 : ℝ≥0∞) ≤ _)
      · simp only [Set.indicator_of_notMem hw, add_zero]
        exact (le_of_not_ge hw)
    _ ≤ ENNReal.ofReal (r / 2) + (P n : Measure (Ω n)) A := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      exact add_le_add le_rfl (lintegral_indicator_one_le A)
    _ < ENNReal.ofReal (r / 2) + ENNReal.ofReal (r / 2) :=
      ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hA
    _ = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_add hr2.le hr2.le]
      congr 1
      ring
    _ < ε := hrε

end LatticeProb.Cadlag.HalfLine
