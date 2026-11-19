import LongRangeHeat.KallenbergFixedLaw

/-!
# Countable collections of oscillation partitions

Uniform partition estimates at countably many scales can be combined using
countable subadditivity, including when partition sets are not measurable.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

variable {E : Type} [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
  {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]

/-- Uniform partition estimates at countably many scales hold simultaneously
outside an event bounded by the sum of the probability budgets. -/
theorem exists_uniform_oscillation_partition_collection
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)
    (hY : ∀ n, Measurable (Y n)) (t : ℕ → Time) (ht : ∀ k, 0 < t k)
    (η : ℕ → ℝ) (hη : ∀ k, 0 < η k) (p : ℕ → ℝ≥0∞) (hp : ∀ k, 0 < p k)
    (h : ∀ H : ℝ, 0 < H → ∀ ζ : ℝ, 0 < ζ →
      ∀ τ : (n : ℕ) → Ω n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ω n))
          {w | ζ ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0)) :
    ∃ δ : ℕ → ℝ, (∀ k, 0 < δ k) ∧ ∀ n,
      (P n : Measure (Ω n)) {w | ¬ ∀ k, HasOscillationPartition (Y n w) (t k) (δ k) (η k)} ≤
        ∑' k, p k := by
  classical
  choose δ hδ hbound using fun k =>
    exists_pos_uniform_oscillation_partition_of_optional_increment P Y hY (t k) (ht k) h
      (hη k) (hp k)
  refine ⟨δ, hδ, fun n => ?_⟩
  calc
    _ ≤ (P n : Measure (Ω n)) (⋃ k, {w | ¬ HasOscillationPartition (Y n w) (t k) (δ k) (η k)}) := by
      apply measure_mono
      intro w hw
      simp only [Set.mem_ofPred_eq, not_forall] at hw
      exact Set.mem_iUnion.mpr hw
    _ ≤ ∑' k, (P n : Measure (Ω n))
        {w | ¬ HasOscillationPartition (Y n w) (t k) (δ k) (η k)} := measure_iUnion_le _
    _ ≤ ∑' k, p k := ENNReal.tsum_le_tsum (fun k => (hbound k n).le)

end LatticeProb.Cadlag.HalfLine
