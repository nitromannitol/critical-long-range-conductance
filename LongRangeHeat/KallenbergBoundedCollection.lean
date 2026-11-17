import LongRangeHeat.KallenbergFiniteHorizon
import LongRangeHeat.KallenbergCompactContainment

/-!
# Totally bounded sets of paths

Countably many compact-containment and oscillation-partition estimates give a
high-probability totally bounded set of càdlàg paths.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped ENNReal Topology

/-- Countable state-containment and partition estimates give a common totally bounded set,
with its complement controlled by the sums of the failure probabilities. -/
theorem exists_totallyBounded_measure_compl_le
    {E : Type} [MetricSpace E]
    (t : ℕ → Time) (δ η : ℕ → ℝ)
    (ht : Tendsto t atTop atTop)
    (hδ : ∀ k, 0 < δ k) (hη : ∀ k, 0 < η k)
    (hη0 : Tendsto η atTop (𝓝 0)) (S : ℕ → Set E) (hS : ∀ k, IsCompact (S k))
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → D E)
    (p q : ℕ → ℝ≥0∞)
    (hp : ∀ n k, P n {ω | ¬ HasOscillationPartition (Y n ω) (t k) (δ k) (η k)} ≤ p k)
    (hq : ∀ n k, P n {ω | ∃ s ≤ t k, (Y n ω).1 s ∉ S k} ≤ q k) :
    ∃ A : Set (D E), TotallyBounded A ∧ ∀ n,
      P n {ω | Y n ω ∉ A} ≤ (∑' k, p k) + ∑' k, q k := by
  let A : Set (D E) := {x | (∀ k, HasOscillationPartition x (t k) (δ k) (η k)) ∧
    ∀ k s, s ≤ t k → x.1 s ∈ S k}
  refine ⟨A, ?_, fun n => ?_⟩
  · apply totallyBounded_of_partition_sequence A t η δ ht hη0 hη hδ
    · intro k
      exact ⟨S k, hS k, fun x hx s hs => hx.2 k s hs⟩
    · exact fun k x hx => hx.1 k
  · calc
      _ ≤ P n ((⋃ k, {ω | ¬ HasOscillationPartition (Y n ω) (t k) (δ k) (η k)}) ∪
          ⋃ k, {ω | ∃ s ≤ t k, (Y n ω).1 s ∉ S k}) := by
        apply measure_mono
        intro ω hω
        simp only [A, Set.mem_ofPred_eq, not_and, not_forall] at hω
        by_cases h : ∀ k, HasOscillationPartition (Y n ω) (t k) (δ k) (η k)
        · right
          obtain ⟨k, s, hs, hnot⟩ := hω h
          exact Set.mem_iUnion.mpr ⟨k, s, hs, hnot⟩
        · left
          obtain ⟨k, hk⟩ := not_forall.mp h
          exact Set.mem_iUnion.mpr ⟨k, hk⟩
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add
        ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (hp n)))
        ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (hq n))))

end LatticeProb.Cadlag.HalfLine
