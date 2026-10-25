import LongRangeAudit.QuenchedInvariance.Vocabulary.EthierKurtzTrotterKato

/-! # Independent EthierKurtzSkorokhod vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# Ethier–Kurtz: weak convergence and relative compactness in `D_E[0,∞)`

S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
(1986), Chapter 3, on the half-line càdlàg space `D_E[0,∞)` with the metric (5.2):
Theorem 7.8(b) (a relatively compact sequence of laws whose finite-dimensional laws converge
on a dense set of times converges weakly; `E` separable) and Theorem 8.6, (b) ⇒ (a) (Kurtz's
criterion for relative compactness from conditional increment bounds with respect to the raw
natural filtration, under the marginal compactness condition 7.2(a) at rational times; `E`
complete and separable). The propositions are stated so that a formalization citing them can
carry them as explicit hypotheses; they are not proved here.
-/

namespace LatticeProb.External

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open LatticeProb.Cadlag.HalfLine

/-- **Ethier–Kurtz, Chapter 3, Theorem 7.8(b).** -/
def EthierKurtzConvergenceFromFdd : Prop :=
  ∀ (E : Type) [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (mu : ℕ → ProbabilityMeasure (D E)) (nu : ProbabilityMeasure (D E)),
    IsCompact (closure (Set.range mu)) →
    (∃ S : Set Time, Dense S ∧
      ∀ (k : ℕ) (ts : Fin k → Time), (∀ i, ts i ∈ S) →
        Tendsto (fun n => jointLaw (mu n) ts) atTop (𝓝 (jointLaw nu ts))) →
    Tendsto mu atTop (𝓝 nu)

/-- **Ethier–Kurtz, Chapter 3, Theorem 8.6, (b) ⇒ (a).** -/
def EthierKurtzRelativeCompactness : Prop :=
  ∀ (E : Type) [MetricSpace E] [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E]
    [BorelSpace E] (A : Type) (Ω : A → Type) (m : ∀ a, MeasurableSpace (Ω a))
    (P : ∀ a, @ProbabilityMeasure (Ω a) (m a)) (Y : ∀ a, Ω a → D E)
    (hY : ∀ a, @Measurable (Ω a) (D E) (m a) inferInstance (Y a)),
    (∀ a t, @Measurable (Ω a) E (m a) inferInstance (fun w => (Y a w).1 t)) →
    (∀ eta : ℝ, 0 < eta → ∀ t : ℚ, 0 ≤ t → ∃ K : Set E, IsCompact K ∧
      ∀ a, ENNReal.ofReal (1 - eta) ≤
        (P a : @Measure (Ω a) (m a)) {w | (Y a w).1 (t : ℝ).toNNReal ∈ K}) →
    (∀ T : ℝ, 0 < T → ∃ beta : ℝ, 0 < beta ∧
      ∃ gam : ∀ a, ℝ → Ω a → ℝ≥0,
        (∀ a delta, 0 < delta → delta < 1 →
          @Measurable (Ω a) ℝ≥0 (m a) inferInstance (gam a delta)) ∧
        (∀ a delta, 0 < delta → delta < 1 → ∀ t u v : Time,
          (t : ℝ) ≤ T → (u : ℝ) ≤ delta → (v : ℝ) ≤ min delta t →
          ∀ᵐ w ∂(P a : @Measure (Ω a) (m a)),
            (@condLExp (Ω a) (m a) (naturalSigma (Y a) t)
              (P a : @Measure (Ω a) (m a))
              (incrementPower (Y a) beta (t + u) t) w) *
                incrementPower (Y a) beta t (t - v) w ≤
            @condLExp (Ω a) (m a) (naturalSigma (Y a) t)
              (P a : @Measure (Ω a) (m a)) (fun w => gam a delta w) w) ∧
        Tendsto (fun delta : ℝ => ⨆ a, ∫⁻ w, (gam a delta w : ℝ≥0∞)
          ∂(P a : @Measure (Ω a) (m a))) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun delta : ℝ => ⨆ a,
          ∫⁻ w, incrementPower (Y a) beta delta.toNNReal 0 w
            ∂(P a : @Measure (Ω a) (m a))) (𝓝[>] 0) (𝓝 0)) →
    IsCompact (closure (Set.range (fun a =>
      (P a).map (@Measurable.aemeasurable (Ω a) (D E) (m a) inferInstance
        (Y a) (P a) (hY a)))))

end LatticeProb.External

end LongRangeAudit.QuenchedInvariance
