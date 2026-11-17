import LongRangeHeat.KallenbergStopping
import LongRangeHeat.Statements.Aldous
import LongRangeHeat.KallenbergWeakStopping
import LongRangeHeat.KallenbergModulusProbability

/-!
# Stopping increments of the annealed walks

The stopping-time estimate of Proposition 4.2 implies uniform control of
bounded discrete stopping increments along a sequence of scales.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped Topology NNReal ENNReal
open LongRange (Edge)

/-- Proposition 4.2 gives the uniform stopping-increment condition used in
Kallenberg's tightness argument. -/
theorem stoppingIncrementCondition_of_aldous
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    stoppingIncrementCondition (Ω := fun _ : ℕ => PathSpace d)
      (fun n => annealedLaw hd P a hP (hε n).1) (fun _ => id) := by
  apply stoppingIncrementCondition_of_positive_stopping_increment
  intro H hH η hη τ hτ u hupos hu
  have hstop : ∀ n t, MeasurableSet[canonicalSigma d t]
      {X | ((τ n X : ℝ≥0) : ℝ) ≤ t} := by
    intro n t
    simpa only [NNReal.coe_le_coe] using (hτ n).2.2 t
  have hlim := Statements.aldous_condition hMSC hNash hDavies hd P a hP ε hε hε0
    H hH (fun n X => (τ n X : ℝ)) hstop (fun n X => (τ n X).2)
    (fun n X => (hτ n).2.1 X) (fun n => (u n : ℝ))
    (fun n => by exact_mod_cast hupos n) hu (show 0 < η / 2 by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards with n
  apply measure_mono
  intro X hX
  change η ≤ dist (X.1 (τ n X + u n)) (X.1 (τ n X)) at hX
  change η / 2 < ‖X.1 (((τ n X : ℝ) + (u n : ℝ)).toNNReal) -
    X.1 ((τ n X : ℝ).toNNReal)‖
  have ht : ((τ n X : ℝ) + (u n : ℝ)).toNNReal = τ n X + u n := by
    rw [← NNReal.coe_add, Real.toNNReal_coe]
  have hs : ((τ n X : ℝ)).toNNReal = τ n X := Real.toNNReal_coe
  simpa only [ht, hs, ← dist_eq_norm] using (show η / 2 <
    dist (X.1 (τ n X + u n)) (X.1 (τ n X)) by linarith)


/-- Proposition 4.2 gives sequential increment convergence at every bounded
natural stopping time of the annealed coordinate process. -/
theorem annealed_tendsto_optional_increment
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) {H η : ℝ} (hH : 0 < H) (hη : 0 < η)
    (τ : ℕ → PathSpace d → Time) (hτ : ∀ n, naturalStopping id H (τ n))
    (u : ℕ → Time) (hupos : ∀ n, 0 < u n)
    (hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d))
      {X | η ≤ dist (X.1 (τ n X + u n)) (X.1 (τ n X))}) atTop (𝓝 0) := by
  have hstop : ∀ n t, MeasurableSet[canonicalSigma d t]
      {X | ((τ n X : ℝ≥0) : ℝ) ≤ t} := by
    intro n t
    simpa only [NNReal.coe_le_coe] using (hτ n).2 t
  have hlim := Statements.aldous_condition hMSC hNash hDavies hd P a hP ε hε hε0
    H hH (fun n X => (τ n X : ℝ)) hstop (fun n X => (τ n X).2)
    (fun n X => (hτ n).1 X) (fun n => (u n : ℝ))
    (fun n => by exact_mod_cast hupos n) hu (show 0 < η / 2 by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards with n
  apply measure_mono
  intro X hX
  change η ≤ dist (X.1 (τ n X + u n)) (X.1 (τ n X)) at hX
  change η / 2 < ‖X.1 (((τ n X : ℝ) + (u n : ℝ)).toNNReal) -
    X.1 ((τ n X : ℝ).toNNReal)‖
  have ht : ((τ n X : ℝ) + (u n : ℝ)).toNNReal = τ n X + u n := by
    rw [← NNReal.coe_add, Real.toNNReal_coe]
  have hs : ((τ n X : ℝ)).toNNReal = τ n X := Real.toNNReal_coe
  simpa only [ht, hs, ← dist_eq_norm] using (show η / 2 <
    dist (X.1 (τ n X + u n)) (X.1 (τ n X)) by linarith)

/-- Proposition 4.2 yields the paired weakly optional expectation bound for
annealed walk laws. -/
theorem annealed_exists_uniform_weak_paired_expectation
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) {H η : ℝ} (hH : 0 < H) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ σ τ : PathSpace d → Time, weakNaturalStopping id H σ →
      weakNaturalStopping id H τ → (∀ X, σ X ≤ τ X) →
      (∀ X, (τ X : ℝ) ≤ (σ X : ℝ) + δ) →
      (∫ X, boundedDistance (X.1 (σ X)) (X.1 (τ X))
        ∂(annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d))) < η := by
  apply exists_pos_eventually_uniform_weak_paired_expectation
    (fun n => annealedLaw hd P a hP (hε n).1) (fun _ => id) (fun _ => measurable_id)
    ?_ hH hη
  intro T hT ζ hζ τ hτ u hupos hu
  exact annealed_tendsto_optional_increment hMSC hNash hDavies hd P a hP ε hε hε0
    hT hζ τ hτ u hupos hu

/-- Proposition 4.2 provides high-probability small-oscillation partitions
for the annealed walk laws. -/
theorem annealed_exists_oscillation_partition
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) (T t : Time) (ht0 : 0 < t) (ht : t < T)
    {ζ : ℝ} (hζ : 0 < ζ) {β : ℝ≥0∞} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d))
        {X | ¬ HasOscillationPartition X t δ (2 * ζ)} < β := by
  apply exists_pos_eventually_oscillation_partition_of_optional_increment
    (fun n => annealedLaw hd P a hP (hε n).1) (fun _ => id) (fun _ => measurable_id)
    T t ht0 ht hζ ?_ hβ
  intro H hH η hη τ hτ u hupos hu
  exact annealed_tendsto_optional_increment hMSC hNash hDavies hd P a hP ε hε hε0
    hH hη τ hτ u hupos hu

end LongRangeHeat
