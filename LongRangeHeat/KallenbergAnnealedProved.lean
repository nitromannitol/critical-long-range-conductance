import LongRangeHeat.KallenbergAnnealedFinal
import LongRangeHeat.KallenbergApplication
import LongRangeHeat.Statements.AldousProved
import LongRangeHeat.Statements.FddProved

/-!
# Annealed invariance principle without the on-diagonal hypothesis

The Kallenberg–Aldous route to Theorem 1.2 with Propositions 4.2 and 4.3 in the forms
`aldous_condition_proved` and `fdd_convergence_proved`, whose on-diagonal heat-kernel bound is
proved for the critical lattice kernel. Only the Nash and Davies inputs remain hypotheses.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped Topology NNReal
open LongRange (Edge)

/-- Proposition 4.2 gives sequential increment convergence at every bounded natural stopping
time of the annealed coordinate process. -/
theorem annealed_tendsto_optional_increment_proved
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
  have hlim := Statements.aldous_condition_proved hNash hDavies hd P a hP ε hε hε0
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

/-- The annealed laws converge to scaled Brownian motion: the Kallenberg–Aldous criterion
applied to Propositions 4.2 and 4.3. -/
theorem annealed_invariance_of_kallenberg_proved
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
    let s : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2)
    Tendsto (fun ε : Set.Ioo (0 : ℝ) (1 / 2) => annealedLaw hd P a hP ε.2.1)
      (Filter.comap Subtype.val (𝓝 0)) (𝓝 (B.map (scaledBrownianPath s))) := by
  dsimp only
  rw [Filter.tendsto_iff_seq_tendsto]
  intro ε hε0
  have hε0' : Tendsto (fun n => ((ε n : Set.Ioo (0 : ℝ) (1 / 2)) : ℝ)) atTop (𝓝 0) :=
    Filter.tendsto_comap_iff.1 hε0
  have hε : ∀ n, ((ε n : Set.Ioo (0 : ℝ) (1 / 2)) : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2) :=
    fun n => (ε n).2
  apply tendsto_of_ordered_fdd_of_optional_increment
    (fun n => annealedLaw hd P a hP (hε n).1) _ 0
  · intro k ts hmono
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (ProbabilityMeasure (Fin 0 → EuclideanSpace ℝ (Fin d))) :=
        subsingleton_probabilityMeasure
      exact tendsto_const_nhds.congr fun _ => Subsingleton.elim _ _
    · rw [jointLaw_map_scaledBrownianPath]
      exact Statements.fdd_convergence_proved hNash hDavies hd P a hP B hB hk ts hmono
        (fun n => (ε n : ℝ)) hε hε0'
  · intro H hH η hη τ hτ u hupos hu
    exact annealed_tendsto_optional_increment_proved hNash hDavies hd P a hP
      (fun n => (ε n : ℝ)) hε hε0' hH hη τ hτ u hupos hu

end LongRangeHeat
