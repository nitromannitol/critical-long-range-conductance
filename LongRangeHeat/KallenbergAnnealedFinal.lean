import LongRangeHeat.KallenbergAnnealed
import LongRangeHeat.KallenbergCriterion

/-!
# Annealed invariance principle

Tightness from stopping increments and convergence of finite-dimensional
laws imply convergence of the annealed path laws.
-/

namespace LongRangeHeat

open Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped Topology NNReal
open LongRange (Edge)

/-- The annealed laws converge to scaled Brownian motion. -/
theorem annealed_invariance_of_kallenberg
    (hMSC : MuruganSaloffCosteUniform)
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
      exact Statements.fdd_convergence hMSC hNash hDavies hd P a hP B hB hk ts hmono
        (fun n => (ε n : ℝ)) hε hε0'
  · intro H hH η hη τ hτ u hupos hu
    exact annealed_tendsto_optional_increment hMSC hNash hDavies hd P a hP
      (fun n => (ε n : ℝ)) hε hε0' hH hη τ hτ u hupos hu

end LongRangeHeat
