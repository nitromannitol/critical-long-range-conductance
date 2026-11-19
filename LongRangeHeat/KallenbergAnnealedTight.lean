import LongRangeHeat.KallenbergCompleteness
import LongRangeHeat.KallenbergAnnealedBudget
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Tightness of annealed paths

Complete path space turns the high-probability totally bounded sets into
compact sets. Prokhorov's theorem gives relative compactness of the laws.
-/

namespace LongRangeHeat

open Set Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped ENNReal Topology
open LongRange (Edge)

/-- The sequence of annealed laws is tight. -/
theorem annealedLaw_isTight_of_stopping
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    IsTightMeasureSet {((annealedLaw hd P a hP (hε n).1 : ProbabilityMeasure (PathSpace d)) :
      Measure (PathSpace d)) | n} := by
  let : CompleteSpace (PathSpace d) := completeSpace_of_complete_state
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro δ hδ
  obtain ⟨r, hr, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ δ := by
    by_cases htop : δ = ∞
    · exact ⟨1, by norm_num, htop ▸ le_top⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos (ne_of_gt hδ) htop,
        le_of_eq (ENNReal.ofReal_toReal htop)⟩
  obtain ⟨A, hA, hmeasure⟩ :=
    annealed_exists_totallyBounded_measure_compl hMSC hNash hDavies hd P a hP ε hε hε0 hr
  refine ⟨closure A, hA.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  exact ((measure_mono (compl_subset_compl.mpr subset_closure)).trans (hmeasure n)).trans hrδ

/-- The annealed laws have compact closure by Prokhorov's theorem. -/
theorem annealedLaw_isCompact_closure_range_of_stopping
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    IsCompact (closure (range (fun n => annealedLaw hd P a hP (hε n).1))) := by
  apply isCompact_closure_of_isTightMeasureSet
  convert annealedLaw_isTight_of_stopping hMSC hNash hDavies hd P a hP ε hε hε0 using 1
  ext μ
  simp only [mem_ofPred_eq, mem_range]
  constructor
  · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, rfl⟩

end LongRangeHeat
