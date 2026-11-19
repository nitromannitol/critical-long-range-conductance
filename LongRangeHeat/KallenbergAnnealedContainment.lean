import LongRangeHeat.KallenbergCompactContainment
import LongRangeHeat.KallenbergApplication
import LongRangeHeat.InvariancePrinciple

/-!
# Compact containment for the annealed walks

The marginal displacement bound and the stopping-time estimate give compact
containment on every finite time interval.
-/

namespace LongRangeHeat

open MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.External
open scoped ENNReal
open LongRange (Edge)

/-- The annealed walk laws satisfy compact containment through every finite horizon. -/
theorem annealed_exists_compact_containment
    (hMSC : MuruganSaloffCosteUniform)
    (hNash : ChenKimKumagaiWangNash)
    (hDavies : ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0)) (T : Time)
    {p : ℝ} (hp : 0 < p) :
    ∃ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S ∧ ∀ n,
      (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d))
        {X | ∃ s ≤ T, X.1 s ∉ S} ≤ ENNReal.ofReal p := by
  apply exists_compact_measure_excursion_le
    (fun n => (annealedLaw hd P a hP (hε n).1 : Measure (PathSpace d)))
    (fun _ => id) 0 T ?_ ?_ hp
  · intro u q hq
    obtain ⟨R, _, hR⟩ := annealedLaw_exists_radius (hd := hd) (P := P) (a := a) (hP := hP)
      hMSC hNash hDavies hε u hq
    refine ⟨R, fun n => ?_⟩
    simpa only [id, dist_zero_right] using hR n
  · intro q hq
    obtain ⟨δ, hδ, hδbound⟩ := annealed_exists_uniform_oscillation_partition
      hMSC hNash hDavies hd P a hP ε hε hε0 (T + 1)
      (by positivity) (show (0 : ℝ) < 1 by norm_num) (ENNReal.ofReal_pos.mpr hq)
    exact ⟨δ, hδ, fun n => (hδbound n).le⟩

end LongRangeHeat
