import LongRangeAudit.HeatHomogenization.SolutionBasic
import LongRangeHeat.Statements.MainTheorem

/-! # Transport between the heat equation vocabularies -/

namespace LongRangeAudit.HeatHomogenization

open MeasureTheory

/-- The two conductance assumptions have the same fields. -/
theorem conductanceLaw_iff {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : ℝ) (a : Ω → Edge d → ℝ) :
    ConductanceLaw P lam a ↔ _root_.LongRangeHeat.ConductanceLaw P lam a := by
  constructor <;> intro h
  · exact ⟨h.isProbabilityMeasure, h.lam_mem, h.measurable, h.indep, h.bounds, h.mean_one⟩
  · exact ⟨h.isProbabilityMeasure, h.lam_mem, h.measurable, h.indep, h.bounds, h.mean_one⟩

end LongRangeAudit.HeatHomogenization
