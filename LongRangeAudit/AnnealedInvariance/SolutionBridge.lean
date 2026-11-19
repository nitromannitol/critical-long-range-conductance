import LongRangeAudit.AnnealedInvariance.SolutionBasic
import LongRangeAudit.QuenchedInvariance.SolutionBridge
import LongRangeHeat.Statements.InvariancePrincipleOfDavies

/-! # Transport between path-law vocabularies -/

namespace LongRangeAudit.QuenchedInvariance

open MeasureTheory
noncomputable section
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The conductance assumptions agree field by field. -/
theorem heatConductanceLaw (P : Measure Ω) (lam : ℝ) (a : Ω → LongRange.Edge d → ℝ)
    (h : ConductanceLaw P lam a) : _root_.LongRangeHeat.ConductanceLaw P lam a :=
  ⟨h.isProbabilityMeasure, h.lam_mem, h.measurable, h.indep, h.bounds, h.mean_one⟩

/-- Both constructions mix the identical path law over the same conductance law. -/
theorem heatAnnealedLaw_eq (hd : 1 ≤ d) (P : Measure Ω) (a : Ω → LongRange.Edge d → ℝ)
    {lam ε : ℝ} (hP : ConductanceLaw P lam a) (hε : 0 < ε) :
    annealedLaw hd P a hP hε =
      _root_.LongRangeHeat.annealedLaw hd P a (heatConductanceLaw P lam a hP) hε := rfl

end
end LongRangeAudit.QuenchedInvariance
