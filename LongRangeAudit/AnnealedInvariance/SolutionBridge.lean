import LongRangeAudit.AnnealedInvariance.SolutionBasic
import LongRangeAudit.QuenchedInvariance.SolutionBridge
import LongRangeHeat.Statements.InvariancePrinciple

/-! # Transport between path-law vocabularies -/

namespace LongRangeAudit.QuenchedInvariance

open MeasureTheory
noncomputable section
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The uniform graph estimate has the same constant order in both vocabularies. -/
theorem muruganSaloffCosteUniform
    (h : LatticeProb.External.MuruganSaloffCosteUniform) :
    _root_.LatticeProb.External.MuruganSaloffCosteUniform := by
  intro X G hInf hConn V φ γ hm hV hv hp hγ hu hl hφ ζ hζ Cφ hCφ
  obtain ⟨C, hC, hb⟩ := h X (graphCopy G) hInf hConn V φ γ hm hV hv hp hγ
    (by simpa only [LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          densityPower_eq, graph_mass_eq, graph_reference_eq, graph_dist_eq] using hu)
    (by simpa only [LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          densityPower_eq, graph_mass_eq, graph_reference_eq, graph_dist_eq] using hl)
    hφ ζ hζ Cφ hCφ
  refine ⟨C, hC, ?_⟩
  intro k hk hs hj n
  have result := hb k hk hs
    (by simpa only [graph_mass_eq, graph_dist_eq] using hj) n
  simpa only [LatticeProb.Graph.LongRangeKernel.evenKernelSup,
    _root_.LatticeProb.Graph.LongRangeKernel.evenKernelSup, densityPower_eq,
    graph_mass_eq] using result

/-- The stopping-time compactness statements have the same full body. -/
theorem ethierKurtzStopping_iff : LatticeProb.External.EthierKurtzRelativeCompactnessStopping ↔
    _root_.LatticeProb.External.EthierKurtzRelativeCompactnessStopping := Iff.rfl

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
