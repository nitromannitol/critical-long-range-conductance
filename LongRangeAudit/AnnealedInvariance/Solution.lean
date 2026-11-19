import LongRangeAudit.AnnealedInvariance.SolutionBridge

/-! # Annealed invariance principle -/

namespace LongRangeAudit.AnnealedInvariance
open Filter MeasureTheory LongRangeAudit.QuenchedInvariance
open LongRangeAudit.QuenchedInvariance.LongRange (Edge)
open scoped Topology
noncomputable section
attribute [local instance 2000] LongRangeAudit.QuenchedInvariance.LatticeProb.continuousMapMeasurableSpace
/-- Theorem 1.2: convergence of the annealed rescaled walks. -/
theorem annealed_invariance_principle
    (hMSC : LongRangeAudit.QuenchedInvariance.LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LongRangeAudit.QuenchedInvariance.LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LongRangeAudit.QuenchedInvariance.LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK :
      LongRangeAudit.QuenchedInvariance.LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LongRangeAudit.QuenchedInvariance.LatticeProb.External.EthierKurtzConvergenceFromFdd)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : LongRangeAudit.QuenchedInvariance.ConductanceLaw P lam a)
    (B : ProbabilityMeasure (LongRangeAudit.QuenchedInvariance.LatticeProb.BrownianPath d))
    (hB : LongRangeAudit.QuenchedInvariance.LatticeProb.IsStandardBrownianLaw
      (B : Measure (LongRangeAudit.QuenchedInvariance.LatticeProb.BrownianPath d))) :
    let s : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2)
    let F : LongRangeAudit.QuenchedInvariance.LatticeProb.BrownianPath d →
        LongRangeAudit.QuenchedInvariance.PathSpace d := fun w =>
      LongRangeAudit.QuenchedInvariance.LatticeProb.Cadlag.HalfLine.D.ofContinuous
        ⟨fun t => s • w t, w.continuous.const_smul s⟩
    ∃ _ : Measurable F,
      Tendsto (fun ε : Set.Ioo (0 : ℝ) (1 / 2) =>
        LongRangeAudit.QuenchedInvariance.annealedLaw hd P a hP ε.2.1)
        (Filter.comap Subtype.val (𝓝 0)) (𝓝 (ProbabilityMeasure.map B F)) := by
  have h := _root_.LongRangeHeat.Statements.annealed_invariance_principle
    (muruganSaloffCosteUniform hMSC) (chenKimKumagaiWangNash hNash)
    (chenKimKumagaiWangDavies hDavies) (ethierKurtzStopping_iff.mp hEK)
    (ethierKurtzFdd_iff.mp hFdd) hd P a (heatConductanceLaw P lam a hP) B
    (brownianLaw_iff _ |>.mp hB)
  dsimp only at h ⊢
  simp only [← heatAnnealedLaw_eq hd P a hP] at h
  exact h

end
end LongRangeAudit.AnnealedInvariance
