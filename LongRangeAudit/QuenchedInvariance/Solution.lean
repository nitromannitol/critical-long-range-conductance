import LongRangeAudit.QuenchedInvariance.SolutionBridge

namespace LongRangeAudit.QuenchedInvariance
noncomputable section
open Filter MeasureTheory LongRange LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Cadlag.HalfLine
open scoped ENNReal Topology

-- Use the same independently defined Borel instance as the Challenge.
attribute [local instance 2000] LatticeProb.continuousMapMeasurableSpace
/-- The full quenched invariance principle from the proved source provider. -/
theorem quenched_invariance_principle
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hTK : External.EthierKurtzTrotterKato)
    (hRC : External.EthierKurtzRelativeCompactness)
    (hFdd : External.EthierKurtzConvergenceFromFdd)
    (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (d : ℕ) (hd : 1 ≤ d) (lam : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hU : AssumptionU P lam a)
    (g : (Fin d → ℝ) → ℝ) (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) (hgc : HasCompactSupport g)
    (hg1 : ∫ x, g x = 1)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
  let ρ := Measure.map (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
    (volume.withDensity (fun x => ENNReal.ofReal (g x)))
  let s := Real.sqrt (2 * (meanConductance P hd a / (2 * (d : ℝ))))
  let F : EuclideanSpace ℝ (Fin d) × BrownianPath d →
      D (EuclideanSpace ℝ (Fin d)) := fun p =>
    D.ofContinuous ⟨(fun t => p.1 + s • p.2 t),
      continuous_const.add (p.2.continuous.const_smul s)⟩
  ∃ ρp : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), (ρp : Measure _) = ρ ∧
    ∃ hF : Measurable F,
      ∀ᵐ ω ∂P,
        Tendsto
          (fun ε : Eps => pathLaw
            (walkRates hd ε.property.1 hU.lam_pos (a ω) (hU.bounds ω))
            (initialLaw ε.val g ε.property.1 (integrable_initial_density hg hgc) hg0 hg1 :
              Measure (Site d))
            (walkEmbed ε.val))
          epsFilter
          (𝓝 (ProbabilityMeasure.map
            (⟨(ρp : Measure _).prod (B : Measure (BrownianPath d)),
            inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × BrownianPath d))
              hF.aemeasurable))  := by
  exact _root_.LongRange.quenched_invariance_principle_of_cited h619 h66 h37 h637 h614
    (trotterKato hTK) hRC hFdd (muruganSaloffCoste hMSC)
    (chenKimKumagaiWangNash hNash) (chenKimKumagaiWangDavies hDavies)
    d hd lam P a (assumption hU) g hg hg0 hgc hg1 B hB

/-- The full quenched invariance principle from the proved source provider. -/
theorem quenched_invariance_principle_intro
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hTK : External.EthierKurtzTrotterKato)
    (hRC : External.EthierKurtzRelativeCompactness)
    (hFdd : External.EthierKurtzConvergenceFromFdd)
    (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (d : ℕ) (hd : 1 ≤ d) (lam : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hU : AssumptionU P lam a)
    (g : (Fin d → ℝ) → ℝ) (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) (hgc : HasCompactSupport g)
    (hg1 : ∫ x, g x = 1)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
  let ρ := Measure.map (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
    (volume.withDensity (fun x => ENNReal.ofReal (g x)))
  let s := Real.sqrt (meanConductance P hd a / (d : ℝ))
  let F : EuclideanSpace ℝ (Fin d) × BrownianPath d →
      D (EuclideanSpace ℝ (Fin d)) := fun p =>
    D.ofContinuous ⟨(fun t => p.1 + s • p.2 t),
      continuous_const.add (p.2.continuous.const_smul s)⟩
  ∃ ρp : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), (ρp : Measure _) = ρ ∧
    ∃ hF : Measurable F,
      ∀ᵐ ω ∂P,
        Tendsto
          (fun ε : Eps => pathLaw
            (walkRates hd ε.property.1 hU.lam_pos (a ω) (hU.bounds ω))
            (initialLaw ε.val g ε.property.1 (integrable_initial_density hg hgc) hg0 hg1 :
              Measure (Site d))
            (walkEmbed ε.val))
          epsFilter
          (𝓝 (ProbabilityMeasure.map
            (⟨(ρp : Measure _).prod (B : Measure (BrownianPath d)),
            inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × BrownianPath d))
              hF.aemeasurable))  := by
  exact _root_.LongRange.quenched_invariance_principle_intro_of_cited h619 h66 h37 h637 h614
    (trotterKato hTK) hRC hFdd (muruganSaloffCoste hMSC)
    (chenKimKumagaiWangNash hNash) (chenKimKumagaiWangDavies hDavies)
    d hd lam P a (assumption hU) g hg hg0 hgc hg1 B hB

end
end LongRangeAudit.QuenchedInvariance
