import LongRange.Continuum.Canonical
import LongRange.TwoScale.MainTheorem

/-!
# Quantitative homogenization with a produced classical continuum solution

The constants are those of the original main theorem and are selected before the
probability space, conductance field and forcing. The continuum solution is produced
from these data, and the same random scale controls every classical representative.
No weak Sobolev identification is asserted.
-/

namespace LongRange.TwoScale

open MeasureTheory LatticeProb LatticeProb.Elliptic LatticeProb.Euclidean.Lattice

noncomputable section

/-- The main estimate with all-data classical existence and uniqueness. The same minimal
scale gives the sampled error for every classical representative by closure uniqueness. -/
theorem exists_classical_solution_main_estimate
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (d : ℕ) (hd : 1 ≤ d) (lam σ μ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    (U : Set (Fin d → ℝ)) (hU : IsC2HolderDomain σ U) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ f : (Fin d → ℝ) → ℝ, c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M →
      ∃ ū : (Fin d → ℝ) → ℝ,
        (IsClassicalDirichletSolution U μ (meanConductance P hd a / (2 * d)) f ū ∧
          Continuous ū ∧ ∀ x ∉ U, ū x = 0) ∧
        (∀ v, (IsClassicalDirichletSolution U μ
          (meanConductance P hd a / (2 * d)) f v ∧ Continuous v ∧
            ∀ x ∉ U, v x = 0) → v = ū) ∧
        ∃ 𝒳 : Ω → ENNReal, Measurable 𝒳 ∧
          (∀ s : ℝ, 1 ≤ s → P {ω | ENNReal.ofReal s < 𝒳 ω} ≤
            ENNReal.ofReal (C * Real.exp (-(c * s)))) ∧
          ∀ v : (Fin d → ℝ) → ℝ, IsClassicalDirichletSolution U μ
              (meanConductance P hd a / (2 * d)) f v →
            ∀ ω, ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
              𝒳 ω ≤ ENNReal.ofReal |Real.log ε| →
              ∀ u : Site d → ℝ, SupportedIn ε U u →
                (∀ q ∈ latticeSet ε U,
                  μ * u q - generator ε (a ω) u q = f (physical ε q)) →
                l2Norm ε U (fun q => u q - v (physical ε q)) ≤
                  C / Real.sqrt |Real.log ε| := by
  obtain ⟨C, c, hC, hc, hmain⟩ :=
    LongRange.main_theorem h619 h66 h37 h637 d hd lam σ μ hσ hμ U hU M
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P a hA f hf
  obtain ⟨ū, hū, huniq⟩ :=
    Continuum.existsUnique_classical_solution h614 h37 hd hσ hμ hU hA hf
  obtain ⟨𝒳, hmeas, htail, herr⟩ := hmain P a hA f hf ū hū.1
  refine ⟨ū, hū, huniq, 𝒳, hmeas, htail, ?_⟩
  intro v hv ω ε hε hscale u hu heqn
  rw [Continuum.sampled_error_eq h37 hd hμ hU hA hū.1 hv ε u]
  exact herr ω ε hε hscale u hu heqn

end

end LongRange.TwoScale
