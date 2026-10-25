import LongRange.Continuum.Weak
import LongRange.TwoScale.MainTheorem

/-!
# Quantitative homogenization for the original weak continuum solution

The source data produce a unique H¹₀ class and a unique continuous zero-extended
classical representative. The original lattice error samples this representative.
-/

namespace LongRange.TwoScale

open MeasureTheory LatticeProb LatticeProb.Elliptic LatticeProb.Euclidean.Lattice
open LatticeProb.Elliptic.WeakDirichlet

noncomputable section

/-- The full main estimate with a produced unique weak class and its unique continuous
classical representative. Constants precede the probability space, field and datum. -/
theorem exists_weak_solution_main_estimate
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (h75 : LatticeProb.External.GilbargTrudingerZeroBoundaryApproximation)
    (h82 : LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness)
    (d : ℕ) (hd : 1 ≤ d) (lam σ μ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    (U : Set (Fin d → ℝ)) (hU : IsC2HolderDomain σ U) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ f : (Fin d → ℝ) → ℝ, c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M →
      ∃ w : H10 U, ∃ ū : (Fin d → ℝ) → ℝ,
        IsWeakSolution U μ (meanConductance P hd a / (2 * d)) f w ∧
        (∀ z : H10 U, IsWeakSolution U μ (meanConductance P hd a / (2 * d)) f z →
          z = w) ∧
        (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū ∧
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
  obtain ⟨w, ū, hw, hwu, hū, hae, huniq⟩ :=
    Continuum.exists_weak_classical_solution h614 h619 h66 h37 h637 h75 h82
      hd hσ hμ hU hA hf
  obtain ⟨𝒳, hmeas, htail, herr⟩ := hmain P a hA f hf ū hū.1
  refine ⟨w, ū, hw, hwu, hae, hū, huniq, 𝒳, hmeas, htail, ?_⟩
  intro v hv ω ε hε hscale u hu heqn
  rw [Continuum.sampled_error_eq h37 hd hμ hU hA hū.1 hv ε u]
  exact herr ω ε hε hscale u hu heqn

end

end LongRange.TwoScale
