import LongRange.TwoScale.WeakMain

/-!
# Quantitative homogenization for weak source solutions

The full source main estimate, including the produced unique weak solution and representative.
-/

namespace LongRange.Statements

open MeasureTheory LatticeProb LatticeProb.Elliptic LatticeProb.Euclidean.Lattice
open LatticeProb.Elliptic.WeakDirichlet

/-- The full source main estimate produces the unique weak solution and representative. -/

theorem main_theorem
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
                  C / Real.sqrt |Real.log ε| :=

by
  exact LongRange.TwoScale.exists_weak_solution_main_estimate
    h614 h619 h66 h37 h637 h75 h82 d hd lam σ μ hσ hμ U hU M

end LongRange.Statements
