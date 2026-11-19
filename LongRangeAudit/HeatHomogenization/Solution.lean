import LongRangeAudit.HeatHomogenization.SolutionBridge

/-! # Quantitative homogenization of the heat equation -/

namespace LongRangeAudit.HeatHomogenization

noncomputable section
open MeasureTheory Set
open scoped ContDiff

/-- Theorem 1.1: the lattice heat flow approximates the continuum heat flow. -/
theorem main_theorem {d : ℕ} (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ),
      ConductanceLaw P lam a → ∀ T : ℝ, 0 ≤ T → ∀ ε ∈ Ioo (0 : ℝ) (1 / 2),
      (∀ r, BddAbove ((fun t => latticeNorm ε (fun q => latticeHeat ε (a r) f t q -
        restrict ε (continuumHeat f t) q)) '' Icc 0 T) ∧
        ∀ t ∈ Icc 0 T, MemL2 (fun q => latticeHeat ε (a r) f t q -
          restrict ε (continuumHeat f t) q)) ∧
      IsOq P 2 (fun r => sSup ((fun t => latticeNorm ε
        (fun q => latticeHeat ε (a r) f t q - restrict ε (continuumHeat f t) q)) '' Icc 0 T))
        (C * (1 + T) / Real.sqrt |Real.log ε|) := by
  obtain ⟨C, hC, h⟩ := _root_.LongRangeHeat.Statements.main_theorem hd hf hfc hlam
  refine ⟨C, hC, ?_⟩
  intro Ω _ P a ha T hT ε hε
  exact h Ω P a ((conductanceLaw_iff P lam a).mp ha) T hT ε hε

end
end LongRangeAudit.HeatHomogenization
