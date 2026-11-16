import LongRangeHeat.MainTheorem

/-!
# Quantitative homogenization of the heat equation

Theorem 1.1 gives a Gaussian bound for the error between the lattice and continuum solutions.
-/

namespace LongRangeHeat.Statements

open LatticeProb LatticeProb.Euclidean.Lattice LongRange MeasureTheory Set
open scoped ContDiff

/-- **Theorem 1.1** (`thm:main`): quantitative homogenization of the heat equation. -/
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
        (C * (1 + T) / Real.sqrt |Real.log ε|) :=
  latticeHeat_homogenization hd hf hfc hlam

end LongRangeHeat.Statements
