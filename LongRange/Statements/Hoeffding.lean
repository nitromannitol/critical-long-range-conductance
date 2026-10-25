import LatticeProb.Prob.HoeffdingSeries.OsForm

/-!
# Hoeffding inequality for infinite sums

A statement-preserving wrapper for Proposition 2.1 (`prop:concentrationineq`).
-/

open MeasureTheory ProbabilityTheory Filter LatticeProb

/-- Proposition 2.1 (`prop:concentrationineq`): independent centred variables bounded by one with
square-summable weights have an almost surely and `L²`-convergent weighted series, whose absolute
value is `O₂(C (∑ aₙ²)^{1/2})` with a universal constant `C`. -/

theorem LongRange.Statements.hoeffding_infinite :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ℕ → ℝ),
      (∀ n, Measurable (X n)) → iIndepFun X P →
      (∀ n, ∫ ω, X n ω ∂P = 0) → (∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ 1) →
      Summable (fun n => a n ^ 2) →
      ∃ S : Ω → ℝ, MemLp S 2 P ∧
        (∀ᵐ ω ∂P, Tendsto (fun N => ∑ n ∈ Finset.range N, a n * X n ω) atTop
          (nhds (S ω))) ∧
        Tendsto (fun N => eLpNorm
          (fun ω => ∑ n ∈ Finset.range N, a n * X n ω - S ω) 2 P) atTop (nhds 0) ∧
        OsBound P 2 (C * Real.sqrt (∑' n, a n ^ 2)) (fun ω => |S ω|) :=

by exact LatticeProb.hoeffding_infinite
