import LatticeProb.Prob.McDiarmidIndep

/-!
# McDiarmid inequality

A statement-preserving wrapper for Proposition 2.2 (`prop.McDiarmid`).
-/

open MeasureTheory ProbabilityTheory LatticeProb

/-- Proposition 2.2 (`prop.McDiarmid`): for independent variables with values in `[λ, λ⁻¹]` and a
Borel function with bounded differences `aᵢ` on the cube, the two-sided tail bound
`2 exp(−2t²/∑ aᵢ²)` and the bound `O₂(C (∑ aᵢ²)^{1/2})` with a universal constant `C`. -/

theorem LongRange.Statements.mcdiarmid :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 → ∀ {n : ℕ} {Ω : Type*}
      [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P] (X : Fin n → Ω → ℝ),
      (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X P →
      (∀ i ω, X i ω ∈ Set.Icc lam lam⁻¹) →
      ∀ (f : (Fin n → ℝ) → ℝ), Measurable f → ∀ (a : Fin n → ℝ), (∀ i, 0 ≤ a i) →
      (∀ i (x : Fin n → ℝ) (y : ℝ), (∀ j, x j ∈ Set.Icc lam lam⁻¹) →
        y ∈ Set.Icc lam lam⁻¹ → |f x - f (Function.update x i y)| ≤ a i) →
      (∀ t : ℝ, 0 < t → P {ω | t < |f (fun i => X i ω) -
          ∫ ω', f (fun i => X i ω') ∂P|} ≤
          ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / ∑ i, a i ^ 2))) ∧
      OsBound P 2 (C * Real.sqrt (∑ i, a i ^ 2))
        (fun ω => |f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂P|) :=

by exact LatticeProb.mcdiarmid_indep
