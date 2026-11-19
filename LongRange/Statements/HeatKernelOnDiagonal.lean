import LongRange.HeatKernel.UniformOnDiagonal

/-!
# Uniform on-diagonal heat-kernel bound

Proposition B.1 holds with one constant depending only on dimension and ellipticity. The
discrete on-diagonal estimate of Murugan–Saloff-Coste is proved for the critical lattice
kernel, so the cited theorem is not a hypothesis.
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

/-- Proposition B.1: one constant bounds the kernels of all admissible fields. -/
theorem LongRange.Statements.heatkernel_onDiagonal_proved
    (d : ℕ) (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ (t : ℝ≥0) (x y : Site d),
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) :=
  LongRange.unitHeat_onDiagonal_uniform_proved d hd hlam
