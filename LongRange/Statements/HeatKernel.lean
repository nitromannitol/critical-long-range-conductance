import LongRange.HeatKernel.UniformOnDiagonal

/-!
# on-diagonal heat kernel bound

Proposition B.1 with one constant depending only on dimension and ellipticity.
The uniform constant form of the cited Murugan–Saloff-Coste theorem remains an
explicit hypothesis; its lattice specialization and the continuous-time bound are proved.
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

/-- Proposition B.1: one positive constant bounds the transition kernels of every
admissible symmetric conductance field on the Euclidean lattice. -/

theorem LongRange.Statements.heatkernel_onDiagonal
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform) (d : ℕ) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ (t : ℝ≥0) (x y : Site d),
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) :=

by exact LongRange.unitHeat_onDiagonal_uniform hMSC d hd hlam
