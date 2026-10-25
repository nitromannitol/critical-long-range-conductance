import LongRange.HeatKernel.UniformOffDiagonal

/-!
# off-diagonal heat kernel bound

Proposition B.2 with one constant depending only on dimension and ellipticity.
The Murugan–Saloff-Coste and Chen–Kim–Kumagai–Wang cited inputs remain explicit
hypotheses. The truncation, Nash, Davies and indexed uniform-constant adapters are proved.
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

/-- Proposition B.2: the original minimum heat bound holds uniformly over every
admissible symmetric conductance field, every positive time and distinct sites. -/

theorem LongRange.Statements.heatkernel_offDiagonal
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies) (d : ℕ) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
      ∀ t : ℝ≥0, 0 < t → ∀ x y : Site d, x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * min ((1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
          (t * Real.log (2 + radius (physical 1 (y - x))) /
            radius (physical 1 (y - x)) ^ (d + 2)) :=

by exact LongRange.unitHeat_offDiagonal_uniform hMSC hNash hDavies d hd hlam
