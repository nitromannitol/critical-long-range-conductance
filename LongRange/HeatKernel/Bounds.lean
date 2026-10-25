import LongRange.HeatKernel.OnDiagonal
import LongRange.HeatKernel.OffDiagonal
import LatticeProb.Graph.LongRangeKernel.LatticeGaussianLower
import LatticeProb.Analysis.NashProduct

/-!
# Heat kernel bounds from the cited inputs

Propositions B.1 and B.2 with the Gaussian lower bound for the lattice walk and the product
condition for the Nash profile discharged, so that the on-diagonal estimate rests only on the
cited Murugan–Saloff-Coste theorem, and the off-diagonal estimate on it and the two cited
Chen–Kim–Kumagai–Wang results.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

variable {d : ℕ}

/-- Proposition B.1 (`p.heatkernel`): the unit-scale walk satisfies
`p_t(x,y) ≤ C (1 + t log(2+t))^{-d/2}`, with a constant depending on the configuration. -/
theorem unitHeat_onDiagonal_of_msc (hMSC : LatticeProb.External.MuruganSaloffCoste)
    (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x y : Site d),
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) :=
  unitHeat_onDiagonal hMSC hd
    (LatticeProb.Graph.LongRangeKernel.weightedLattice_gaussian_lower hd) hlam a ha

/-- Proposition B.2 (`p.heatkernel.offdiag`): for `t > 0` and `x ≠ y`,
`p_t(x,y) ≤ C min((1 + t log(2+t))^{-d/2}, t log(2+|x−y|)/|x−y|^{d+2})`, with a constant
depending on the configuration. -/
theorem unitHeat_offDiagonal_of_cited (hMSC : LatticeProb.External.MuruganSaloffCoste)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x y : Site d, x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * min ((1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
          (t * Real.log (2 + radius (physical 1 (y - x))) /
            radius (physical 1 (y - x)) ^ (d + 2)) :=
  unitHeat_offDiagonal hMSC hNash hDavies hd
    (LatticeProb.Graph.LongRangeKernel.weightedLattice_gaussian_lower hd)
    (fun _ hα ↦ (LatticeProb.nashProfile_productProfile hd hα).2) hlam a ha

end LongRange
