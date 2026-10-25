import LongRange.Model.Corrector
import LongRange.Corrector.Energy

/-!
# Well-definedness of the corrector

Under the standing assumptions the corrector functional has a unique minimizer, and the
minimizers are exactly the solutions of the corrector equation.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

/-- Definition 3.1 is well posed: a unique minimizer exists, and minimizers are exactly the
solutions of (eq:elleqdefnu). -/
theorem corrector_wellDefined {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) :
    (∃! φ : Site d → ℝ, IsCorrectorMinimizer ε U a p φ) ∧
      ∀ φ : Site d → ℝ, IsCorrectorMinimizer ε U a p φ ↔ IsCorrectorSolution ε U a p φ :=
  ⟨existsUnique_correctorMinimizer hd hε hU hlam ha p, fun _ =>
    ⟨fun h => ⟨h.1, (isCorrectorMinimizer_iff hd hε hU hlam ha p h.1).mp h.2⟩,
      fun h => ⟨h.1, (isCorrectorMinimizer_iff hd hε hU hlam ha p h.1).mpr h.2⟩⟩⟩

/-- A corrector solution is a minimizer. -/
theorem IsCorrectorSolution.isCorrectorMinimizer {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {p : Fin d → ℝ} {φ : Site d → ℝ} (h : IsCorrectorSolution ε U a p φ) :
    IsCorrectorMinimizer ε U a p φ :=
  ((corrector_wellDefined hd hε hU hlam ha p).2 φ).mpr h

end LongRange
