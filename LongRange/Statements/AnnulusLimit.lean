import LongRange.Scaling.AnnulusLimit

/-!
# The annular normalization increment

Halving the mesh gives an exact Euclidean integer-annulus sum, whose limit is
`d V_d log 2`. The normalization ratio has two-sided inverse-logarithmic order.
-/

namespace LongRange.Statements

open Filter Topology LatticeProb.Euclidean.Lattice
open LatticeProb.Euclidean.LatticeAnnulusRiemann

/-- The exact annulus identity, its full positive-side limit, and the eventual two-sided
ratio order use the same dimension and the source normalization `kappa`. -/

theorem annulus_limit {d : ℕ} (hd : 1 ≤ d) :
    (∀ ε : ℝ, 0 < ε →
      kappa d (ε / 2) - kappa d ε =
        ∑ w ∈ annulusIndices d (1 / ε),
          Real.rpow (radius (physical 1 w)) (-(d : ℝ))) ∧
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) ∧
    (∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) δ →
        c / |Real.log ε| ≤ kappa d (ε / 2) / kappa d ε - 1 ∧
        kappa d (ε / 2) / kappa d ε - 1 ≤ C / |Real.log ε|) :=

by
  exact ⟨fun _ hε => LongRange.kappa_half_sub_eq_annulus_sum hε,
    LongRange.tendsto_kappa_half_sub hd, LongRange.kappa_half_ratio_order hd⟩

end LongRange.Statements
