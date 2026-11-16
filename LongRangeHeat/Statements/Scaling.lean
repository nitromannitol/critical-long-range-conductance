import LongRangeHeat.Scaling

/-!
# Scaling identities for the heat equations

The identities and the annular normalization increment in equation (1.7).
-/

namespace LongRangeHeat.Statements

open Filter Topology LatticeProb LatticeProb.Euclidean.Lattice LongRange
open LatticeProb.Euclidean.LatticeAnnulusRiemann

noncomputable section

/-- Equation (1.7): halving space changes the lattice and continuum time scales. -/
theorem scaling_identity {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (a : Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) {t : ℝ} (ht : 0 ≤ t) (q : Site d) :
    latticeHeat (ε / 2) a (fun x => f (2 • x)) t q =
        latticeHeat ε a f ((4 * kappa d ε / kappa d (ε / 2)) * t) q ∧
      continuumHeat (fun x => f (2 • x)) t ((1 / 2 : ℝ) • physical ε q) =
        continuumHeat f (4 * t) (physical ε q) := by
  exact ⟨latticeHeat_half hd ⟨hε.1, by linarith [hε.2]⟩ a f t q,
    continuumHeat_half hd f ht _⟩

/-- The normalization increment in equation (1.7) is an annular sum with the stated limit. -/
theorem kappa_halving_increment {d : ℕ} (hd : 1 ≤ d) :
    (∀ ε : ℝ, 0 < ε → kappa d (ε / 2) - kappa d ε =
      ∑ w ∈ annulusIndices d (1 / ε),
        Real.rpow (radius (physical 1 w)) (-(d : ℝ))) ∧
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) :=
  ⟨fun _ hε => kappa_half_sub_eq_annulus_sum hε, tendsto_kappa_half_sub hd⟩

/-- The halving increment and its exact logarithmic normalization, as in equation (1.7). -/
theorem kappa_halving {d : ℕ} (hd : 1 ≤ d) :
    (∀ ε : ℝ, 0 < ε → kappa d (ε / 2) - kappa d ε =
      ∑ w ∈ annulusIndices d (1 / ε),
        Real.rpow (radius (physical 1 w)) (-(d : ℝ))) ∧
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) ∧
    Tendsto (fun ε : ℝ =>
      ((kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2)) * |Real.log ε|)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  exact ⟨(kappa_halving_increment hd).1, (kappa_halving_increment hd).2,
    kappa_half_ratio_tendsto hd⟩

end
end LongRangeHeat.Statements
