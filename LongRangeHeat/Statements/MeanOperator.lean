import LongRangeHeat.MeanOperator

/-!
# The identity (2.1) and Lemma 3.1

The second moments of the short jumps and the consistency of the mean operator
`L̄ = meanGenerator ε` of (3.1) with the continuum solution `ū = continuumHeat f` of (1.5). The sum
over `z ∈ εℤ^d` with `0 < |z| ≤ 1` runs over the integer sites `q ∈ unitBallIndices d ε` with
`z = εq`, and `∂_s ū_s(x)` is the right time derivative `derivWithin (fun r => ū(r, x)) (Ici s) s`,
which equals `(2d)⁻¹ Δ ū_s(x)` (`LongRangeHeat.derivWithin_continuumHeat`).
-/

namespace LongRangeHeat.Statements

open Set LongRange LatticeProb LatticeProb.Euclidean.Lattice
open scoped ContDiff

variable {d : ℕ}

/-- **(2.1)** (`eq:second.moment`): for every `ε ∈ (0, 1/2)` and `1 ≤ i, j ≤ d`,
`ε^d ∑_{z ∈ εℤ^d, 0 < |z| ≤ 1} J(z) z_i z_j = (κ_ε / d) δ_{ij}`. -/
theorem second_moment (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) (i j : Fin d) :
    ε ^ d * ∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * physical ε q i * physical ε q j =
      kappa d ε / d * if i = j then 1 else 0 :=
  second_moment_eq hd ⟨hε.1, by linarith [hε.2]⟩ i j

/-- **Lemma 3.1** (`lem:mean`, consistency of the mean operator). For `f ∈ C_c^∞(ℝ^d)` there is
`C = C(d, f)` such that, for every `ε ∈ (0, 1/2)` and every `s ≥ 0`, the lattice function
`∂_s ū_s - L̄ ū_s` lies in `L²(εℤ^d)` and `‖∂_s ū_s - L̄ ū_s‖_{L²(εℤ^d)} ≤ C / κ_ε`. -/
theorem mean_operator_consistency (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s →
      MemL2 (fun q : Site d => derivWithin (fun r => continuumHeat f r (physical ε q)) (Ici s) s -
        meanGenerator ε (restrict ε (continuumHeat f s)) q) ∧
      latticeNorm ε (fun q : Site d =>
        derivWithin (fun r => continuumHeat f r (physical ε q)) (Ici s) s -
          meanGenerator ε (restrict ε (continuumHeat f s)) q) ≤ C / kappa d ε :=
  _root_.LongRangeHeat.mean_operator_consistency hd hf hfc

end LongRangeHeat.Statements
