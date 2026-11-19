import LongRangeHeat.Statements.FddOfDavies
import LongRange.Support.External.ChenKimKumagaiWangDaviesProof

/-!
# Proposition 4.3 without cited hypotheses

Proposition 4.3 (`prop:fdd`) of the heat-kernel version, with every input of
Proposition 4.1 proved.
-/

namespace LongRangeHeat.Statements

open MeasureTheory Filter LatticeProb LatticeProb.Cadlag.HalfLine LatticeProb.Euclidean.Lattice
open scoped NNReal Topology
open LongRange (Edge)

/-- **Proposition 4.3** (`prop:fdd`, finite-dimensional marginals). Let `W` be a standard
Brownian motion in `ℝ^d` (given by a standard Brownian law `B` on `C([0, ∞), ℝ^d)`), let `k ≥ 1`
and let `0 ≤ t_1 < ⋯ < t_k`. Then, as `ε → 0` (along every sequence in `(0, 1/2)` tending to
`0`), the law of `(X^ε_{t_1}, …, X^ε_{t_k})` under the annealed law `P^ann_0 = E[P^a_0]`
converges weakly to the law of `d^{-1/2} (W_{t_1}, …, W_{t_k})`.

The heat-kernel bounds of Proposition 4.1 enter through `heat_kernel_bounds_unconditional`;
no cited result is assumed. Theorem 1.1 is used as a proved result. -/
theorem fdd_convergence_unconditional
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d)))
    {k : ℕ} (hk : 1 ≤ k) (t : Fin k → ℝ≥0) (ht : StrictMono t)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ProbabilityMeasure.map
        (LongRangeHeat.annealedLaw hd P a hP (hε n).1)
        (fun (X : LongRangeHeat.PathSpace d) (j : Fin k) => X.1 (t j))) atTop
      (𝓝 (ProbabilityMeasure.map B
        (fun (ω : BrownianPath d) (j : Fin k) => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t j)))) :=
  fdd_convergence_of_davies LatticeProb.External.chenKimKumagaiWangDavies_holds hd P a hP B hB
    hk t ht ε hε hε0

end LongRangeHeat.Statements
