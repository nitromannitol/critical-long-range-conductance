import LongRangeHeat.Statements.HeatKernelBoundsOfDavies
import LongRange.Support.External.ChenKimKumagaiWangDaviesProof

/-!
# Proposition 4.1 without cited hypotheses

Proposition 4.1 (`prop:hk`) of the heat-kernel version. The on-diagonal bound of Step 1, the
Nash inequality and the Davies estimate used in Step 2 are all proved.
-/

namespace LongRangeHeat.Statements

open Set MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal
open LongRange (Edge)

/-- **Proposition 4.1** (`prop:hk`, heat-kernel bounds). Let `X^ε` be the walk with generator
`L^ε` (`LongRange.walkRates`), `P^a_x[X^ε_h ∈ ·]` its transition kernel at time `h` from `x`,
and `p^ε_h(x, y) = ε^{-d} P^a_x[X^ε_h = y]` its heat kernel. For `d ≥ 1` and `λ ∈ (0, 1]`
there is `C = C(d, λ) < ∞` such that, for every `ε ∈ (0, 1/2)`, every realization `a` of the
conductances with values in `[λ, λ⁻¹]` and all `x, y ∈ εℤ^d`:

* (i) on-diagonal bound: `p^ε_h(x, y) ≤ C / h^{d/2}` for every `h ≥ ε`;
* (ii) displacement bound: `P^a_x[|X^ε_h - x| > R] ≤ C h (1 + ln (1 + R)) / R²` for every `h > 0`
  and every `R ≥ ε`.

No cited result is assumed. The on-diagonal estimate of Step 1, which the paper takes from
Murugan–Saloff-Coste (Theorem 1.1), is proved for the critical lattice kernel; the Nash
inequality of Chen–Kim–Kumagai–Wang (Proposition 3.1(ii),
`LatticeProb.External.chenKimKumagaiWangNash_holds`) and their Davies estimate (Theorem 4.4 with
Example 4.3, `LatticeProb.External.chenKimKumagaiWangDavies_holds`) used in Step 2 are proved. -/
theorem heat_kernel_bounds_unconditional
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ x y : Site d,
      (∀ h : ℝ≥0, ε ≤ h →
        (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε.1 hlam.1 a ha).transitionKernel h x).real {y} ≤
          C / (h : ℝ) ^ ((d : ℝ) / 2)) ∧
      (∀ h : ℝ≥0, 0 < h → ∀ R : ℝ, ε ≤ R →
        ((LongRange.walkRates hd hε.1 hlam.1 a ha).transitionKernel h x).real
            {z | R < radius (physical ε (z - x))} ≤
          C * h * (1 + Real.log (1 + R)) / R ^ 2) :=
  heat_kernel_bounds_of_davies LatticeProb.External.chenKimKumagaiWangDavies_holds hd hlam

end LongRangeHeat.Statements
