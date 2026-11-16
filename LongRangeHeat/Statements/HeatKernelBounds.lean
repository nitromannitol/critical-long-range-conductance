import LongRangeHeat.HeatKernelBounds

/-!
# Proposition 4.1: heat-kernel bounds

Statement of Proposition 4.1 (`prop:hk`) of the heat-kernel version: the on-diagonal bound and the
displacement bound for the walk `X^ε` with generator `L^ε`, valid for every realization of the
conductances.
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

The cited heat-kernel theorems enter as the hypotheses `hMSC` (Murugan–Saloff-Coste on-diagonal
bound, uniform in the kernel constants), `hNash` and `hDavies` (the Nash and Davies inputs of
Chen–Kim–Kumagai–Wang for the off-diagonal bound). The off-diagonal bound of Step 2 is derived
from these inputs, not from the stability theorem and its extension to graphs that the paper
cites. -/
theorem heat_kernel_bounds
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ x y : Site d,
      (∀ h : ℝ≥0, ε ≤ h →
        (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε.1 hlam.1 a ha).transitionKernel h x).real {y} ≤
          C / (h : ℝ) ^ ((d : ℝ) / 2)) ∧
      (∀ h : ℝ≥0, 0 < h → ∀ R : ℝ, ε ≤ R →
        ((LongRange.walkRates hd hε.1 hlam.1 a ha).transitionKernel h x).real
            {z | R < radius (physical ε (z - x))} ≤
          C * h * (1 + Real.log (1 + R)) / R ^ 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := LongRangeHeat.heat_kernel_on_diagonal hMSC hd hlam.1
  obtain ⟨C₂, hC₂, h₂⟩ := LongRangeHeat.heat_kernel_displacement hMSC hNash hDavies hd hlam.1
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun ε hε a ha x y => ⟨fun h hεh => ?_,
    fun h hh R hεR => ?_⟩⟩
  · exact (h₁ ε hε a ha x y h hεh).trans (div_le_div_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (NNReal.coe_nonneg h) _))
  · have hR0 : 0 < R := lt_of_lt_of_le hε.1 hεR
    have hlg : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
    refine (h₂ ε hε a ha x h hh R hεR).trans ?_
    gcongr
    exact le_max_right _ _
