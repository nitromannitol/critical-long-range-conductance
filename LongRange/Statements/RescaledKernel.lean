import LongRange.HeatKernel.RescaledKilled

/-!
# The actual full and killed position laws and their common rescaled minimum bound
-/

namespace LongRange.Statements

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

/-- At every nonnegative time the densities are the actual endpoint and survival
masses. One positive `C(d, lam)` bounds both densities at every positive time and scale. -/

theorem rescaled_kernel
    (hMSCUniform : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (d : ℕ) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo 0 1,
      ∀ a : Edge d → ℝ, ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
      ∀ t : ℝ≥0, ∀ x y : Site d,
      (LongRange.rescaledDensity hd hε hlam a ha t x y = (ε ^ d)⁻¹ *
        ((walkRates hd hε.1 hlam a ha).regularLaw (MeasureTheory.Measure.dirac x)).real
          {h | physical ε (h.position t) = physical ε y}) ∧
      (LongRange.rescaledDensity hd hε hlam a ha t x y = (ε ^ d)⁻¹ *
        ((unitRates hd hlam a ha).transitionKernel
          (NNReal.mk (1 / (kappa d ε * ε ^ 2))
            (by positivity [kappa_pos hd hε]) * t) x).real {y}) ∧
      (∀ U : Set (Fin d → ℝ),
        LongRange.rescaledKilledDensity hd hε hlam a ha U t x y = (ε ^ d)⁻¹ *
          ((walkRates hd hε.1 hlam a ha).regularLaw (MeasureTheory.Measure.dirac x)).real
            {h | physical ε (h.position t) = physical ε y ∧
              ∀ s ≤ t, physical ε (h.position s) ∈ U}) ∧
      (∀ U : Set (Fin d → ℝ),
        LongRange.rescaledKilledDensity hd hε hlam a ha U t x y ≤
          LongRange.rescaledDensity hd hε hlam a ha t x y) ∧
      (0 < t → x ≠ y →
        let bound := C * min
          ((ε ^ 2 + t / kappa d ε * Real.log (2 + t / (kappa d ε * ε ^ 2))) ^
            (-((d : ℝ) / 2)))
          (t / kappa d ε * Real.log (2 + radius (physical ε (y - x)) / ε) /
            radius (physical ε (y - x)) ^ (d + 2))
        LongRange.rescaledDensity hd hε hlam a ha t x y ≤ bound ∧
          ∀ U : Set (Fin d → ℝ),
            LongRange.rescaledKilledDensity hd hε hlam a ha U t x y ≤ bound) :=

by
  obtain ⟨C, hC, hb⟩ :=
    rescaledDensity_and_killed_offDiagonal_uniform hMSCUniform hNash hDavies d hd hlam
  refine ⟨C, hC, ?_⟩
  intro ε hε a ha t x y
  refine ⟨rescaledDensity_eq_position_mass hd hε hlam a ha t x y,
    rescaledDensity_eq_unit hd hε hlam a ha t x y, ?_, ?_, ?_⟩
  · intro U
    exact rescaledKilledDensity_eq_position_mass hd hε hlam a ha U t x y
  · intro U
    exact rescaledKilledDensity_le hd hε hlam a ha U t x y
  · intro ht hxy
    exact hb ε hε a ha t ht x y hxy

end

end LongRange.Statements
