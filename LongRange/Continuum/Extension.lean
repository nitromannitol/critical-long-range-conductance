import LatticeProb.External.GilbargTrudinger

/-!
# Compactly supported regular extension

Gilbarg–Trudinger's extension input, applied with the whole space as neighborhood,
gives a compactly supported global extension with the global coordinate Hölder bound.
-/

namespace LongRange

/-- The cited extension theorem gives a compactly supported global `C²` extension,
with a uniform global `C^{2,σ}` bound, by choosing the whole space as neighborhood. -/
theorem regular_extension_of_gt (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    {d : ℕ} (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) {U : Set (Fin d → ℝ)}
    (hU : LatticeProb.Elliptic.IsC2HolderDomain σ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ, ContDiffOn ℝ 2 u U →
      LatticeProb.Elliptic.c2HolderNorm σ U u < ⊤ →
      ∃ v : (Fin d → ℝ) → ℝ,
        ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ Set.EqOn v u U ∧
        LatticeProb.Elliptic.c2HolderNorm σ Set.univ v ≤
          ENNReal.ofReal C * LatticeProb.Elliptic.c2HolderNorm σ U u := by
  obtain ⟨C, hC, hext⟩ :=
    h637 d hd σ hσ hσ1 U hU Set.univ isOpen_univ (Set.subset_univ _)
  refine ⟨C, hC, ?_⟩
  intro u hu hnorm
  obtain ⟨v, hv, hcompact, _, heq, hbound⟩ := hext u hu hnorm
  exact ⟨v, hv, hcompact, heq, hbound⟩

end LongRange
