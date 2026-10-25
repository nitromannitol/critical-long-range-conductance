import LongRange.Corrector.Monotonicity
import LongRange.Corrector.Definition
import LongRange.Poincare.Inequality

/-!
# Lemma 5.2: monotonicity of the corrector energy

Energy monotonicity combined with the Poincaré inequality on the smaller domain gives the norm
comparison with a constant depending only on `d`, `λ` and an upper bound for `diam U`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

/-- Lemma 5.2 (`l.corrector.monotonicity`) for correctors on nested bounded open domains. -/
theorem corrector_monotonicity (d : ℕ) (hd : 1 ≤ d) (lam R : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ U V : Set (Fin d → ℝ), IsOpen U → Bornology.IsBounded U →
      Bornology.IsBounded V → U ⊆ V → euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (p : Fin d → ℝ) (φU φV : Site d → ℝ),
      IsCorrectorSolution ε U a p φU → IsCorrectorSolution ε V a p φV →
        bilinForm ε a φU φU ≤ bilinForm ε a φV φV ∧
        h1CritSq ε φU + l2NormSq ε U φU ≤ C * (h1CritSq ε φV + l2NormSq ε V φV) := by
  obtain ⟨Cp, hCp, hP⟩ := poincare d hd R
  refine ⟨(1 + Cp) * lam⁻¹ ^ 2, by positivity, ?_⟩
  intro U V hUo hU hV hUV hdiam ε hε a ha p φU φV hφU hφV
  exact ⟨corrector_bilinForm_mono hd hε hU hV hUV hlam ha p hφU.1 hφU.2 hφV.1 hφV.2,
    corrector_norm_mono_of_poincare hd hε hU hV hUV hlam ha p hCp.le
      (hP U hUo hU hdiam ε hε) hφU.1 hφU.2 hφV.1 hφV.2⟩

end LongRange
