import LongRangeHeat.ScalingComparison
import LongRangeHeat.MainTheorem

/-!
# Supremum bounds for scaled heat errors

For smooth compactly supported data, the lattice heat errors at both scales are bounded on
bounded time intervals.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LongRange
open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-- The rescaled initial condition is smooth and compactly supported. -/
theorem smooth_compactSupport_dilate {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun x => f ((2 : ℝ) • x)) ∧ HasCompactSupport (fun x => f ((2 : ℝ) • x)) := by
  constructor
  · have h : ContDiff ℝ ∞ (fun x : Fin d → ℝ => (2 : ℝ) • x) :=
      contDiff_id.const_smul (2 : ℝ)
    exact hf.comp h
  · exact hfc.comp_smul (G₀ := ℝ) (by norm_num : (2 : ℝ) ≠ 0)

/-- The heat error at half spacing is bounded for rescaled initial data. -/
theorem bddAbove_latticeHeat_error_half (hd : 1 ≤ d) {ε lam T : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    BddAbove ((fun s => latticeNorm (ε / 2)
      (fun q => latticeHeat (ε / 2) a (fun x => f ((2 : ℝ) • x)) s q -
        continuumHeat (fun x => f ((2 : ℝ) • x)) s (physical (ε / 2) q))) '' Set.Icc 0 T) := by
  obtain ⟨hf₂, hfc₂⟩ := smooth_compactSupport_dilate hf hfc
  exact bddAbove_latticeHeat_error hd (by linarith [hε.1]) (by linarith [hε.2])
    hlam ha hf₂ hfc₂


/-- The continuum mismatch is controlled by the two bounded heat-error suprema. -/
theorem heat_scaling_error_le_sup_of_smooth (hd : 1 ≤ d) {ε lam T : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {t : ℝ} (ht : 0 ≤ t) (hT : 4 * t ≤ T) :
    Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
        latticeNorm ε (fun q => continuumHeat f (4 * t) (physical ε q) -
          continuumHeat f ((4 * kappa d ε / kappa d (ε / 2)) * t) (physical ε q)) ≤
      sSup ((fun s => latticeNorm (ε / 2)
        (fun q => latticeHeat (ε / 2) a (fun x => f ((2 : ℝ) • x)) s q -
          continuumHeat (fun x => f ((2 : ℝ) • x)) s (physical (ε / 2) q))) '' Set.Icc 0 T) +
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * sSup ((fun s => latticeNorm ε
        (fun q => latticeHeat ε a f s q - continuumHeat f s (physical ε q))) '' Set.Icc 0 T) := by
  have hB := bddAbove_latticeHeat_error (T := T) hd hε.1 (by linarith [hε.2]) hlam ha hf hfc
  have hBh := bddAbove_latticeHeat_error_half (T := T) hd hε hlam ha hf hfc
  have hdilate : (fun x : Fin d → ℝ => f ((2 : ℝ) • x)) =
      (fun x : Fin d → ℝ => f ((2 : ℕ) • x)) := by
    funext x
    congr 1
    exact Nat.cast_smul_eq_nsmul ℝ 2 x
  rw [hdilate] at hBh ⊢
  exact heat_scaling_error_le_sup hd hε hlam ha hf.continuous hfc ht hT hB hBh

end
end LongRangeHeat
