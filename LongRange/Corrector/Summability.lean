import LongRange.Calculus.Summability

/-!
# Generator summability for bounded perturbations

This bounded-range formulation applies the stage's affine generator summability theorem.
The affine slope is evaluated at physical lattice sites.
-/

namespace LongRange

open LatticeProb

/-- A bounded perturbation of a physical affine function has a summable generator series. -/
theorem summable_generator_affine_of_bounded_range {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    (q : Site d) (φ : Site d → ℝ) (hφ : Bornology.IsBounded (Set.range φ)) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) *
        ((linearFn ε p (q + w) + φ (q + w)) - (linearFn ε p q + φ q)) *
          jumpKernel (LatticeProb.Euclidean.Lattice.physical ε w)) := by
  obtain ⟨M, hM⟩ := hφ.exists_norm_le
  have hb (q : Site d) : |φ q| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM _ (Set.mem_range_self q)
  exact summable_generator_affine hd hε.1 hlam ha p
    ⟨M, (abs_nonneg (φ 0)).trans (hb 0), hb⟩ q

end LongRange
