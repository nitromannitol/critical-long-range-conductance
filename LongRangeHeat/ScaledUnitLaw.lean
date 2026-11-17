import LongRangeHeat.UnitAnnealed

/-!
# Scaling laws of the unit walk

Composing deterministic space and time scalings identifies transformations of the rescaled
walk law with transformations of the unit walk law.
-/

namespace LongRangeHeat

open MeasureTheory LatticeProb.Cadlag.HalfLine LatticeProb.Euclidean.Lattice
open scoped NNReal
open LongRange (Edge)

noncomputable section

/-- Two deterministic space-time scalings compose by multiplying their parameters. -/
theorem scaledPath_scaledPath {d : ℕ} (b b' : ℝ)
    (c c' : {c : ℝ≥0 // 0 < c}) (x : PathSpace d) :
    scaledPath b c (scaledPath b' c' x) =
      scaledPath (b * b') ⟨c'.1 * c.1, mul_pos c'.2 c.2⟩ x := by
  apply Subtype.ext
  funext t
  simp only [scaledPath, transformPath_apply, dilation, OrderIso.mulLeft₀_apply,
    mul_smul, mul_assoc]

/-- A scaled annealed walk law is a single scaling of the unit annealed law. -/
theorem annealedLaw_map_scaledPath {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) (b : ℝ)
    (c : {c : ℝ≥0 // 0 < c}) :
    let r : {r : ℝ≥0 // 0 < r} := ⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
      le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
      one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩
    (annealedLaw hd P a hP hε.1).map (scaledPath b c) =
      (unitAnnealedLaw hd P a hP).map
        (scaledPath (b * ε) ⟨r.1 * c.1, mul_pos r.2 c.2⟩) := by
  dsimp only
  let r : {r : ℝ≥0 // 0 < r} := ⟨⟨1 / (LongRange.kappa d ε * ε ^ 2),
    le_of_lt (one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _)))⟩,
    one_div_pos.mpr (mul_pos (LongRange.kappa_pos hd hε) (pow_pos hε.1 _))⟩
  have hm (q : ℝ) (s : {c : ℝ≥0 // 0 < c}) : Measurable (scaledPath (d := d) q s) :=
    measurable_transformPath (fun y : EuclideanSpace ℝ (Fin d) => q • y)
      (continuous_const_smul q) (dilation s.1 s.2)
  apply Subtype.ext
  change Measure.map (scaledPath b c) (annealedLaw hd P a hP hε.1 : Measure (PathSpace d)) =
    Measure.map (scaledPath (b * ε) ⟨r.1 * c.1, mul_pos r.2 c.2⟩)
      (unitAnnealedLaw hd P a hP : Measure (PathSpace d))
  rw [annealedLaw_eq_scaled_unit hd hε P a hP, Measure.map_map (hm b c) (hm ε r)]
  congr 1
  funext x
  exact scaledPath_scaledPath b ε c r x

end
end LongRangeHeat
