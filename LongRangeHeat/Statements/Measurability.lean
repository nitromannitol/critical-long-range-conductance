import LongRangeHeat.FddMarginals
import LongRangeHeat.UnscaledLimit

/-!
# Measurability of the maps in Proposition 4.3 and Theorem 1.2

Proposition 4.3 and the unscaled form of Theorem 1.2 push laws forward along evaluation maps and
along space-time scalings of paths. These maps are measurable, so the pushforwards are the image
laws.
-/

namespace LongRangeHeat.Statements

open MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine
open scoped NNReal

/-- The evaluation maps of Proposition 4.3 are measurable: `X ↦ (X_{t_1}, …, X_{t_k})` on
`D([0, ∞), ℝ^d)` and `ω ↦ c (ω_{t_1}, …, ω_{t_k})` on `C([0, ∞), ℝ^d)`, for all times
`t_1, …, t_k` and every scalar `c`. -/
theorem measurable_fdd_maps {d k : ℕ} (t : Fin k → ℝ≥0) (c : ℝ) :
    Measurable (fun (X : LongRangeHeat.PathSpace d) (j : Fin k) => X.1 (t j)) ∧
      Measurable (fun (ω : BrownianPath d) (j : Fin k) => c • ω (t j)) :=
  ⟨measurable_pi_iff.mpr fun j => measurable_eval (t j),
    LongRangeHeat.measurable_brownianEval t c⟩

/-- The space-time scaling `X ↦ (b X_{c s})_{s ≥ 0}` of the unscaled form of Theorem 1.2 is a
measurable map of `D([0, ∞), ℝ^d)` for every `b` and every `c > 0`. -/
theorem measurable_scaled_path {d : ℕ} (b : ℝ) (c : {c : ℝ≥0 // 0 < c}) :
    Measurable (LongRangeHeat.scaledPath (d := d) b c) :=
  (LongRangeHeat.measurable_scaledPath (d := d)).comp
    ((measurable_const (a := ((b, c) : ℝ × {c : ℝ≥0 // 0 < c}))).prodMk measurable_id)

end LongRangeHeat.Statements
