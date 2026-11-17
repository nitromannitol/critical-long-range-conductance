import LongRangeHeat.ScalingConvergence
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Weak convergence under path scalings

A deterministic converging space-time scaling preserves weak convergence when the limiting
law is supported on continuous paths.
-/

namespace LongRangeHeat

open Set Filter MeasureTheory LatticeProb.Cadlag.HalfLine
open scoped Topology NNReal

noncomputable section

/-- Deterministic space-time scalings transfer a weak limit supported on continuous paths. -/
theorem tendsto_map_scaledPath {d : ℕ} {μ : ℕ → ProbabilityMeasure (PathSpace d)}
    {ν : ProbabilityMeasure (PathSpace d)} (hμ : Tendsto μ atTop (𝓝 ν))
    (hν : ∀ᵐ y ∂(ν : Measure (PathSpace d)), Continuous y.1)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    {c : ℕ → {c : ℝ≥0 // 0 < c}} (hc : Tendsto c atTop (𝓝 ⟨1, zero_lt_one⟩)) :
    Tendsto (fun n => (μ n).map (scaledPath (b n) (c n))) atTop
      (𝓝 (ν.map (scaledPath B ⟨1, zero_lt_one⟩))) := by
  let p : ℕ → ℝ × {c : ℝ≥0 // 0 < c} := fun n => (b n, c n)
  let p₀ : ℝ × {c : ℝ≥0 // 0 < c} := (B, ⟨1, zero_lt_one⟩)
  have hp : Tendsto p atTop (𝓝 p₀) := hb.prodMk_nhds hc
  have hprod : Tendsto (fun n => (diracProba (p n)).prod (μ n)) atTop
      (𝓝 ((diracProba p₀).prod ν)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (((continuous_diracProba.continuousAt.tendsto.comp hp).prodMk_nhds hμ))
  let F : (ℝ × {c : ℝ≥0 // 0 < c}) × PathSpace d → PathSpace d := fun q =>
    scaledPath q.1.1 q.1.2 q.2
  have hF : Measurable F := measurable_scaledPath
  have hcont : ∀ᵐ q ∂(((diracProba p₀).prod ν : ProbabilityMeasure _) : Measure _),
      ContinuousAt F q := by
    change ∀ᵐ q ∂(Measure.dirac p₀).prod (ν : Measure (PathSpace d)), ContinuousAt F q
    rw [Measure.dirac_prod, ae_map_iff measurable_prodMk_left.aemeasurable
      (measurableSet_of_continuousAt F)]
    exact hν.mono fun y hy => continuousAt_scaledPath B y hy
  have hmap := ProbabilityMeasure.tendsto_map_of_ae_continuousAt hprod hF hcont
  have heq (z : ℝ × {c : ℝ≥0 // 0 < c}) (m : ProbabilityMeasure (PathSpace d)) :
      ((diracProba z).prod m).map F = m.map (scaledPath z.1 z.2) := by
    apply Subtype.ext
    change Measure.map F ((Measure.dirac z).prod (m : Measure (PathSpace d))) = _
    rw [Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
    rfl
  simpa only [heq] using hmap

end
end LongRangeHeat
