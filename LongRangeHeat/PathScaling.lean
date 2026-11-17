import LongRangeHeat.Annealed
import LongRange.Support.Prob.Cadlag.HalfLine.Separable

/-!
# Space and time changes of paths

Continuous changes of the state and increasing time changes act measurably on half-line
càdlàg path space.
-/

namespace LongRangeHeat

open LatticeProb.Cadlag.HalfLine TopologicalSpace MeasureTheory

/-- Apply a continuous state map after an increasing time change. -/
def transformPath {E F : Type*} [MetricSpace E] [MetricSpace F]
    (f : E → F) (hf : Continuous f) (l : LambdaPrime) (x : D E) : D F :=
  ⟨fun t => f (x.1 (l t)), by
    have hx := x.2.comp_lambdaPrime l
    constructor
    · intro t
      exact hf.continuousAt.comp_continuousWithinAt (hx.1 t)
    · intro t ht
      obtain ⟨y, hy⟩ := hx.2 t ht
      exact ⟨f y, (hf.tendsto y).comp hy⟩⟩

/-- The path transformation acts pointwise on each time evaluation. -/
@[simp] theorem transformPath_apply {E F : Type*} [MetricSpace E] [MetricSpace F]
    (f : E → F) (hf : Continuous f) (l : LambdaPrime) (x : D E) (t : Time) :
    (transformPath f hf l x).1 t = f (x.1 (l t)) := rfl

/-- A continuous state map and a fixed increasing time change give a measurable path map. -/
theorem measurable_transformPath {E F : Type*} [MetricSpace E] [MetricSpace F]
    [SeparableSpace E] [SeparableSpace F] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] (f : E → F) (hf : Continuous f)
    (l : LambdaPrime) : Measurable (transformPath f hf l) := by
  apply measurable_iff_measurable_eval.mpr
  intro t
  exact hf.measurable.comp (measurable_eval (l t))

end LongRangeHeat
