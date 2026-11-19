import LongRange.Support.Analysis.Davies.KilledConvergence
import LongRange.Support.Analysis.Davies.KilledEnergy

/-!
# Passing finite killed bounds to the full kernel

A bound uniform over all finite killed forms passes to the full transition
kernel by exhaustion.
-/

namespace LatticeProb.Davies

open Filter External
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Uniform finite-form semigroup bounds pass to the full transition kernel. -/
theorem ckkwKernel_le_of_semigroup_bound {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (rates : JumpChain.BoundedRates S)
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) (i j : S) (B : ℝ)
    (h : ∀ (U : Finset S) (x y : U), (killedForm rates hs U).semigroup t x y ≤ B) :
    ckkwKernel rates t i j ≤ B := by
  classical
  have hlim := tendsto_killedKernel rates t i j
  change (rates.transitionKernel t i).real {j} ≤ B
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop ({i, j} : Finset S)] with U hU
  have hi : i ∈ U := hU (by simp)
  have hj : j ∈ U := hU (by simp)
  rw [killedKernel_eq_semigroup rates hs U t ⟨i, hi⟩ ⟨j, hj⟩]
  exact h U ⟨i, hi⟩ ⟨j, hj⟩

end
end LatticeProb.Davies
