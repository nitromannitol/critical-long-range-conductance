import LongRange.Support.Prob.Cadlag.HalfLine.TerminalJump

/-!
# Averaging bounded path increments

An increment between two nearby times is controlled by averaged forward increments.
-/

namespace LatticeProb.Cadlag.HalfLine

open MeasureTheory Set
open scoped ENNReal

variable {E : Type} [MetricSpace E]

/-- The bounded distance satisfies the triangle inequality. -/
theorem boundedDistance_triangle (a b c : E) :
    boundedDistance a c ≤ boundedDistance a b + boundedDistance b c := by
  have hq (x y : E) : q x y ≠ ∞ :=
    ne_of_lt ((min_le_right (edist x y) (1 : ℝ≥0∞)).trans_lt ENNReal.one_lt_top)
  simp only [boundedDistance_eq_toReal_q, ← ENNReal.toReal_add (hq a b) (hq b c)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hq a b, hq b c⟩) (q_triangle a b c)

variable [MeasurableSpace E] [BorelSpace E] [TopologicalSpace.SeparableSpace E]

/-- Averaging the triangle inequality gives the pathwise bound in Lemma 16.12. -/
theorem averaged_boundedDistance_le (x : D E) (σ τ : Time) {δ : ℝ} (hδ : 0 ≤ δ)
    (hστ : σ ≤ τ) (hnear : (τ : ℝ) ≤ (σ : ℝ) + δ) :
    δ * boundedDistance (x.1 σ) (x.1 τ) ≤
      (∫ h in (0 : ℝ)..2 * δ,
        boundedDistance (x.1 σ) (x.1 ((σ : ℝ) + h).toNNReal)) +
      ∫ h in (0 : ℝ)..δ,
        boundedDistance (x.1 τ) (x.1 ((τ : ℝ) + h).toNNReal) := by
  let f : ℝ → ℝ := fun t => boundedDistance (x.1 σ) (x.1 t.toNNReal)
  let g : ℝ → ℝ := fun t => boundedDistance (x.1 τ) (x.1 t.toNNReal)
  have hfi (a b : ℝ) : IntervalIntegrable f volume a b := by
    simpa only [f, Real.toNNReal_coe] using
      intervalIntegrable_boundedDistance x (σ : ℝ) a b
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b := by
    simpa only [g, Real.toNNReal_coe] using
      intervalIntegrable_boundedDistance x (τ : ℝ) a b
  have hshiftf : IntervalIntegrable (fun h => f ((τ : ℝ) + h)) volume 0 δ := by
    simpa only [add_zero, add_sub_cancel_left, sub_self] using
      (hfi ((τ : ℝ) + 0) ((τ : ℝ) + δ)).comp_add_left (τ : ℝ)
  have hshiftg : IntervalIntegrable (fun h => g ((τ : ℝ) + h)) volume 0 δ := by
    simpa only [add_zero, add_sub_cancel_left, sub_self] using
      (hgi ((τ : ℝ) + 0) ((τ : ℝ) + δ)).comp_add_left (τ : ℝ)
  have htri : δ * boundedDistance (x.1 σ) (x.1 τ) ≤
      ∫ h in (0 : ℝ)..δ, f ((τ : ℝ) + h) + g ((τ : ℝ) + h) := by
    have h := intervalIntegral.integral_mono_on hδ intervalIntegrable_const
      (hshiftf.add hshiftg) (fun h _ => by
        have hh := boundedDistance_triangle (x.1 σ) (x.1 ((τ : ℝ) + h).toNNReal) (x.1 τ)
        simpa only [f, g, boundedDistance, dist_comm] using hh)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      f, g, boundedDistance, dist_comm] using h
  have hcompare : (∫ h in (0 : ℝ)..δ, f ((τ : ℝ) + h)) ≤
      ∫ h in (0 : ℝ)..2 * δ, f ((σ : ℝ) + h) := by
    rw [intervalIntegral.integral_comp_add_left, intervalIntegral.integral_comp_add_left]
    apply intervalIntegral.integral_mono_interval _ (by linarith) _
      (Filter.Eventually.of_forall fun t => boundedDistance_nonneg _ _) (hfi _ _)
    · simpa only [add_zero] using (show (σ : ℝ) ≤ (τ : ℝ) by exact_mod_cast hστ)
    · linarith
  calc
    _ ≤ (∫ h in (0 : ℝ)..δ, f ((τ : ℝ) + h)) +
        ∫ h in (0 : ℝ)..δ, g ((τ : ℝ) + h) := by
      simpa only [intervalIntegral.integral_add hshiftf hshiftg] using htri
    _ ≤ _ := add_le_add hcompare le_rfl

end LatticeProb.Cadlag.HalfLine
