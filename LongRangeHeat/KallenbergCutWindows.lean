import LongRange.Support.Prob.Cadlag.HalfLine.Separable

/-!
# Cut windows for signed time changes

The total length of the windows between finitely many cuts and their images
is bounded by the number of cuts times the uniform displacement.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set MeasureTheory
open scoped ENNReal NNReal

/-- The union of windows between cuts and their images has volume at most
the number of cuts times the maximal displacement. -/
theorem volume_cut_windows_le (F : Finset Time) (l : LambdaPrime) (B : ℝ≥0)
    (hmove : ∀ c ∈ F, dist c (l c) ≤ B) :
    volume (⋃ c ∈ F, Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) ≤
      F.card * ENNReal.ofReal B := by
  calc
    _ ≤ ∑ c ∈ F, volume (Ico (min (c : ℝ) (l c : ℝ))
        (max (c : ℝ) (l c : ℝ))) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ F, ENNReal.ofReal B := by
      apply Finset.sum_le_sum
      intro c hc
      rw [Real.volume_Ico, max_sub_min_eq_abs]
      apply ENNReal.ofReal_le_ofReal
      simpa only [NNReal.dist_eq, abs_sub_comm] using hmove c hc
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]


/-- A discrepancy estimate outside signed cut windows gives an integrated
estimate with an explicit window and tail contribution. -/
theorem integratedDiscrepancy_le_of_cut_windows {E : Type*} [MetricSpace E]
    (x y : D E) (l : LambdaPrime) (T : Time) (F : Finset Time) (B : ℝ≥0)
    (ε : ℝ) (hmove : ∀ c ∈ F, dist c (l c) ≤ B)
    (hsmall : ∀ u : ℝ, 0 < u → u ≤ T →
      u ∉ (⋃ c ∈ F, Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) →
      discrepancy x y l u.toNNReal ≤ ENNReal.ofReal ε) :
    integratedDiscrepancy x y l ≤ ENNReal.ofReal ε +
      F.card * ENNReal.ofReal B + ENNReal.ofReal (Real.exp (-(T : ℝ))) := by
  have hmeas : MeasurableSet (⋃ c ∈ F,
      Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) :=
    MeasurableSet.biUnion (Finset.countable_toSet F) (fun _ _ => measurableSet_Ico)
  exact (integratedDiscrepancy_le_of_exceptional_set x y l T hmeas hsmall).trans
    (add_le_add (add_le_add le_rfl (volume_cut_windows_le F l B hmove)) le_rfl)


/-- Outside a cut window, a stopping time lies on the same side of the cut
and its image. -/
theorem lt_cut_iff_lt_image_of_not_mem_windows (F : Finset Time)
    (l : LambdaPrime) (u c : Time) (hc : c ∈ F)
    (hu : (u : ℝ) ∉ ⋃ c ∈ F,
      Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) :
    u < c ↔ u < l c := by
  have hout : (u : ℝ) ∉ Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ)) := by
    intro h
    exact hu (mem_iUnion₂.mpr ⟨c, hc, h⟩)
  by_cases h : c ≤ l c
  · have hr : (c : ℝ) ≤ (l c : ℝ) := h
    rw [min_eq_left hr, max_eq_right hr] at hout
    constructor
    · intro huc
      exact huc.trans_le h
    · intro hul
      by_contra huc
      apply hout
      exact ⟨le_of_not_gt huc, hul⟩
  · have hr : (l c : ℝ) ≤ (c : ℝ) := (le_of_not_ge h)
    rw [min_eq_right hr, max_eq_left hr] at hout
    constructor
    · intro huc
      by_contra hul
      apply hout
      exact ⟨le_of_not_gt hul, huc⟩
    · intro hul
      exact hul.trans_le hr

end LatticeProb.Cadlag.HalfLine
