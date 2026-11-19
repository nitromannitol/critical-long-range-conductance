import LongRangeHeat.KallenbergCutWindows
import LongRangeHeat.KallenbergPartitionTimeChange

/-!
# Stopped indices of aligned partitions

Outside cut windows, independently stopped times have the same index in
aligned finite step partitions.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set MeasureTheory
open scoped ENNReal NNReal

/-- Two times have the same step index if they have the same comparison
with every pair of corresponding cuts. -/
theorem stepIndex_eq_of_cut_comparisons {N : ℕ} (s r : Fin N → Time) (a b : Time)
    (h : ∀ i, a < s i ↔ b < r i) : stepIndex s a = stepIndex r b := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [stepIndex]
    by_cases ha : a < s 0
    · have hb : b < r 0 := (h 0).mp ha
      simp only [ha, hb, ite_true]
    · have hb : ¬ b < r 0 := fun hb => ha ((h 0).mpr hb)
      simp only [ha, hb, ite_false]
      exact congrArg Fin.succ (ih (fun i => s i.succ) (fun i => r i.succ)
        (fun i => h i.succ))

/-- Outside the windows of the cuts, independently stopped times have
the same index in a partition and its time-changed image. -/
theorem stepIndex_stopped_timeChange (N : ℕ) (s : Fin N → Time)
    (l : LambdaPrime) (t u : Time)
    (hside : ∀ i, u < s i ↔ u < l (s i)) :
    stepIndex s (min t u) = stepIndex (fun i => l (s i)) (min (l t) u) := by
  apply stepIndex_eq_of_cut_comparisons
  intro i
  simp only [min_lt_iff, l.lt_iff_lt, hside i]


/-- Outside the cut windows, two aligned step paths with the same values
have zero stopped discrepancy. -/
theorem discrepancy_stepPaths_eq_zero_of_not_mem_windows {E : Type*} [MetricSpace E]
    (N : ℕ) (s : Fin N → Time) (v : Fin (N + 1) → E) (l : LambdaPrime)
    (u : Time) (hu : (u : ℝ) ∉ ⋃ c ∈ Finset.univ.image s,
      Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) :
    discrepancy (stepPath s v) (stepPath (fun i => l (s i)) v) l u = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro t
  have hside (i : Fin N) : u < s i ↔ u < l (s i) :=
    lt_cut_iff_lt_image_of_not_mem_windows (Finset.univ.image s) l u (s i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hu
  have hi := stepIndex_stopped_timeChange N s l t u hside
  change q (v (stepIndex s (min t u)))
    (v (stepIndex (fun i => l (s i)) (min (l t) u))) ≤ 0
  rw [← hi]
  simp only [q, edist_self, min_eq_left (show (0 : ℝ≥0∞) ≤ 1 from zero_le_one)]
  exact le_rfl

/-- Aligned finite step paths with common values have integrated discrepancy
bounded by the total cut-window volume and the exponential tail. -/
theorem integratedDiscrepancy_stepPaths_le {E : Type*} [MetricSpace E]
    (N : ℕ) (s : Fin N → Time) (v : Fin (N + 1) → E)
    (l : LambdaPrime) (T : Time) (B : ℝ≥0)
    (hmove : ∀ i, dist (s i) (l (s i)) ≤ B) :
    integratedDiscrepancy (stepPath s v) (stepPath (fun i => l (s i)) v) l ≤
      (Finset.univ.image s).card * ENNReal.ofReal B +
        ENNReal.ofReal (Real.exp (-(T : ℝ))) := by
  let F : Finset Time := Finset.univ.image s
  have hmove' : ∀ c ∈ F, dist c (l c) ≤ B := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact hmove i
  have hsmall : ∀ u : ℝ, 0 < u → u ≤ T →
      u ∉ (⋃ c ∈ F, Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) →
      discrepancy (stepPath s v) (stepPath (fun i => l (s i)) v) l u.toNNReal ≤
        ENNReal.ofReal 0 := by
    intro u hu _ hout
    have hout' : (u.toNNReal : ℝ) ∉ (⋃ c ∈ F,
        Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) := by
      simpa only [Real.coe_toNNReal _ hu.le] using hout
    rw [discrepancy_stepPaths_eq_zero_of_not_mem_windows N s v l u.toNNReal hout']
    exact bot_le
  have h := integratedDiscrepancy_le_of_cut_windows (stepPath s v)
    (stepPath (fun i => l (s i)) v) l T F B 0 hmove' hsmall
  simpa only [ENNReal.ofReal_zero, zero_add, F] using h

end LatticeProb.Cadlag.HalfLine
