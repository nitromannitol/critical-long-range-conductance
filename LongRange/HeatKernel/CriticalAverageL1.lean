import LongRange.HeatKernel.CriticalBallAverage

/-!
# Bounds for finite translate averages

An average over a finite set has supremum and summability bounds in terms of
the original absolutely summable function.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The absolute value of a translate average is controlled by the average of absolute values. -/
theorem abs_finsetTranslateAverage_le {G : Type*} [Add G] (s : Finset G) (f : G → ℝ) (x : G) :
    |finsetTranslateAverage s f x| ≤ (∑ z ∈ s, |f (x + z)|) / s.card := by
  unfold finsetTranslateAverage
  simp only [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ s.card from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- Every translate average of an absolutely summable function has a uniform bound. -/
theorem abs_finsetTranslateAverage_le_tsum {G : Type*} [AddCommGroup G]
    (s : Finset G) (f : G → ℝ) (hf : Summable (fun x => |f x|)) (x : G) :
    |finsetTranslateAverage s f x| ≤ (∑' x, |f x|) / s.card := by
  classical
  apply (abs_finsetTranslateAverage_le s f x).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h : (∑ z ∈ s, |f (x + z)|) = ∑ y ∈ s.image (fun z => x + z), |f y| := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact add_left_cancel hab
  rw [h]
  exact hf.sum_le_tsum _ (fun _ _ => abs_nonneg _)

/-- A finite average of translates preserves an absolute-sum bound. -/
theorem finsetTranslateAverage_summable_abs {G : Type*} [AddCommGroup G]
    (s : Finset G) (hs : s.Nonempty) (f : G → ℝ) (hf : Summable (fun x => |f x|)) :
    Summable (fun x => |finsetTranslateAverage s f x|) ∧
      (∑' x, |finsetTranslateAverage s f x|) ≤ ∑' x, |f x| := by
  have htrans (z : G) : Summable (fun x => |f (x + z)|) :=
    ((Equiv.addRight z).summable_iff (f := fun x => |f x|)).mpr hf
  have hsum : Summable (fun x => (∑ z ∈ s, |f (x + z)|) / s.card) :=
    (summable_sum (fun z _ => htrans z)).div_const _
  have havg : Summable (fun x => |finsetTranslateAverage s f x|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_finsetTranslateAverage_le s f) hsum
  refine ⟨havg, (havg.tsum_le_tsum (abs_finsetTranslateAverage_le s f) hsum).trans_eq ?_⟩
  rw [tsum_div_const, Summable.tsum_finsetSum (fun z _ => htrans z)]
  have heq (z : G) : (∑' x, |f (x + z)|) = ∑' x, |f x| :=
    by simpa only [Equiv.coe_addRight] using
      ((Equiv.addRight z).tsum_eq (fun x : G => |f x|))
  simp_rw [heq]
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn

/-- The square sum of an average is bounded by the square of the absolute sum
    divided by the cardinality of the averaging set. -/
theorem finsetTranslateAverage_sq_tsum_le_abs_tsum {G : Type*} [AddCommGroup G]
    (s : Finset G) (hs : s.Nonempty) (f : G → ℝ) (hf : Summable (fun x => |f x|)) :
    Summable (fun x => (finsetTranslateAverage s f x) ^ 2) ∧
      (∑' x, (finsetTranslateAverage s f x) ^ 2) ≤ (∑' x, |f x|) ^ 2 / s.card := by
  let M : ℝ := (∑' x, |f x|) / s.card
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have habs := finsetTranslateAverage_summable_abs s hs f hf
  have hupper : ∀ x, (finsetTranslateAverage s f x) ^ 2 ≤
      M * |finsetTranslateAverage s f x| := by
    intro x
    have h := abs_finsetTranslateAverage_le_tsum s f hf x
    change |finsetTranslateAverage s f x| ≤ M at h
    have h' := mul_le_mul_of_nonneg_right h (abs_nonneg (finsetTranslateAverage s f x))
    have heq : (finsetTranslateAverage s f x) ^ 2 =
        |finsetTranslateAverage s f x| * |finsetTranslateAverage s f x| := by
      rw [← pow_two, sq_abs]
    rw [heq]
    exact h'
  have hmajor : Summable (fun x => M * |finsetTranslateAverage s f x|) := habs.1.mul_left M
  have hsq : Summable (fun x => (finsetTranslateAverage s f x) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hupper hmajor
  refine ⟨hsq, ?_⟩
  calc
    _ ≤ ∑' x, M * |finsetTranslateAverage s f x| := hsq.tsum_le_tsum hupper hmajor
    _ = M * ∑' x, |finsetTranslateAverage s f x| := tsum_mul_left
    _ ≤ M * ∑' x, |f x| := mul_le_mul_of_nonneg_left habs.2 hM
    _ = (∑' x, |f x|) ^ 2 / s.card := by dsimp [M]; ring

end LatticeProb.Graph.LongRangeKernel
