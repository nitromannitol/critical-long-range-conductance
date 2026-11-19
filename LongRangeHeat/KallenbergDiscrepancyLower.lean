import LongRange.Support.Prob.Cadlag.HalfLine.Discrepancy

/-!
# Lower bounds for integrated discrepancy

A time-aligned pair of values controls the integrated discrepancy through the
exponential tail beyond both times.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

/-- A fixed aligned pair gives a lower bound for the integrated discrepancy. -/
theorem exponential_mul_q_le_integratedDiscrepancy {E : Type*} [MetricSpace E]
    (x y : D E) (l : LambdaPrime) (T t : Time) (ht : t ≤ T) (hlt : l t ≤ T) :
    ENNReal.ofReal (Real.exp (-(T : ℝ))) * q (x.1 t) (y.1 (l t)) ≤
      integratedDiscrepancy x y l := by
  have hq : q (x.1 t) (y.1 (l t)) ≠ ∞ :=
    ne_of_lt ((min_le_right _ _).trans_lt ENNReal.one_lt_top)
  have htail : (∫⁻ u : ℝ in Ioi (T : ℝ), ENNReal.ofReal (Real.exp (-u))) =
      ENNReal.ofReal (Real.exp (-(T : ℝ))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi _)
      (Eventually.of_forall fun u => (Real.exp_pos (-u)).le), integral_exp_neg_Ioi]
  calc
    _ = ∫⁻ u : ℝ in Ioi (T : ℝ),
        ENNReal.ofReal (Real.exp (-u)) * q (x.1 t) (y.1 (l t)) := by
      rw [lintegral_mul_const' _ _ hq, htail]
    _ ≤ ∫⁻ u : ℝ in Ioi (T : ℝ),
        ENNReal.ofReal (Real.exp (-u)) * discrepancy x y l u.toNNReal := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hTu : T ≤ u.toNNReal := by
        exact_mod_cast (show (T : ℝ) ≤ (u.toNNReal : ℝ) by
          rw [Real.coe_toNNReal _ (T.2.trans hu.le)]
          exact hu.le)
      apply mul_le_mul_right
      have h := le_iSup (fun s : Time => q (x.1 (min s u.toNNReal))
        (y.1 (min (l s) u.toNNReal))) t
      simpa only [discrepancy, min_eq_left (ht.trans hTu), min_eq_left (hlt.trans hTu)] using h
    _ ≤ integratedDiscrepancy x y l := by
      apply lintegral_mono_set
      exact Ioi_subset_Ioi T.2

/-- A sufficiently small integrated discrepancy controls the distance between
aligned values on a bounded time interval. -/
theorem dist_le_of_integratedDiscrepancy_lt {E : Type*} [MetricSpace E]
    (x y : D E) (l : LambdaPrime) (T t : Time) (ht : t ≤ T) (hlt : l t ≤ T)
    (hsmall : (integratedDiscrepancy x y l).toReal < Real.exp (-(T : ℝ))) :
    dist (x.1 t) (y.1 (l t)) ≤
      Real.exp (T : ℝ) * (integratedDiscrepancy x y l).toReal := by
  have hfin : integratedDiscrepancy x y l ≠ ∞ :=
    ne_of_lt ((integratedDiscrepancy_le_one x y l).trans_lt ENNReal.one_lt_top)
  have h := ENNReal.toReal_mono hfin
    (exponential_mul_q_le_integratedDiscrepancy x y l T t ht hlt)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    q, ENNReal.toReal_min (edist_ne_top _ _) ENNReal.one_ne_top, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_one] at h
  have hepos : 0 < Real.exp (-(T : ℝ)) := Real.exp_pos _
  have hdist : dist (x.1 t) (y.1 (l t)) < 1 := by
    by_contra hn
    have hone : min (dist (x.1 t) (y.1 (l t))) 1 = 1 :=
      min_eq_right (le_of_not_gt hn)
    rw [hone, mul_one] at h
    linarith
  rw [min_eq_left hdist.le] at h
  have hinv : Real.exp (T : ℝ) * Real.exp (-(T : ℝ)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (T : ℝ)).le
  rw [← mul_assoc, hinv, one_mul] at hm
  exact hm

end

end LatticeProb.Cadlag.HalfLine
