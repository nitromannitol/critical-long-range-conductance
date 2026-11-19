import LongRangeHeat.KallenbergOriginalPaths

/-!
# Completeness of half-line path space

The half-line Skorokhod metric is complete whenever the state space is
complete.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Every Cauchy sequence of half-line paths has a limit when the state space
is complete. -/
theorem cauchySeq_tendsto_of_complete_state {E : Type*} [MetricSpace E]
    [CompleteSpace E] (x : ℕ → D E) (hx : CauchySeq x) :
    ∃ y : D E, Tendsto x atTop (𝓝 y) := by
  let b : ℕ → ℝ := fun n => (1 / (2 : ℝ)) ^ n
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  obtain ⟨f, hf, hclose⟩ := Metric.exists_subseq_bounded_of_cauchySeq x hx b hb
  have hselect (n : ℕ) : ∃ k : Lambda,
      max (gamma k.1) (integratedDiscrepancy (x (f n)) (x (f (n + 1))) k.1) <
        ENNReal.ofReal (b n) := by
    apply iInf_lt_iff.mp
    have hd : dist (x (f n)) (x (f (n + 1))) < b n := by
      rw [dist_comm]
      exact hclose n _ (hf.monotone (Nat.le_add_right n 1))
    have he : skorohodDistanceExtended (x (f n)) (x (f (n + 1))) =
        ENNReal.ofReal (dist (x (f n)) (x (f (n + 1)))) := by
      rw [dist_eq_skorohodDistance, skorohodDistance, ENNReal.ofReal_toReal]
      exact ne_of_lt ((skorohodDistanceExtended_le_one _ _).trans_lt ENNReal.one_lt_top)
    change skorohodDistanceExtended (x (f n)) (x (f (n + 1))) < _
    rw [he]
    exact (ENNReal.ofReal_lt_ofReal_iff (hb n)).mpr hd
  choose k hk using hselect
  let l : ℕ → Lambda := fun n => (k n).symm
  have hgamma (n : ℕ) : gamma (l n).1 ≤ ENNReal.ofReal (b n) := by
    simpa only [l, Lambda.gamma_symm] using ((le_max_left _ _).trans (hk n).le)
  have hdisc (n : ℕ) :
      integratedDiscrepancy (x (f n)) (x (f (n + 1))) (l n).1.symm ≤
        ENNReal.ofReal (b n) := by
    simpa only [l, Lambda.symm, OrderIso.symm_symm] using
      ((le_max_right _ _).trans (hk n).le)
  have hbsum : Summable b := by simpa only [b] using summable_geometric_two
  have hg : (∑' n, gamma (l n).1) ≠ ∞ := by
    exact ne_of_lt ((ENNReal.tsum_le_tsum hgamma).trans_lt hbsum.tsum_ofReal_lt_top)
  have hd : Summable fun n =>
      (integratedDiscrepancy (x (f n)) (x (f (n + 1))) (l n).1.symm).toReal := by
    apply hbsum.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg)
    intro n
    simpa only [ENNReal.toReal_ofReal (hb n).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdisc n)
  obtain ⟨y, hy⟩ := exists_tendsto_of_summable_timeChanges (fun n => x (f n)) l hg hd
  exact ⟨y, tendsto_nhds_of_cauchySeq_of_subseq hx hf.tendsto_atTop hy⟩

/-- Completeness transfers from the state space to half-line path space. -/
theorem completeSpace_of_complete_state {E : Type*} [MetricSpace E] [CompleteSpace E] :
    CompleteSpace (D E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro x hx
  exact cauchySeq_tendsto_of_complete_state x hx

end

end LatticeProb.Cadlag.HalfLine
