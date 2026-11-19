import LongRangeHeat.KallenbergChangeLimit

/-!
# Tail compositions of time changes

Relative prefixes have distortion bounded by the sum of the intervening
distortions.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal Topology

noncomputable section

/-- The relative time change from one prefix to another. -/
def relativeChange (l : ℕ → Lambda) (n m : ℕ) : Lambda :=
  (changePrefix l m).trans (changePrefix l n).symm

/-- The distortion of a relative prefix is bounded by its tail sum. -/
theorem gamma_relativeChange_le (l : ℕ → Lambda) {n m : ℕ} (hnm : n ≤ m) :
    gamma (relativeChange l n m).1 ≤ ∑ k ∈ Finset.Ico n m, gamma (l k).1 := by
  induction m, hnm using Nat.le_induction with
  | base =>
      have he : (relativeChange l n n).1 = OrderIso.refl Time := by
        ext t
        simp only [relativeChange, Lambda.trans, Lambda.symm, OrderIso.trans_apply,
          OrderIso.symm_apply_apply, OrderIso.refl_apply]
      simp only [he, gamma_identity, Finset.Ico_self, Finset.sum_empty, le_refl]
  | succ m hnm ih =>
      have he : (relativeChange l n (m + 1)).1 =
          ((l m).trans (relativeChange l n m)).1 := by
        ext t
        rfl
      rw [he, Finset.sum_Ico_succ_top hnm]
      exact (Lambda.gamma_trans_le _ _).trans (by simpa only [add_comm] using add_le_add_left ih _)

/-- The relative limit has distortion bounded by the remaining distortion sum. -/
theorem gamma_relativeLimit_le (l : ℕ → Lambda) (L : Lambda)
    (hg : (∑' k, gamma (l k).1) ≠ ∞)
    (hL : ∀ T : Time, TendstoUniformlyOn (fun n => (changePrefix l n).1) L.1
      atTop (Iic T)) (n : ℕ) :
    gamma (L.trans (changePrefix l n).symm).1 ≤ ∑' k, gamma (l (n + k)).1 := by
  let S : ℝ≥0∞ := ∑' k, gamma (l (n + k)).1
  have hS : S ≠ ∞ := by
    apply ne_of_lt
    simpa only [S, Nat.add_comm] using
      (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective n)
        (fun k => gamma (l k).1)).trans_lt (lt_top_iff_ne_top.mpr hg)
  let C : ℝ := S.toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hbound (m : ℕ) : gamma (relativeChange l n (n + m)).1 ≤ ENNReal.ofReal C := by
    rw [show ENNReal.ofReal C = S from ENNReal.ofReal_toReal hS]
    refine (gamma_relativeChange_le l (Nat.le_add_right n m)).trans ?_
    rw [Finset.sum_Ico_eq_sum_range]
    exact ENNReal.sum_le_tsum _
  have hlim (t : Time) : Tendsto (fun m => (relativeChange l n (n + m)).1 t)
      atTop (𝓝 ((L.trans (changePrefix l n).symm).1 t)) := by
    have hp := ((hL t).tendsto_at (mem_Iic.mpr le_rfl)).comp (tendsto_add_atTop_nat n)
    have hp' : Tendsto (fun m => (changePrefix l (n + m)).1 t) atTop (𝓝 (L.1 t)) := by
      simpa only [Function.comp_def, Nat.add_comm] using hp
    exact ((changePrefix l n).1.symm.continuous.tendsto (L.1 t)).comp hp'
  have hresult := gamma_le_of_secant (L.trans (changePrefix l n).symm).1 hC
    (fun _ _ hts => secant_bounds_of_tendsto
      (fun m => relativeChange l n (n + m))
      (fun t => (L.trans (changePrefix l n).symm).1 t) hC hbound hlim hts)
  simpa only [show ENNReal.ofReal C = S from ENNReal.ofReal_toReal hS] using hresult

/-- The distortions of the relative limits vanish along the sequence. -/
theorem tendsto_gamma_relativeLimit (l : ℕ → Lambda) (L : Lambda)
    (hg : (∑' k, gamma (l k).1) ≠ ∞)
    (hL : ∀ T : Time, TendstoUniformlyOn (fun n => (changePrefix l n).1) L.1
      atTop (Iic T)) :
    Tendsto (fun n => gamma (L.trans (changePrefix l n).symm).1) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => bot_le) (gamma_relativeLimit_le l L hg hL)
  change Tendsto (fun n => ∑' k, gamma (l (n + k)).1) atTop (𝓝 (0 : ℝ≥0∞))
  simpa only [Nat.add_comm] using ENNReal.tendsto_sum_nat_add (fun k => gamma (l k).1) hg

end

end LatticeProb.Cadlag.HalfLine
