import LongRange.Support.Prob.Cadlag.HalfLine.TimeChange
import LongRangeHeat.KallenbergLocalCauchy

/-!
# Compositions of time changes

The logarithmic distortion of a finite composition is bounded by the sum
of the distortions of its factors.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Successive time changes composed in chronological order. -/
def changePrefix (l : ℕ → Lambda) : ℕ → Lambda
  | 0 => identityChange
  | n + 1 => (l n).trans (changePrefix l n)

/-- The distortion of a prefix is bounded by the sum of its factors. -/
theorem gamma_changePrefix_le (l : ℕ → Lambda) (n : ℕ) :
    gamma (changePrefix l n).1 ≤ ∑ k ∈ Finset.range n, gamma (l k).1 := by
  induction n with
  | zero => simp only [changePrefix, identityChange, gamma_identity, Finset.range_zero,
      Finset.sum_empty, le_refl]
  | succ n ih =>
      rw [changePrefix, Finset.sum_range_succ]
      exact (Lambda.gamma_trans_le _ _).trans (by simpa only [add_comm] using add_le_add_left ih _)

/-- Uniform distortion bounds control the displacement of consecutive prefixes. -/
theorem dist_changePrefix_succ_le (l : ℕ → Lambda) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ∑ k ∈ Finset.range n, gamma (l k).1 ≤ ENNReal.ofReal C)
    (n : ℕ) (t : Time) :
    dist ((changePrefix l (n + 1)).1 t) ((changePrefix l n).1 t) ≤
      Real.exp C * ((t : ℝ) * (Real.exp (gamma (l n).1).toReal - 1)) := by
  have hp : (gamma (changePrefix l n).1).toReal ≤ C := by
    have hb := (gamma_changePrefix_le l n).trans (hbound n)
    simpa only [ENNReal.toReal_ofReal hC] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hl := (lipschitzWith_of_gamma (changePrefix l n).1
    (ne_of_lt (changePrefix l n).2.2)).dist_le_mul ((l n).1 t) t
  have hd := abs_sub_le_of_gamma (l n).1 (ne_of_lt (l n).2.2) t
  change dist ((changePrefix l n).1 ((l n).1 t)) ((changePrefix l n).1 t) ≤ _
  calc
    _ ≤ Real.exp (gamma (changePrefix l n).1).toReal * dist ((l n).1 t) t := hl
    _ ≤ Real.exp C * dist ((l n).1 t) t :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) dist_nonneg
    _ ≤ Real.exp C * ((t : ℝ) * (Real.exp (gamma (l n).1).toReal - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos C).le
      simpa only [NNReal.dist_eq] using hd

/-- Summable distortions in displacement form make the finite compositions
converge uniformly on every bounded interval. -/
theorem exists_tendstoUniformlyOn_changePrefix (l : ℕ → Lambda) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ∑ k ∈ Finset.range n, gamma (l k).1 ≤ ENNReal.ofReal C)
    (hs : Summable fun n => Real.exp (gamma (l n).1).toReal - 1) :
    ∃ L : Time → Time, ∀ T : Time,
      TendstoUniformlyOn (fun n => (changePrefix l n).1) L atTop (Iic T) := by
  apply exists_tendstoUniformlyOn_of_uniformCauchySeqOn
  intro T
  apply uniformCauchySeqOn_of_summable_dist
    (hs.mul_left (Real.exp C * (T : ℝ)))
  intro n t ht
  have hnonneg : 0 ≤ Real.exp (gamma (l n).1).toReal - 1 := by
    have hg : 0 ≤ (gamma (l n).1).toReal := ENNReal.toReal_nonneg
    linarith [Real.add_one_le_exp (gamma (l n).1).toReal]
  calc
    dist ((changePrefix l n).1 t) ((changePrefix l (n + 1)).1 t) =
        dist ((changePrefix l (n + 1)).1 t) ((changePrefix l n).1 t) := dist_comm _ _
    _ ≤ Real.exp C * ((t : ℝ) * (Real.exp (gamma (l n).1).toReal - 1)) :=
      dist_changePrefix_succ_le l hC hbound n t
    _ ≤ (Real.exp C * (T : ℝ)) * (Real.exp (gamma (l n).1).toReal - 1) := by
      have ht' : (t : ℝ) ≤ T := ht
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht' hnonneg)
          (Real.exp_pos C).le

end

end LatticeProb.Cadlag.HalfLine
