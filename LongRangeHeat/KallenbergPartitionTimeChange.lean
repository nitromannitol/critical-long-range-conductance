import LongRangeHeat.KallenbergPartitionCompact
import LongRangeHeat.KallenbergTimeChange

/-!
# Time changes for oscillation partitions

The nonterminal cuts of partitions with a uniform width bound can be
aligned with their limits by small half-line time changes.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter
open scoped Topology ENNReal NNReal

/-- Nonterminal partition cuts with positive limiting widths admit small
time changes aligning them with their convergent approximating cuts. -/
theorem eventually_exists_timeChange_for_partition_cuts (k : ℕ) (hk : 0 < k)
    (cut : ℕ → ℕ → Time) (limit : Fin (k + 1) → Time) {δ g : ℝ} (B : ℝ≥0)
    (hδ : 0 < δ) (hg : 0 < g) (hB : 0 < (B : ℝ))
    (hzero : limit 0 = 0) (hcutzero : ∀ n, cut n 0 = 0)
    (hwidth : ∀ i : Fin k, i.val + 1 < k →
      δ ≤ (limit i.succ : ℝ) - (limit i.castSucc : ℝ))
    (hlim : ∀ i, Tendsto (fun n => cut n i.val) atTop (𝓝 (limit i))) :
    ∀ᶠ n in atTop, ∃ l : Lambda, gamma l.1 ≤ ENNReal.ofReal g ∧
      (∀ t, dist t (l.1 t) ≤ B) ∧
      ∀ i : Fin k, l.1 (limit i.castSucc) = cut n i.val := by
  cases k with
  | zero => omega
  | succ N =>
    let s : Fin (N + 1) → Time := fun i => limit i.castSucc
    let v : ℕ → Fin (N + 1) → Time := fun n i => cut n i.val
    have hs : StrictMono s := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hw := hwidth i.castSucc (by simp only [Fin.val_castSucc]; omega)
      change limit i.castSucc.castSucc < limit i.succ.castSucc
      have heq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      rw [← heq]
      exact_mod_cast (show (limit i.castSucc.castSucc : ℝ) < limit i.castSucc.succ by
        linarith)
    have hs0 : s 0 = 0 := by simpa only [s, Fin.castSucc_zero] using hzero
    have hv0 (n : ℕ) : v n 0 = 0 := by simpa only [v, Fin.val_zero] using hcutzero n
    have hvlim (i : Fin (N + 1)) : Tendsto (fun n => v n i) atTop (𝓝 (s i)) :=
      hlim i.castSucc
    exact eventually_exists_small_timeChange_interpolating_knots N s v B hg hB
      hs.injective hs0 hv0 hvlim


/-- Aligned interval endpoints transfer a half-open oscillation bound through
the time change. -/
theorem dist_timeChange_le_of_interval_oscillation {E : Type*} [MetricSpace E]
    (x : D E) (l : Lambda) (a b c d t : Time) {η : ℝ}
    (ha : l.1 a = c) (hb : l.1 b = d) (ht : a ≤ t) (htb : t < b)
    (hcd : c < d)
    (hosc : ∀ s u : Time, c ≤ s → s < d → c ≤ u → u < d →
      dist (x.1 s) (x.1 u) ≤ η) :
    dist (x.1 (l.1 t)) (x.1 c) ≤ η := by
  have hleft : c ≤ l.1 t := by simpa only [ha] using l.1.monotone ht
  have hright : l.1 t < d := by simpa only [hb] using l.1.strictMono htb
  exact hosc (l.1 t) c hleft hright le_rfl hcd

end LatticeProb.Cadlag.HalfLine
