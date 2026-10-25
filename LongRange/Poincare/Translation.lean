import LongRange.Poincare.Averaging

/-!
# Physical-diameter exit for a fixed lattice translation

A positive coordinate displacement repeated more than the physical diameter leaves the
support. The number of steps is at most three times the diameter divided by the displacement
scale. This bound uses physical coordinates throughout.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A supported square sum is controlled by each forward displacement at a fixed scale. -/
theorem sq_sum_le_of_forward_shift_bound {ε a R : ℝ} (hε : 0 < ε) (ha : 0 < a)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hdiam : euclideanDiam U ≤ R)
    (hscale : a ≤ R) {h : Site d → ℝ} (hh : SupportedIn ε U h)
    (i : Fin d) (z : Site d) (hz : a ≤ ε * (z i : ℝ)) :
    ∑' x, h x ^ 2 ≤ 9 * (R / a) ^ 2 *
      ∑' x, (h (x + z) - h x) ^ 2 := by
  let N := ⌈R / a⌉₊ + 1
  have hR : 0 < R := ha.trans_le hscale
  have hexit (x : Site d) (hx : h x ≠ 0) : h (x + N • z) = 0 := by
    apply hh
    intro hy
    have hxu : physical ε x ∈ U := by
      by_contra hout
      exact hx (hh x hout)
    have hb := (abs_coord_le_radius
      (physical ε (x + N • z) - physical ε x) i).trans
      ((radius_sub_le_euclideanDiam hU hy hxu).trans hdiam)
    have he : (physical ε (x + N • z) - physical ε x) i =
        (N : ℝ) * (ε * (z i : ℝ)) := by
      simp only [physical, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      ring
    rw [he] at hb
    have hn : R < (N : ℝ) * a := by
      have hn := Nat.le_ceil (R / a)
      have hs := (div_le_iff₀ ha).mp hn
      change R ≤ (⌈R / a⌉₊ : ℝ) * a at hs
      dsimp only [N]
      push_cast
      nlinarith only [hs, ha]
    have hm := mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    exact (not_lt_of_ge (le_trans (le_abs_self _) hb)) (hn.trans_le hm)
  have ht := sq_sum_le_translate_energy (hh.summable_sq hε hU) z N hexit
  have hN : (N : ℝ) ≤ 3 * (R / a) := by
    have hc := Nat.ceil_lt_add_one (div_nonneg hR.le ha.le)
    have hratio : 1 ≤ R / a := (le_div_iff₀ ha).mpr (by simpa using hscale)
    dsimp only [N]
    push_cast
    linarith
  calc
    _ ≤ (N : ℝ) ^ 2 * ∑' x, (h (x + z) - h x) ^ 2 := ht
    _ ≤ (3 * (R / a)) ^ 2 * ∑' x, (h (x + z) - h x) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) (tsum_nonneg (fun _ => sq_nonneg _))
    _ = _ := by ring

end

end LongRange.Poincare
