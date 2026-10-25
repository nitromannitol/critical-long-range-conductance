import LongRange.Poincare.Support
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Translation telescoping and weighted displacement bounds

Telescoping along a fixed displacement controls a supported square sum by its displacement
energy. Summing this inequality against nonnegative weights gives the weighted core of the
single-scale argument without introducing an iterated operator.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- A square-summable function has square-summable differences under every translation. -/
theorem summable_sq_sub_translate {h : G → ℝ}
    (hh : Summable (fun x => h x ^ 2)) (z : G) :
    Summable (fun x => (h (x + z) - h x) ^ 2) := by
  have ht : Summable (fun x : G => h (x + z) ^ 2) :=
    ((Equiv.addRight z).summable_iff (f := fun x : G => h x ^ 2)).mpr hh
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ ((ht.add hh).mul_left 2)
  intro x
  nlinarith [sq_nonneg (h (x + z) + h x)]

/-- Pointwise Cauchy–Schwarz applied to the finite translation telescope. -/
theorem sq_le_translate_steps (h : G → ℝ) (z : G) (N : ℕ)
    (hexit : ∀ x, h x ≠ 0 → h (x + N • z) = 0) (x : G) : h x ^ 2 ≤ (N : ℝ) *
      ∑ n ∈ Finset.range N, (h (x + n • z + z) - h (x + n • z)) ^ 2 := by
  by_cases hx : h x = 0
  · rw [hx, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  · have ht : (∑ n ∈ Finset.range N,
        (h (x + n • z + z) - h (x + n • z))) = -h x := by
      simp_rw [show ∀ n : ℕ, x + n • z + z = x + (n + 1) • z by
        intro n; rw [add_nsmul, one_nsmul, add_assoc]]
      rw [Finset.sum_range_sub (fun n : ℕ => h (x + n • z)) N, hexit x hx,
        zero_nsmul, add_zero, zero_sub]
    have hc := sq_sum_le_card_mul_sum_sq
      (s := Finset.range N) (f := fun n => h (x + n • z + z) - h (x + n • z))
    simpa only [ht, neg_sq, Finset.card_range] using hc

/-- Telescoping to a translate disjoint from the support gives the squared step bound. -/
theorem sq_sum_le_translate_energy {h : G → ℝ}
    (hh : Summable (fun x => h x ^ 2)) (z : G) (N : ℕ)
    (hexit : ∀ x, h x ≠ 0 → h (x + N • z) = 0) :
    ∑' x, h x ^ 2 ≤ (N : ℝ) ^ 2 * ∑' x, (h (x + z) - h x) ^ 2 := by
  have hd := summable_sq_sub_translate hh z
  have hs (n : ℕ) : Summable (fun x : G =>
      (h (x + n • z + z) - h (x + n • z)) ^ 2) :=
    ((Equiv.addRight (n • z)).summable_iff
      (f := fun x : G => (h (x + z) - h x) ^ 2)).mpr hd
  calc
    _ ≤ ∑' x, (N : ℝ) * ∑ n ∈ Finset.range N,
        (h (x + n • z + z) - h (x + n • z)) ^ 2 :=
      hh.tsum_le_tsum (sq_le_translate_steps h z N hexit)
        ((summable_sum (fun n _ => hs n)).mul_left _)
    _ = (N : ℝ) * ∑ n ∈ Finset.range N, ∑' x : G,
        (h (x + n • z + z) - h (x + n • z)) ^ 2 := by
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun n _ => hs n)]
    _ = (N : ℝ) ^ 2 * ∑' x, (h (x + z) - h x) ^ 2 := by
      have he (n : ℕ) : (∑' x : G,
          (h (x + n • z + z) - h (x + n • z)) ^ 2) =
          ∑' x : G, (h (x + z) - h x) ^ 2 :=
        (Equiv.addRight (n • z)).tsum_eq (fun x : G => (h (x + z) - h x) ^ 2)
      simp_rw [he]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Nonnegative weighted summation preserves a common displacement-energy bound. -/
theorem weighted_sq_sum_le {h : G → ℝ} (S : Finset (G))
    (w : G → ℝ) (hw : ∀ z ∈ S, 0 ≤ w z) (B : ℝ)
    (hB : ∀ z ∈ S, (∑' x, h x ^ 2) ≤ B * ∑' x, (h (x + z) - h x) ^ 2) :
    (∑ z ∈ S, w z) * (∑' x, h x ^ 2) ≤
      B * ∑ z ∈ S, w z * ∑' x, (h (x + z) - h x) ^ 2 := by
  calc
    _ = ∑ z ∈ S, w z * (∑' x, h x ^ 2) := by rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ S, w z * (B * ∑' x, (h (x + z) - h x) ^ 2) :=
      Finset.sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hB z hz) (hw z hz))
    _ = _ := by rw [Finset.mul_sum]; congr 1; funext z; ring

end

end LongRange.Poincare
