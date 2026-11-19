import LongRange.HeatKernel.CriticalPowerEnergy
import Mathlib.Algebra.Order.Chebyshev

/-!
# Averaging over finite sets

Jensen's inequality bounds the squared deviation from a finite average.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The squared deviation from a finite average is bounded by the average squared deviation. -/
theorem sq_sub_finset_average_le {X : Type*} (s : Finset X) (hs : s.Nonempty)
    (f : X → ℝ) (a : ℝ) :
    (a - (∑ y ∈ s, f y) / s.card) ^ 2 ≤
      (∑ y ∈ s, (a - f y) ^ 2) / s.card := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hj := sum_div_card_sq_le_sum_sq_div_card (s := s) (f := fun y => a - f y)
  have he : (∑ y ∈ s, (a - f y)) / (s.card : ℝ) =
      a - (∑ y ∈ s, f y) / s.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [he] at hj
  exact hj

/-- The average of a function over translates by a finite set. -/
noncomputable def finsetTranslateAverage {G : Type*} [Add G] (s : Finset G)
    (f : G → ℝ) (x : G) : ℝ := (∑ z ∈ s, f (x + z)) / s.card

/-- A finite translate average satisfies the pointwise Jensen bound. -/
theorem sq_sub_finsetTranslateAverage_le {G : Type*} [Add G] (s : Finset G)
    (hs : s.Nonempty) (f : G → ℝ) (x : G) :
    (f x - finsetTranslateAverage s f x) ^ 2 ≤
      (∑ z ∈ s, (f x - f (x + z)) ^ 2) / s.card :=
  sq_sub_finset_average_le s hs (fun z => f (x + z)) (f x)

/-- Squared deviations under translation are summable for square-summable functions. -/
theorem summable_sq_sub_translate {G : Type*} [AddCommGroup G] (f : G → ℝ)
    (hf : Summable (fun x => f x ^ 2)) (z : G) :
    Summable (fun x => (f x - f (x + z)) ^ 2) := by
  have ht : Summable (fun x => f (x + z) ^ 2) :=
    ((Equiv.addRight z).summable_iff (f := fun x => f x ^ 2)).mpr hf
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((hf.add ht).mul_left 2)
  intro x
  nlinarith [sq_nonneg (f x + f (x + z))]

/-- Jensen's inequality, summed over all sites, for finite translate averages. -/
theorem finsetTranslateAverage_sq_tsum_le {G : Type*} [AddCommGroup G]
    (s : Finset G) (hs : s.Nonempty) (f : G → ℝ)
    (hf : Summable (fun x => f x ^ 2)) :
    Summable (fun x => (f x - finsetTranslateAverage s f x) ^ 2) ∧
      (∑' x, (f x - finsetTranslateAverage s f x) ^ 2) ≤
        (∑ z ∈ s, ∑' x, (f x - f (x + z)) ^ 2) / s.card := by
  have hz (z : G) : Summable (fun x => (f x - f (x + z)) ^ 2) :=
    summable_sq_sub_translate f hf z
  have hsum : Summable (fun x => (∑ z ∈ s, (f x - f (x + z)) ^ 2) / s.card) :=
    (summable_sum (fun z _ => hz z)).div_const _
  have havg : Summable (fun x => (f x - finsetTranslateAverage s f x) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (sq_sub_finsetTranslateAverage_le s hs f) hsum
  refine ⟨havg, (havg.tsum_le_tsum (sq_sub_finsetTranslateAverage_le s hs f) hsum).trans_eq ?_⟩
  rw [tsum_div_const, Summable.tsum_finsetSum (fun z _ => hz z)]

/-- A uniform lower bound on a kernel converts the finite average into its energy. -/
theorem finsetTranslateAverage_sq_tsum_le_energy {G : Type*} [AddCommGroup G]
    (s : Finset G) (hs : s.Nonempty) (k : G → G → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x z, z ∈ s → (s.card : ℝ)⁻¹ ≤ C * (k x (x + z)).toReal)
    (f : lp (fun _ : G => ℝ) 2) :
    (∑' x, (f x - finsetTranslateAverage s f x) ^ 2) ≤
      2 * C * realKernelEnergy k f := by
  classical
  have hf : Summable (fun x => f x ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hrow (x : G) : Summable (fun y => (k x y).toReal * (f x - f y) ^ 2) :=
    summable_real_kernel_energy_row k hk hsym f hf.tsum_ofReal_lt_top x
  have houter : Summable (fun x => C * ∑' y, (k x y).toReal * (f x - f y) ^ 2) :=
    (summable_real_kernel_energy k hk hsym f hf.tsum_ofReal_lt_top).mul_left C
  have hpoint (x : G) : (∑ z ∈ s, (f x - f (x + z)) ^ 2) / s.card ≤
      C * ∑' y, (k x y).toReal * (f x - f y) ^ 2 := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    calc
      _ ≤ ∑ z ∈ s, C * ((k x (x + z)).toReal * (f x - f (x + z)) ^ 2) := by
        apply Finset.sum_le_sum
        intro z hz
        have h := mul_le_mul_of_nonneg_right (hbound x z hz) (sq_nonneg (f x - f (x + z)))
        nlinarith
      _ = C * ∑ y ∈ s.image (fun z => x + z), (k x y).toReal * (f x - f y) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_image]
        intro a _ b _ hab
        exact add_left_cancel hab
      _ ≤ C * ∑' y, (k x y).toReal * (f x - f y) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact (hrow x).sum_le_tsum _ (fun y _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  have hsum : Summable (fun x => (∑ z ∈ s, (f x - f (x + z)) ^ 2) / s.card) :=
    (summable_sum (fun z _ => summable_sq_sub_translate f hf z)).div_const _
  have h := (hsum.tsum_le_tsum hpoint houter)
  have hj := (finsetTranslateAverage_sq_tsum_le s hs f hf).1.tsum_le_tsum
    (sq_sub_finsetTranslateAverage_le s hs f) hsum
  calc
    _ ≤ ∑' x, (∑ z ∈ s, (f x - f (x + z)) ^ 2) / s.card := hj
    _ ≤ ∑' x, C * ∑' y, (k x y).toReal * (f x - f y) ^ 2 := h
    _ = 2 * C * realKernelEnergy k f := by rw [tsum_mul_left, realKernelEnergy]; ring

/-- A lower bound for an even Markov power controls deviations from a finite average. -/
theorem finsetTranslateAverage_sq_tsum_le_power_loss {G : Type*} [AddCommGroup G]
    (s : Finset G) (hs : s.Nonempty) (k : G → G → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x z, z ∈ s → (s.card : ℝ)⁻¹ ≤
      C * (densityPower (fun _ => 1) k (2 * n) x (x + z)).toReal)
    (f : lp (fun _ : G => ℝ) 2) :
    (∑' x, (f x - finsetTranslateAverage s f x) ^ 2) ≤
      2 * C * (‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2) := by
  have hp : ∀ x, ∑' y, densityPower (fun _ => 1) k (2 * n) x y = 1 := by
    have h := densityPower_isMarkov (fun _ : G => 1) (by simp) k
      (by simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using hk) (2 * n)
    simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using h
  have hsp := densityPower_symmetric (fun _ : G => 1) (by simp) k hsym (2 * n)
  have h := finsetTranslateAverage_sq_tsum_le_energy s hs _ hp hsp C hC hbound f
  rwa [realKernelEnergy_densityPower_two_mul k hk hsym n f] at h

end LatticeProb.Graph.LongRangeKernel
