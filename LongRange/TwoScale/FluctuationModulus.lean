import LongRange.TwoScale.FluctuationCoeff
import LongRange.Appendix.Kappa
import LongRange.TwoScale.KernelSums
import LatticeProb.Analysis.TaylorHolder

/-!
# Scale comparison for the smooth fluctuation

The logarithmic normalization changes by a bounded amount between comparable scales.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The critical normalization has uniformly bounded logarithmic error on `(0,1)`. -/
lemma kappa_log_error_bound (hd : 1 ≤ d) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      |kappa d ε - (d * Euclidean.Shell.unitBallVolume d) * (|Real.log ε|)| ≤ E := by
  obtain ⟨E, hE, he⟩ := kappa_asymptotic hd
  obtain ⟨C, hC, hc⟩ := kappa_le d
  let D : ℝ := d * Euclidean.Shell.unitBallVolume d
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg d)
    (Euclidean.Shell.unitBallVolume_pos d).le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨E + C * (1 + Real.log 2) + D * Real.log 2, by positivity, ?_⟩
  intro ε hε
  by_cases hs : ε ≤ 1 / 2
  · have hh := he ε ⟨hε.1, hs⟩
    rw [← Euclidean.Shell.unitBallVolume_eq_pi_div_gamma] at hh
    have hp := mul_nonneg hC.le (show 0 ≤ 1 + Real.log 2 by positivity)
    have hq := mul_nonneg hD hlog2
    exact hh.trans (by
      change E ≤ E + C * (1 + Real.log 2) + D * Real.log 2
      linarith only [hp, hq])
  · have hl : (|Real.log ε|) ≤ Real.log 2 := by
      rw [abs_of_neg (Real.log_neg hε.1 hε.2)]
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
        (lt_of_not_ge hs).le
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0), Real.log_one] at hh
      linarith
    calc
      _ ≤ |kappa d ε| + |D * (|Real.log ε|)| := abs_sub _ _
      _ = kappa d ε + D * (|Real.log ε|) := by
        rw [abs_of_nonneg (kappa_pos hd hε).le,
          abs_of_nonneg (mul_nonneg hD (abs_nonneg _))]
      _ ≤ C * (1 + Real.log 2) + D * Real.log 2 :=
        add_le_add ((hc ε hε).trans
          (mul_le_mul_of_nonneg_left (by linarith) hC.le))
          (mul_le_mul_of_nonneg_left hl hD)
      _ ≤ _ := by linarith

/-- Comparable scales have critical normalizations differing by a bounded amount. -/
theorem kappa_sub_le_of_ratio (hd : 1 ≤ d) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ K, 0 ≤ K ∧ ∀ ε ε',
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 →
      ε ≤ Q * ε' → ε' ≤ Q * ε → |kappa d ε - kappa d ε'| ≤ K := by
  obtain ⟨E, hE, he⟩ := kappa_log_error_bound hd
  let D : ℝ := d * Euclidean.Shell.unitBallVolume d
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg d)
    (Euclidean.Shell.unitBallVolume_pos d).le
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  refine ⟨2 * E + D * Real.log Q, by positivity, ?_⟩
  intro ε ε' hε hε' hratio hratio'
  have hlog := Real.log_le_log hε.1 hratio
  have hlog' := Real.log_le_log hε'.1 hratio'
  rw [Real.log_mul hQ0.ne' hε'.1.ne'] at hlog
  rw [Real.log_mul hQ0.ne' hε.1.ne'] at hlog'
  have hl : |(|Real.log ε|) - (|Real.log ε'|)| ≤ Real.log Q := by
    rw [abs_of_neg (Real.log_neg hε.1 hε.2),
      abs_of_neg (Real.log_neg hε'.1 hε'.2)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmiddle : |D * (|Real.log ε|) - D * (|Real.log ε'|)| ≤ D * Real.log Q := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hl hD
  have hleft := he ε hε
  have hright := he ε' hε'
  change |kappa d ε - D * (|Real.log ε|)| ≤ E at hleft
  change |kappa d ε' - D * (|Real.log ε'|)| ≤ E at hright
  calc
    _ = |(kappa d ε - D * (|Real.log ε|)) +
        (D * (|Real.log ε|) - D * (|Real.log ε'|)) -
        (kappa d ε' - D * (|Real.log ε'|))| := by congr 1; ring
    _ ≤ |kappa d ε - D * (|Real.log ε|)| +
        |D * (|Real.log ε|) - D * (|Real.log ε'|)| +
        |kappa d ε' - D * (|Real.log ε'|)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- The absolute remainder sum is controlled by the critical normalization and a tail
constant, using quadratic growth inside the unit ball and linear growth outside. -/
theorem smoothRemainder_kernel_abs_sum_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (v : (Fin d → ℝ) → ℝ) (B : ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → ∀ q : Site d,
        Summable (fun w : Site d => if w = 0 then 0 else
          jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|) ∧
        ε ^ d * ∑' w : Site d, (if w = 0 then 0 else
          jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|) ≤
          B / 2 * kappa d ε + C * B := by
  classical
  obtain ⟨C, hC, hc⟩ := kernel_tail_sum_bound d
  refine ⟨2 * C, by positivity, ?_⟩
  intro ε hε v B hv hv0 hv1 hv2 q
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  let f := fun w : Site d => if w = 0 then (0 : ℝ) else
    jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|
  let g := fun w : Site d => if w ∈ unitBallIndices d ε then
    B / 2 * (jumpKernel (physical ε w) * radius (physical ε w) ^ 2) else 0
  let t := fun w : Site d => if 1 < radius (physical ε w) then
    jumpKernel (physical ε w) * (1 + radius (physical ε w)) else 0
  have hg : Summable g := by
    apply summable_of_hasFiniteSupport
    apply (unitBallIndices d ε).finite_toSet.subset
    intro w hw
    by_contra hn
    exact hw (if_neg hn)
  have ht : Summable t := (hc ε hε).1
  have hf0 : ∀ w, 0 ≤ f w := by
    intro w
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (jumpKernel_nonneg _) (abs_nonneg _)
  have hg0 (w : Site d) : 0 ≤ g w := by
    have hk := jumpKernel_nonneg (physical ε w)
    dsimp [g]
    split_ifs <;> positivity
  have ht0 (w : Site d) : 0 ≤ t w := by
    have hk := jumpKernel_nonneg (physical ε w)
    have hr := radius_nonneg (physical ε w)
    dsimp [t]
    split_ifs <;> positivity
  have hbound (w : Site d) : f w ≤ g w + 2 * B * t w := by
    by_cases hw : w = 0
    · subst w
      simp only [f, if_pos rfl]
      exact add_nonneg (hg0 0) (mul_nonneg (mul_nonneg (by norm_num) hB) (ht0 0))
    by_cases hr : radius (physical ε w) ≤ 1
    · have hm := (mem_unitBallIndices hε.1 w).mpr ⟨hw, hr⟩
      simp only [f, if_neg hw, g, if_pos hm, t, not_lt.mpr hr, if_false,
        mul_zero, add_zero]
      calc
        _ ≤ jumpKernel (physical ε w) *
            (B / 2 * radius (physical ε w) ^ 2) :=
          mul_le_mul_of_nonneg_left (smoothRemainder_abs_le_sq hv hv2 _ _)
            (jumpKernel_nonneg _)
        _ = _ := by ring
    · have hr' : 1 < radius (physical ε w) := lt_of_not_ge hr
      have hm : w ∉ unitBallIndices d ε := by
        intro hm
        exact hr ((mem_unitBallIndices hε.1 w).mp hm).2
      simp only [f, if_neg hw, g, if_neg hm, t, if_pos hr', zero_add]
      have hlin := TaylorHolder.remainder_le_linear hv0 hv1
        (physical ε q) (physical ε w)
      change |smoothRemainder v (physical ε q) (physical ε w)| ≤ _ at hlin
      calc
        _ ≤ jumpKernel (physical ε w) *
            (2 * B * (1 + radius (physical ε w))) := by
          apply mul_le_mul_of_nonneg_left _ (jumpKernel_nonneg _)
          exact hlin.trans (by nlinarith only [mul_nonneg hB (radius_nonneg
            (physical ε w))])
        _ = _ := by ring
  have hs := Summable.of_nonneg_of_le hf0 hbound (hg.add (ht.mul_left (2 * B)))
  refine ⟨hs, ?_⟩
  change ε ^ d * ∑' w, f w ≤ _
  have hgs : ε ^ d * ∑' w, g w = B / 2 * kappa d ε := by
    rw [tsum_eq_sum (s := unitBallIndices d ε) (fun w hw => if_neg hw)]
    simp only [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum]
    rw [kappa_eq_radial_sum hε.1]
    ring
  calc
    _ ≤ ε ^ d * ∑' w, (g w + 2 * B * t w) :=
      mul_le_mul_of_nonneg_left
        (hs.tsum_le_tsum hbound (hg.add (ht.mul_left (2 * B))))
        (pow_nonneg hε.1.le _)
    _ = B / 2 * kappa d ε + 2 * B * (ε ^ d * ∑' w, t w) := by
      rw [hg.tsum_add (ht.mul_left (2 * B)), tsum_mul_left, mul_add, hgs]
      ring
    _ ≤ B / 2 * kappa d ε + 2 * B * C :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hc ε hε).2
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB))
    _ = _ := by ring

/-- A lower triadic scale bound gives a normalization growing at most linearly in the
block index. The constant is fixed before the index and the scale. -/
theorem kappa_block_le (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → c / 3 ^ m ≤ ε → kappa d ε ≤ C * m := by
  obtain ⟨C, hC, hb⟩ := kappa_le d
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨C * (1 + (|Real.log c|) + Real.log 3), by positivity, ?_⟩
  intro m hm ε hε hscale
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) _
  have hs : c ≤ ε * 3 ^ m := (div_le_iff₀ hp).mp hscale
  have hl := Real.log_le_log hc hs
  rw [Real.log_mul hε.1.ne' hp.ne', Real.log_pow] at hl
  have hl' : (|Real.log ε|) ≤ m * Real.log 3 + (|Real.log c|) := by
    rw [abs_of_neg (Real.log_neg hε.1 hε.2)]
    linarith only [hl, neg_abs_le (Real.log c)]
  calc
    kappa d ε ≤ C * (1 + (|Real.log ε|)) := hb ε hε
    _ ≤ C * (1 + (m * Real.log 3 + (|Real.log c|))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hl') hC.le
    _ ≤ C * ((1 + (|Real.log c|) + Real.log 3) * m) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hh := mul_le_mul_of_nonneg_left hm' (show 0 ≤ 1 + (|Real.log c|) by positivity)
      linarith only [hh]
    _ = _ := by ring

/-- On a triadic block, the absolute unnormalized smooth remainder sum grows at most
linearly in the block index, uniformly over the function and observed site. -/
theorem smoothRemainder_kernel_abs_sum_block_bound (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → c / 3 ^ m ≤ ε →
      ∀ (v : (Fin d → ℝ) → ℝ) (B : ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → ∀ q : Site d,
        Summable (fun w : Site d => if w = 0 then 0 else
          jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|) ∧
        ε ^ d * ∑' w : Site d, (if w = 0 then 0 else
          jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|) ≤
          A * B * m := by
  obtain ⟨C, hC, hb⟩ := smoothRemainder_kernel_abs_sum_bound d
  obtain ⟨D, hD, hd⟩ := kappa_block_le d c hc
  refine ⟨D / 2 + C, by positivity, ?_⟩
  intro m hm ε hε hscale v B hv hv0 hv1 hv2 q
  obtain ⟨hs, hsum⟩ := hb ε hε v B hv hv0 hv1 hv2 q
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨hs, hsum.trans ?_⟩
  calc
    _ ≤ B / 2 * (D * m) + C * B :=
      add_le_add (mul_le_mul_of_nonneg_left (hd m hm ε hε hscale)
        (div_nonneg hB (by norm_num : (0 : ℝ) ≤ 2))) le_rfl
    _ ≤ B / 2 * (D * m) + C * B * m :=
      add_le_add le_rfl (le_mul_of_one_le_right (mul_nonneg hC.le hB) hm')
    _ = _ := by ring

/-- An upper triadic scale bound gives a normalization growing at least linearly in
 the block index, including blocks whose scales are close to one. -/
theorem le_kappa_block (hd : 1 ≤ d) (C₀ : ℝ) (_hC₀ : 0 < C₀) :
    ∃ b : ℝ, 0 < b ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε ≤ C₀ / 3 ^ m → b * m ≤ kappa d ε := by
  obtain ⟨b, hb, hlow⟩ := le_kappa hd
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 1 + |Real.log C₀| := by positivity
  refine ⟨b * Real.log 3 / (1 + |Real.log C₀|), by positivity, ?_⟩
  intro m _ ε hε hscale
  have hp : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) _
  have hs : ε * 3 ^ m ≤ C₀ := (le_div_iff₀ hp).mp hscale
  have hl := Real.log_le_log (mul_pos hε.1 hp) hs
  rw [Real.log_mul hε.1.ne' hp.ne', Real.log_pow] at hl
  have hlog : (m : ℝ) * Real.log 3 ≤ |Real.log ε| + |Real.log C₀| := by
    rw [abs_of_neg (Real.log_neg hε.1 hε.2)]
    linarith only [hl, le_abs_self (Real.log C₀)]
  have hprod := mul_nonneg (abs_nonneg (Real.log ε)) (abs_nonneg (Real.log C₀))
  calc
    _ = b * ((m : ℝ) * Real.log 3) / (1 + |Real.log C₀|) := by ring
    _ ≤ b * (1 + |Real.log ε|) := by
      rw [div_le_iff₀ hden]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hb.le
      nlinarith only [hlog, hprod]
    _ ≤ kappa d ε := hlow ε hε

/-- The reciprocal normalization changes by at most a constant divided by the square
of the block index on an admissible scale block. -/
theorem kappa_inv_sub_block_bound (hd : 1 ≤ d) (c C₀ : ℝ)
    (hc : 0 < c) (hcC : c ≤ C₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε ε' : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 →
      c / 3 ^ m ≤ ε → ε ≤ C₀ / 3 ^ m →
      c / 3 ^ m ≤ ε' → ε' ≤ C₀ / 3 ^ m →
      |(kappa d ε)⁻¹ - (kappa d ε')⁻¹| ≤ D / (m : ℝ) ^ 2 := by
  have hC₀ := hc.trans_le hcC
  obtain ⟨b, hb, hlow⟩ := le_kappa_block hd C₀ hC₀
  obtain ⟨L, hL, hdiff⟩ := kappa_sub_le_of_ratio hd (C₀ / c)
    ((one_le_div hc).mpr hcC)
  refine ⟨L / b ^ 2, by positivity, ?_⟩
  intro m hm ε ε' hε hε' hmin hmax hmin' hmax'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hratio : ε ≤ (C₀ / c) * ε' := by
    calc
      ε ≤ C₀ / 3 ^ m := hmax
      _ = (C₀ / c) * (c / 3 ^ m) := by field_simp
      _ ≤ (C₀ / c) * ε' := mul_le_mul_of_nonneg_left hmin' (div_nonneg hC₀.le hc.le)
  have hratio' : ε' ≤ (C₀ / c) * ε := by
    calc
      ε' ≤ C₀ / 3 ^ m := hmax'
      _ = (C₀ / c) * (c / 3 ^ m) := by field_simp
      _ ≤ (C₀ / c) * ε := mul_le_mul_of_nonneg_left hmin (div_nonneg hC₀.le hc.le)
  have hk := kappa_pos hd hε
  have hk' := kappa_pos hd hε'
  have hden : b ^ 2 * (m : ℝ) ^ 2 ≤ kappa d ε * kappa d ε' := by
    calc
      _ = (b * m) * (b * m) := by ring
      _ ≤ _ := mul_le_mul (hlow m hm ε hε hmax) (hlow m hm ε' hε' hmax')
        (mul_nonneg hb.le hm0.le) hk.le
  calc
    _ = |kappa d ε - kappa d ε'| / (kappa d ε * kappa d ε') := by
      rw [inv_sub_inv hk.ne' hk'.ne', abs_div,
        abs_of_pos (mul_pos hk hk'), abs_sub_comm]
    _ ≤ L / (b ^ 2 * (m : ℝ) ^ 2) :=
      div_le_div₀ hL (hdiff ε ε' hε hε' hratio hratio')
        (mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hm0)) hden
    _ = _ := by ring

/-- Bounded conductance deviations preserve absolute summability and the block bound
for the unnormalized smooth fluctuation numerator. -/
theorem smoothFluctuation_numerator_block_bound (d : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → c / 3 ^ m ≤ ε →
      ∀ (v : (Fin d → ℝ) → ℝ) (B L : ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → 0 ≤ L →
      ∀ (q : Site d) (a : Edge d → ℝ) (m₀ : ℝ), (∀ e, |a e - m₀| ≤ L) →
        Summable (fun w : Site d => if hw : w = 0 then 0 else
          (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε w) *
            smoothRemainder v (physical ε q) (physical ε w)) ∧
        |ε ^ d * ∑' w : Site d, (if hw : w = 0 then 0 else
          (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε w) *
            smoothRemainder v (physical ε q) (physical ε w))| ≤ A * B * L * m := by
  classical
  obtain ⟨A, hA, hbound⟩ := smoothRemainder_kernel_abs_sum_block_bound d c hc
  refine ⟨A, hA, ?_⟩
  intro m hm ε hε hscale v B L hv hv0 hv1 hv2 hL q a m₀ ha
  obtain ⟨hs, hb⟩ := hbound m hm ε hε hscale v B hv hv0 hv1 hv2 q
  let f := fun w : Site d => if hw : w = 0 then (0 : ℝ) else
    (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)
  let g := fun w : Site d => if w = 0 then (0 : ℝ) else
    jumpKernel (physical ε w) * |smoothRemainder v (physical ε q) (physical ε w)|
  have hfg (w : Site d) : ‖f w‖ ≤ L * g w := by
    dsimp [f, g]
    split_ifs with hw
    · simp only [abs_zero, mul_zero, le_refl]
    · rw [abs_mul, abs_mul,
        abs_of_nonneg (jumpKernel_nonneg _)]
      calc
        _ ≤ L * jumpKernel (physical ε w) *
            |smoothRemainder v (physical ε q) (physical ε w)| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (ha _) (jumpKernel_nonneg _)) (abs_nonneg _)
        _ = _ := by ring
  have hsum : Summable f := (hs.mul_left L).of_norm_bounded hfg
  refine ⟨hsum, ?_⟩
  change |ε ^ d * ∑' w, f w| ≤ _
  rw [abs_mul, abs_of_nonneg (pow_nonneg hε.1.le _)]
  calc
    _ ≤ ε ^ d * (L * ∑' w, g w) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε.1.le _)
      simpa only [Real.norm_eq_abs, tsum_mul_left] using
        (tsum_of_norm_bounded (hs.mul_left L).hasSum hfg)
    _ = L * (ε ^ d * ∑' w, g w) := by ring
    _ ≤ L * (A * B * m) := mul_le_mul_of_nonneg_left hb hL
    _ = _ := by ring

/-- On a scale block the normalization-change contribution to the smooth fluctuation
is bounded by a constant divided by the block index. -/
theorem smoothFluctuation_normalization_sub_bound (hd : 1 ≤ d) (c C₀ B L : ℝ)
    (hc : 0 < c) (hcC : c ≤ C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (v : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) → 0 ≤ L →
      ∀ m : ℕ, 1 ≤ m → ∀ ε ε' : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 →
      c / 3 ^ m ≤ ε → ε ≤ C₀ / 3 ^ m →
      c / 3 ^ m ≤ ε' → ε' ≤ C₀ / 3 ^ m →
      ∀ (q : Site d) (a : Edge d → ℝ) (m₀ : ℝ), (∀ e, |a e - m₀| ≤ L) →
        |((kappa d ε)⁻¹ - (kappa d ε')⁻¹) *
          (ε ^ d * ∑' w : Site d, (if hw : w = 0 then 0 else
            (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε w) *
              smoothRemainder v (physical ε q) (physical ε w)))| ≤ A / m := by
  obtain ⟨D, hD, hdiff⟩ := kappa_inv_sub_block_bound hd c C₀ hc hcC
  obtain ⟨E, hE, hsize⟩ := smoothFluctuation_numerator_block_bound d c hc
  refine ⟨D * E * |B| * |L| + 1, by positivity, ?_⟩
  intro v hv hv0 hv1 hv2 hL m hm ε ε' hε hε' hmin hmax hmin' hmax' q a m₀ ha
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hn := (hsize m hm ε hε hmin v B L hv hv0 hv1 hv2 hL q a m₀ ha).2
  rw [abs_mul]
  calc
    _ ≤ (D / (m : ℝ) ^ 2) * (E * B * L * m) :=
      mul_le_mul (hdiff m hm ε ε' hε hε' hmin hmax hmin' hmax') hn
        (abs_nonneg _) (by positivity)
    _ = D * E * |B| * |L| / m := by
      rw [abs_of_nonneg hB, abs_of_nonneg hL]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hm0.le

/-- Scaling both the base point and displacement extracts the square of the scale
from the integral Taylor remainder, without changing its Euclidean displacement. -/
lemma smoothRemainder_smul_eq_integral {v : (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ 2 v) (ε : ℝ) (x z : Fin d → ℝ) :
    smoothRemainder v (ε • x) (ε • z) = ε ^ 2 *
      ∫ t in (0 : ℝ)..1,
        (1 - t) * iteratedFDeriv ℝ 2 v (ε • (x + t • z)) ![z, z] := by
  rw [smoothRemainder, TaylorHolder.remainder_eq_integral hv,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [smul_add, smul_comm t ε z]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_smul, smul_apply, smul_eq_mul]
  ring

/-- Dividing the remainder by the squared nonzero scale leaves the Hessian integral
at the rescaled base points and the original displacement. -/
lemma smoothRemainder_div_sq_eq_integral {v : (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ 2 v) {ε : ℝ} (hε : ε ≠ 0) (x z : Fin d → ℝ) :
    smoothRemainder v (ε • x) (ε • z) / ε ^ 2 =
      ∫ t in (0 : ℝ)..1,
        (1 - t) * iteratedFDeriv ℝ 2 v (ε • (x + t • z)) ![z, z] := by
  rw [smoothRemainder_smul_eq_integral hv]
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hε)

/-- A Hölder continuous Hessian controls the change of the scale-normalized Taylor
remainder. All displacement and base-point bounds use the Euclidean radius. -/
theorem smoothRemainder_div_sq_sub_le {v : (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ 2 v) {σ B : ℝ} (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hHolder : ∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
      B * radius (x - y) ^ σ) {ε ε' : ℝ} (hε : ε ≠ 0) (hε' : ε' ≠ 0)
    (x z : Fin d → ℝ) :
    |smoothRemainder v (ε • x) (ε • z) / ε ^ 2 -
        smoothRemainder v (ε' • x) (ε' • z) / ε' ^ 2| ≤
      B / 2 * radius z ^ 2 * (|ε - ε'| * (radius x + radius z)) ^ σ := by
  let F := fun e t : ℝ =>
    (1 - t) * iteratedFDeriv ℝ 2 v (e • (x + t • z)) ![z, z]
  have hD : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hH : Continuous (fderiv ℝ (fderiv ℝ v)) := hD.continuous_fderiv (by norm_num)
  have hF (e : ℝ) : Continuous (F e) := by
    dsimp [F]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hz : Continuous (fun t : ℝ => x + t • z) := by fun_prop
    have hp : Continuous (fun t : ℝ => e • (x + t • z)) := hz.const_smul e
    exact (continuous_const.sub continuous_id).mul
      (((hH.comp hp).clm_apply continuous_const).clm_apply continuous_const)
  rw [smoothRemainder_div_sq_eq_integral hv hε,
    smoothRemainder_div_sq_eq_integral hv hε']
  change |(∫ t in (0 : ℝ)..1, F ε t) - ∫ t in (0 : ℝ)..1, F ε' t| ≤ _
  rw [← intervalIntegral.integral_sub ((hF ε).intervalIntegrable 0 1)
    ((hF ε').intervalIntegrable 0 1)]
  have hrad (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      radius (ε • (x + t • z) - ε' • (x + t • z)) ≤
        |ε - ε'| * (radius x + radius z) := by
    rw [← sub_smul, TaylorHolder.radius_smul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      radius (x + t • z) ≤ radius x + radius (t • z) := by
        simp only [radius_norm, WithLp.toLp_add]
        exact norm_add_le _ _
      _ ≤ radius x + radius z := by
        rw [TaylorHolder.radius_smul, abs_of_nonneg ht.1.le]
        exact add_le_add_right (mul_le_of_le_one_left (radius_nonneg z) ht.2) _
  have heval (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      |iteratedFDeriv ℝ 2 v (ε • (x + t • z)) ![z, z] -
        iteratedFDeriv ℝ 2 v (ε' • (x + t • z)) ![z, z]| ≤
        (B * (|ε - ε'| * (radius x + radius z)) ^ σ) * radius z ^ 2 := by
    let H := iteratedFDeriv ℝ 2 v (ε • (x + t • z)) -
      iteratedFDeriv ℝ 2 v (ε' • (x + t • z))
    have hnorm : ‖H‖ ≤ B * (|ε - ε'| * (radius x + radius z)) ^ σ :=
      (hHolder _ _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (radius_nonneg _) (hrad t ht) hσ) hB)
    calc
      _ ≤ ‖H‖ * (‖z‖ * ‖z‖) := by
        simpa only [H, sub_apply, Real.norm_eq_abs, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one] using H.le_opNorm ![z, z]
      _ ≤ _ := by
        rw [← pow_two]
        exact mul_le_mul hnorm
          (pow_le_pow_left₀ (norm_nonneg z) (TaylorHolder.norm_le_radius z) 2)
          (sq_nonneg _) (mul_nonneg hB (Real.rpow_nonneg (mul_nonneg (abs_nonneg _)
            (add_nonneg (radius_nonneg _) (radius_nonneg _))) _))
  have hb : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖F ε t - F ε' t‖ ≤
      (1 - t) * ((B * (|ε - ε'| * (radius x + radius z)) ^ σ) * radius z ^ 2) := by
    intro t ht
    dsimp [F]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact mul_le_mul_of_nonneg_left (heval t ht) (sub_nonneg.mpr ht.2)
  have hi : IntervalIntegrable (fun t : ℝ => (1 - t) *
      ((B * (|ε - ε'| * (radius x + radius z)) ^ σ) * radius z ^ 2))
      MeasureTheory.volume 0 1 :=
    ((continuous_const.sub continuous_id).mul (continuous_const :
    Continuous (fun _ : ℝ =>
      (B * (|ε - ε'| * (radius x + radius z)) ^ σ) * radius z ^ 2))).intervalIntegrable 0 1
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (MeasureTheory.ae_of_all _ hb) hi
  rw [Real.norm_eq_abs] at h
  apply h.trans_eq
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t : ℝ => t) (continuous_const.intervalIntegrable 0 1)
      (continuous_id.intervalIntegrable 0 1)]
  norm_num [integral_id]
  ring

/-- Physical sampling is scalar multiplication of the unit-scale lattice embedding. -/
lemma physical_eq_smul_one (ε : ℝ) (q : Site d) :
    physical ε q = ε • physical 1 q := by
  ext i
  simp only [physical, Pi.smul_apply, smul_eq_mul, one_mul]

/-- The critical kernel and volume factor leave precisely the inverse square scale. -/
lemma kernel_volume_mul_remainder {ε : ℝ} (hε : 0 < ε) {w : Site d} (hw : w ≠ 0)
    (v : (Fin d → ℝ) → ℝ) (q : Site d) :
    ε ^ d * (jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)) =
      jumpKernel (physical 1 w) *
        (smoothRemainder v (ε • physical 1 q) (ε • physical 1 w) / ε ^ 2) := by
  rw [jumpKernel_physical hε hw, jumpKernel_physical zero_lt_one hw,
    physical_eq_smul_one ε q, physical_eq_smul_one ε w]
  simp only [one_pow, mul_one, pow_add]
  field_simp

/-- The Hölder comparison of scaled Taylor remainders transfers to the physical
kernel with the exact critical normalization. -/
theorem kernel_remainder_sub_le {v : (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ 2 v) {σ B : ℝ} (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hHolder : ∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
      B * radius (x - y) ^ σ) {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (q : Site d) {w : Site d} (hw : w ≠ 0) :
    |ε ^ d * (jumpKernel (physical ε w) *
        smoothRemainder v (physical ε q) (physical ε w)) -
      ε' ^ d * (jumpKernel (physical ε' w) *
        smoothRemainder v (physical ε' q) (physical ε' w))| ≤
      jumpKernel (physical 1 w) * (B / 2 * radius (physical 1 w) ^ 2 *
        (|ε - ε'| * (radius (physical 1 q) + radius (physical 1 w))) ^ σ) := by
  rw [kernel_volume_mul_remainder hε hw, kernel_volume_mul_remainder hε' hw,
    ← mul_sub, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (smoothRemainder_div_sq_sub_le hv hσ hB hHolder hε.ne' hε'.ne' _ _)
    (jumpKernel_nonneg _)

/-- At scales above a reference scale, the normalized linear remainder is dominated
by the reference kernel with linear growth. This bound is used only on the tail. -/
theorem kernel_remainder_le_reference_linear {v : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hv0 : ∀ x, |v x| ≤ B) (hv1 : ∀ x, ‖fderiv ℝ v x‖ ≤ B)
    {ρ ε : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε) (q : Site d) {w : Site d} (hw : w ≠ 0) :
    ε ^ d * (jumpKernel (physical ε w) *
      |smoothRemainder v (physical ε q) (physical ε w)|) ≤
      2 * B * (ρ ^ d * (jumpKernel (physical ρ w) * (1 + radius (physical ρ w)))) := by
  have hε := hρ.trans_le hρε
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hr := radius_nonneg (physical 1 w)
  have hlin := TaylorHolder.remainder_le_linear hv0 hv1 (physical ε q) (physical ε w)
  change |smoothRemainder v (physical ε q) (physical ε w)| ≤ _ at hlin
  rw [radius_physical_eq_mul hε.le] at hlin
  have hdiv : (2 * B + B * (ε * radius (physical 1 w))) / ε ^ 2 ≤
      2 * B * ((1 + ρ * radius (physical 1 w)) / ρ ^ 2) := by
    calc
      _ = 2 * B / ε ^ 2 + B * radius (physical 1 w) / ε := by
        field_simp
      _ ≤ 2 * B / ρ ^ 2 + B * radius (physical 1 w) / ρ :=
        add_le_add
          (div_le_div₀ (by positivity) le_rfl (sq_pos_of_pos hρ)
            (pow_le_pow_left₀ hρ.le hρε 2))
          (div_le_div₀ (mul_nonneg hB hr) le_rfl hρ hρε)
      _ ≤ 2 * B / ρ ^ 2 + 2 * (B * radius (physical 1 w) / ρ) := by
        have hh : 0 ≤ B * radius (physical 1 w) / ρ := by positivity
        linarith only [hh]
      _ = _ := by field_simp
  rw [jumpKernel_physical hε hw, jumpKernel_physical hρ hw,
    radius_physical_eq_mul hρ.le]
  calc
    _ ≤ ε ^ d * ((ε ^ (d + 2))⁻¹ * (radius (physical 1 w) ^ (d + 2))⁻¹ *
        (2 * B + B * (ε * radius (physical 1 w)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlin (by positivity)) (pow_nonneg hε.le _)
    _ = (radius (physical 1 w) ^ (d + 2))⁻¹ *
        ((2 * B + B * (ε * radius (physical 1 w))) / ε ^ 2) := by
      simp only [pow_add, mul_inv]
      field_simp
    _ ≤ (radius (physical 1 w) ^ (d + 2))⁻¹ *
        (2 * B * ((1 + ρ * radius (physical 1 w)) / ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = _ := by
      simp only [pow_add, mul_inv]
      field_simp

/-- The normalization is the unscaled kernel second moment over its scale-dependent
finite Euclidean ball. -/
lemma kappa_eq_unit_kernel_sum {ρ : ℝ} (hρ : 0 < ρ) :
    kappa d ρ = ∑ w ∈ unitBallIndices d ρ,
      jumpKernel (physical 1 w) * radius (physical 1 w) ^ 2 := by
  rw [kappa_eq_integer_sum hρ]
  apply Finset.sum_congr rfl
  intro w hw
  have hn := ((mem_unitBallIndices hρ w).mp hw).1
  rw [LatticeSums.kernel_mul_radius_sq ((physical_eq_zero_iff zero_lt_one w).not.mpr hn),
    Real.rpow_neg (radius_nonneg _), Real.rpow_natCast]

/-- The finite part of the kernel remainder comparison is bounded by the critical
normalization times the Hölder oscillation on that finite Euclidean ball. -/
theorem kernel_remainder_sub_sum_le {v : (Fin d → ℝ) → ℝ}
    (hv : ContDiff ℝ 2 v) {σ B : ℝ} (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hHolder : ∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
      B * radius (x - y) ^ σ) {ρ ε ε' : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hε' : 0 < ε') (q : Site d) :
    ∑ w ∈ unitBallIndices d ρ,
      |ε ^ d * (jumpKernel (physical ε w) *
          smoothRemainder v (physical ε q) (physical ε w)) -
        ε' ^ d * (jumpKernel (physical ε' w) *
          smoothRemainder v (physical ε' q) (physical ε' w))| ≤
      B / 2 * (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ * kappa d ρ := by
  classical
  rw [kappa_eq_unit_kernel_sum hρ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have hm := (mem_unitBallIndices hρ w).mp hw
  have hr : radius (physical 1 w) ≤ 1 / ρ := by
    rw [radius_physical_eq_mul hρ.le] at hm
    exact (le_div_iff₀ hρ).mpr (by simpa only [mul_comm] using hm.2)
  have hp : (|ε - ε'| * (radius (physical 1 q) + radius (physical 1 w))) ^ σ ≤
      (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ :=
    Real.rpow_le_rpow (mul_nonneg (abs_nonneg _)
      (add_nonneg (radius_nonneg _) (radius_nonneg _)))
      (mul_le_mul_of_nonneg_left (add_le_add_right hr _) (abs_nonneg _)) hσ
  calc
    _ ≤ jumpKernel (physical 1 w) * (B / 2 * radius (physical 1 w) ^ 2 *
        (|ε - ε'| * (radius (physical 1 q) + radius (physical 1 w))) ^ σ) :=
      kernel_remainder_sub_le hv hσ hB hHolder hε hε' q hm.1
    _ ≤ jumpKernel (physical 1 w) * (B / 2 * radius (physical 1 w) ^ 2 *
        (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp (by positivity)) (jumpKernel_nonneg _)
    _ = _ := by ring

/-- The numerator difference splits into a finite Hölder term and a uniformly bounded
linear tail. Absolute summability follows from the bounded-function remainder bound. -/
theorem smoothFluctuation_numerator_sub_le (d : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ (v : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 v →
      ∀ (σ B L : ℝ), 0 ≤ σ → 0 ≤ L →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) → ∀ ρ ε ε' : ℝ,
      ρ ∈ Set.Ioo (0 : ℝ) 1 → ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε' ∈ Set.Ioo (0 : ℝ) 1 → ρ ≤ ε → ρ ≤ ε' →
      ∀ (q : Site d) (a : Edge d → ℝ) (m₀ : ℝ), (∀ e, |a e - m₀| ≤ L) →
      |(ε ^ d * ∑' w : Site d, (if hw : w = 0 then 0 else
          (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε w) *
            smoothRemainder v (physical ε q) (physical ε w))) -
        (ε' ^ d * ∑' w : Site d, (if hw : w = 0 then 0 else
          (a (edgeAdd q w hw) - m₀) * jumpKernel (physical ε' w) *
            smoothRemainder v (physical ε' q) (physical ε' w)))| ≤
        L * (B / 2 * (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ *
          kappa d ρ) + 4 * B * L * T := by
  classical
  obtain ⟨T, hT, htail⟩ := kernel_tail_sum_bound d
  refine ⟨T, hT, ?_⟩
  intro v hv σ B L hσ hL hv0 hv1 hv2 hHolder ρ ε ε' hρ hε hε' hρε hρε' q a m₀ ha
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hρ0 := hρ.1
  let f := fun e : ℝ => fun w : Site d => if hw : w = 0 then (0 : ℝ) else
    (a (edgeAdd q w hw) - m₀) * (e ^ d *
      (jumpKernel (physical e w) * smoothRemainder v (physical e q) (physical e w)))
  have hf (e : ℝ) (he : e ∈ Set.Ioo (0 : ℝ) 1) : Summable (f e) := by
    obtain ⟨C, _, hb⟩ := smoothRemainder_kernel_abs_sum_bound d
    have hs := (hb e he v B hv hv0 hv1 hv2 q).1
    apply (hs.mul_left (L * e ^ d)).of_norm_bounded
    intro w
    dsimp [f]
    split_ifs with hw
    · simp only [abs_zero, mul_zero, le_refl]
    · have hk := jumpKernel_nonneg (physical e w)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg he.1.le _),
        abs_of_nonneg (jumpKernel_nonneg _)]
      calc
        _ ≤ L * (e ^ d * (jumpKernel (physical e w) *
            |smoothRemainder v (physical e q) (physical e w)|)) :=
          mul_le_mul_of_nonneg_right (ha _)
            (mul_nonneg (pow_nonneg he.1.le _) (mul_nonneg hk (abs_nonneg _)))
        _ = _ := by ring
  let g := fun w : Site d => if w ∈ unitBallIndices d ρ then
    L * |ε ^ d * (jumpKernel (physical ε w) *
        smoothRemainder v (physical ε q) (physical ε w)) -
      ε' ^ d * (jumpKernel (physical ε' w) *
        smoothRemainder v (physical ε' q) (physical ε' w))| else 0
  have hg : Summable g := by
    apply summable_of_hasFiniteSupport
    apply (unitBallIndices d ρ).finite_toSet.subset
    intro w hw
    by_contra hn
    exact hw (if_neg hn)
  let t := fun w : Site d => if 1 < radius (physical ρ w) then
    jumpKernel (physical ρ w) * (1 + radius (physical ρ w)) else 0
  have ht : Summable t := (htail ρ hρ).1
  have ht0 (w : Site d) : 0 ≤ t w := by
    dsimp [t]
    split_ifs
    · exact mul_nonneg (jumpKernel_nonneg _)
        (add_nonneg zero_le_one (radius_nonneg _))
    · exact le_rfl
  have hfg (w : Site d) : ‖f ε w - f ε' w‖ ≤
      g w + (4 * B * L * ρ ^ d) * t w := by
    by_cases hw : w = 0
    · subst w
      simp only [f, dite_true, sub_self, norm_zero]
      have hg0 : 0 ≤ g 0 := by dsimp [g]; split_ifs <;> positivity
      exact add_nonneg hg0 (mul_nonneg (by positivity) (ht0 0))
    have heq : f ε w - f ε' w = (a (edgeAdd q w hw) - m₀) *
        (ε ^ d * (jumpKernel (physical ε w) *
            smoothRemainder v (physical ε q) (physical ε w)) -
          ε' ^ d * (jumpKernel (physical ε' w) *
            smoothRemainder v (physical ε' q) (physical ε' w))) := by
      simp only [f, dif_neg hw]
      ring
    rw [heq, Real.norm_eq_abs, abs_mul]
    by_cases hm : w ∈ unitBallIndices d ρ
    · simp only [g, if_pos hm]
      have hh := mul_le_mul_of_nonneg_right (ha (edgeAdd q w hw))
        (abs_nonneg (ε ^ d * (jumpKernel (physical ε w) *
          smoothRemainder v (physical ε q) (physical ε w)) -
        ε' ^ d * (jumpKernel (physical ε' w) *
          smoothRemainder v (physical ε' q) (physical ε' w))))
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (ht0 w)))
    · have hr : 1 < radius (physical ρ w) := by
        by_contra hn
        exact hm ((mem_unitBallIndices hρ.1 w).mpr ⟨hw, le_of_not_gt hn⟩)
      simp only [g, if_neg hm, zero_add, t, if_pos hr]
      have h₁ := kernel_remainder_le_reference_linear hv0 hv1 hρ.1 hρε q hw
      have h₂ := kernel_remainder_le_reference_linear hv0 hv1 hρ.1 hρε' q hw
      have htri := abs_sub
        (ε ^ d * (jumpKernel (physical ε w) *
          smoothRemainder v (physical ε q) (physical ε w)))
        (ε' ^ d * (jumpKernel (physical ε' w) *
          smoothRemainder v (physical ε' q) (physical ε' w)))
      simp only [abs_mul, abs_of_nonneg (pow_nonneg hε.1.le _),
        abs_of_nonneg (pow_nonneg hε'.1.le _),
        abs_of_nonneg (jumpKernel_nonneg _)] at htri
      calc
        _ ≤ L * (ε ^ d * (jumpKernel (physical ε w) *
            |smoothRemainder v (physical ε q) (physical ε w)|) +
          ε' ^ d * (jumpKernel (physical ε' w) *
            |smoothRemainder v (physical ε' q) (physical ε' w)|)) :=
          mul_le_mul (ha _) htri (abs_nonneg _) hL
        _ ≤ L * (2 * B * (ρ ^ d * (jumpKernel (physical ρ w) *
            (1 + radius (physical ρ w)))) +
          2 * B * (ρ ^ d * (jumpKernel (physical ρ w) *
            (1 + radius (physical ρ w))))) :=
          mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hL
        _ = _ := by ring
  have hgBound : ∑' w, g w ≤ L * (B / 2 *
      (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ * kappa d ρ) := by
    rw [tsum_eq_sum (s := unitBallIndices d ρ) (fun w hw => if_neg hw)]
    simp only [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (kernel_remainder_sub_sum_le hv hσ hB hHolder hρ.1 hε.1 hε'.1 q) hL
  have hnorm := tsum_of_norm_bounded (hg.add (ht.mul_left (4 * B * L * ρ ^ d))).hasSum hfg
  rw [hg.tsum_add (ht.mul_left _), tsum_mul_left] at hnorm
  have hsum (e : ℝ) : ∑' w, f e w = e ^ d * ∑' w : Site d,
      (if hw : w = 0 then 0 else (a (edgeAdd q w hw) - m₀) *
        jumpKernel (physical e w) * smoothRemainder v (physical e q) (physical e w)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    dsimp [f]
    split_ifs <;> ring
  rw [(hf ε hε).tsum_sub (hf ε' hε'), hsum ε, hsum ε', Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  calc
    _ ≤ L * (B / 2 * (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ *
        kappa d ρ) + 4 * B * L * (ρ ^ d * ∑' w, t w) := by
      simpa only [mul_assoc] using add_le_add_left hgBound
        ((4 * B * L * ρ ^ d) * ∑' w, t w)
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (htail ρ hρ).2 (by positivity))

/-- Combining the Hölder and inverse-index contributions preserves their uniform
coefficient bound. -/
private lemma modulus_bound_combine (A H J X M : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hX : 0 ≤ X) (hM : 0 ≤ M) :
    A * M + (H * X + J * M) ≤ (A + H + J + 1) * (X + M) := by
  nlinarith only [mul_nonneg hA hX, mul_nonneg hJ hX, mul_nonneg hH hM, hX, hM]

/-- On a triadic scale block, the smooth fluctuation has a uniform Hölder modulus
in the scale, with the logarithmic normalization error bounded by `1 / m`. -/
theorem smoothFluctuation_modulus (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (c C₀ K lam B : ℝ) (hc : 0 < c) (hcC : c ≤ C₀) (hlam : 0 < lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ (v : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) →
      ∀ (m : ℕ), 1 ≤ m → ∀ ε ε' : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε' ∈ Set.Ioo (0 : ℝ) 1 → c / 3 ^ m ≤ ε → ε ≤ C₀ / 3 ^ m →
      c / 3 ^ m ≤ ε' → ε' ≤ C₀ / 3 ^ m →
      ∀ (q : Site d), radius (physical 1 q) ≤ K * 3 ^ m →
      ∀ (a : Edge d → ℝ) (m₀ : ℝ), (∀ e, |a e - m₀| ≤ lam⁻¹) →
        |smoothFluctuation ε a m₀ v q - smoothFluctuation ε' a m₀ v q| ≤
          A * ((3 ^ m * |ε - ε'|) ^ σ + 1 / m) := by
  have hσrange : 0 ≤ σ ∧ σ ≤ 1 := ⟨hσ.le, hσ1⟩
  classical
  obtain ⟨A₀, hA₀, hnormal⟩ :=
    smoothFluctuation_normalization_sub_bound hd c C₀ B lam⁻¹ hc hcC
  obtain ⟨D, hD, hupper⟩ := kappa_block_le d c hc
  obtain ⟨b, hb, hlower⟩ := le_kappa_block hd C₀ (hc.trans_le hcC)
  obtain ⟨T, hT, hdiff⟩ := smoothFluctuation_numerator_sub_le d
  let H : ℝ := lam⁻¹ * (|B| / 2) * (|K| + 1 / c) ^ σ * D / b
  let J : ℝ := 4 * |B| * lam⁻¹ * T / b
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨A₀ + H + J + 1, by positivity, ?_⟩
  intro v hv hv0 hv1 hv2 hHolder m hm ε ε' hε hε' hmin hmax hmin' hmax' q hq a m₀ ha
  have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
  have hL : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hp : (0 : ℝ) < 3 ^ m := pow_pos (by norm_num) _
  let ρ : ℝ := c / 3 ^ m
  have hρ0 : 0 < ρ := div_pos hc hp
  have hρ : ρ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hρ0, hmin.trans_lt hε.2⟩
  let N := fun e : ℝ => e ^ d * ∑' w : Site d, (if hw : w = 0 then 0 else
    (a (edgeAdd q w hw) - m₀) * jumpKernel (physical e w) *
      smoothRemainder v (physical e q) (physical e w))
  have hn : |N ε - N ε'| ≤ lam⁻¹ * (B / 2 *
      (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ * kappa d ρ) +
      4 * B * lam⁻¹ * T :=
    hdiff v hv σ B lam⁻¹ hσrange.1 hL hv0 hv1 hv2 hHolder ρ ε ε'
      hρ hε hε' hmin hmin' q a m₀ ha
  have hr : |ε - ε'| * (radius (physical 1 q) + 1 / ρ) ≤
      (|K| + 1 / c) * (3 ^ m * |ε - ε'|) := by
    have hi : 1 / ρ = 3 ^ m / c := by dsimp [ρ]; field_simp
    rw [hi]
    calc
      _ ≤ |ε - ε'| * (|K| * 3 ^ m + 3 ^ m / c) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_left (hq.trans
            (mul_le_mul_of_nonneg_right (le_abs_self K) hp.le)) _) (abs_nonneg _)
      _ = _ := by ring
  have hpow : (|ε - ε'| * (radius (physical 1 q) + 1 / ρ)) ^ σ ≤
      (|K| + 1 / c) ^ σ * (3 ^ m * |ε - ε'|) ^ σ := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ |K| + 1 / c)
      (mul_nonneg hp.le (abs_nonneg _))]
    exact Real.rpow_le_rpow (mul_nonneg (abs_nonneg _)
      (add_nonneg (radius_nonneg _) (by positivity))) hr hσrange.1
  have hkap : kappa d ρ ≤ D * m := hupper m hm ρ hρ le_rfl
  have hnum : |N ε - N ε'| ≤
      (lam⁻¹ * (B / 2) * (|K| + 1 / c) ^ σ * D *
        (3 ^ m * |ε - ε'|) ^ σ) * m + 4 * B * lam⁻¹ * T := by
    apply hn.trans
    apply add_le_add_left
    calc
      _ ≤ lam⁻¹ * (B / 2 *
          ((|K| + 1 / c) ^ σ * (3 ^ m * |ε - ε'|) ^ σ) * (D * m)) := by
        apply mul_le_mul_of_nonneg_left _ hL
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hkap
          (kappa_pos hd hρ).le (by positivity)
      _ = _ := by ring
  have hsecond : |(kappa d ε')⁻¹ * (N ε - N ε')| ≤
      H * (3 ^ m * |ε - ε'|) ^ σ + J / m := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (kappa_pos hd hε')), ← div_eq_inv_mul]
    calc
      _ ≤ ((lam⁻¹ * (B / 2) * (|K| + 1 / c) ^ σ * D *
          (3 ^ m * |ε - ε'|) ^ σ) * m + 4 * B * lam⁻¹ * T) / (b * m) :=
        div_le_div₀ (by positivity) hnum (mul_pos hb hm0)
          (hlower m hm ε' hε' hmax')
      _ = _ := by
        dsimp [H, J]
        rw [abs_of_nonneg hB]
        field_simp
  have hfirst : |((kappa d ε)⁻¹ - (kappa d ε')⁻¹) * N ε| ≤ A₀ / m :=
    hnormal v hv hv0 hv1 hv2 hL m hm ε ε' hε hε' hmin hmax hmin' hmax' q a m₀ ha
  have heq : smoothFluctuation ε a m₀ v q - smoothFluctuation ε' a m₀ v q =
      ((kappa d ε)⁻¹ - (kappa d ε')⁻¹) * N ε +
        (kappa d ε')⁻¹ * (N ε - N ε') := by
    dsimp [smoothFluctuation, N]
    ring
  rw [heq]
  calc
    _ ≤ A₀ / m + (H * (3 ^ m * |ε - ε'|) ^ σ + J / m) :=
      (abs_add_le _ _).trans (add_le_add hfirst hsecond)
    _ ≤ (A₀ + H + J + 1) * ((3 ^ m * |ε - ε'|) ^ σ + 1 / m) := by
      have hX : 0 ≤ (3 ^ m * |ε - ε'|) ^ σ := Real.rpow_nonneg (by positivity) _
      have hM : 0 ≤ (1 : ℝ) / m := by positivity
      simpa only [div_eq_mul_inv, one_mul] using
        modulus_bound_combine A₀ H J _ _ hA₀.le hH hJ hX hM

end
end LongRange
