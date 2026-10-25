import LongRange.Model.Operator
import LatticeProb.Euclidean.Summability

/-!
# Absolute convergence for the critical operator

The Euclidean radial error series controls the kernel and its first moment after physical
scaling. These estimates justify the generator series on bounded and affine plus bounded data.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The critical jump kernel is nonnegative. -/
theorem jumpKernel_nonneg (z : Fin d → ℝ) : 0 ≤ jumpKernel z := by
  unfold jumpKernel
  split
  · exact le_rfl
  · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)

/-- Physical scaling factors out of the critical kernel at nonzero integer sites. -/
theorem jumpKernel_physical {ε : ℝ} (hε : 0 < ε) {w : Site d} (hw : w ≠ 0) :
    jumpKernel (physical ε w) = (ε ^ (d + 2))⁻¹ *
      (radius (physical 1 w) ^ (d + 2))⁻¹ := by
  rw [jumpKernel_of_ne_zero (fun h => hw ((physical_eq_zero_iff hε w).mp h)),
    radius_physical_eq_mul hε.le, mul_pow, mul_inv_rev, mul_comm]

/-- A scaled kernel first moment is dominated by the unscaled Euclidean radial error. -/
theorem jumpKernel_weight_le {ε : ℝ} (hε : 0 < ε) {w : Site d} (hw : w ≠ 0) :
    jumpKernel (physical ε w) * (1 + radius (physical ε w)) ≤
      ((ε ^ (d + 2))⁻¹ * (1 + ε)) * (radius (physical 1 w) ^ (d + 1))⁻¹ := by
  have hr := lattice_radius_ge_one hw
  have hrpos : 0 < radius (physical 1 w) := lt_of_lt_of_le zero_lt_one hr
  rw [jumpKernel_physical hε hw, radius_physical_eq_mul hε.le]
  have hpow : radius (physical 1 w) ^ (d + 2) =
      radius (physical 1 w) ^ (d + 1) * radius (physical 1 w) := by
    rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]
  have hbase : (1 + ε * radius (physical 1 w)) ≤
      (1 + ε) * radius (physical 1 w) := by nlinarith
  calc
    _ ≤ (ε ^ (d + 2))⁻¹ * (radius (physical 1 w) ^ (d + 2))⁻¹ *
        ((1 + ε) * radius (physical 1 w)) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _))
          (inv_nonneg.mpr (pow_nonneg hrpos.le _)))
    _ = _ := by
      rw [hpow, mul_inv_rev]
      calc
        _ = (ε ^ (d + 2))⁻¹ * (1 + ε) *
            (radius (physical 1 w) ^ (d + 1))⁻¹ *
              ((radius (physical 1 w))⁻¹ * radius (physical 1 w)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hrpos.ne', mul_one]

/-- The Euclidean kernel with its first physical moment is summable. -/
theorem summable_jumpKernel_weight (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun w : Site d =>
      jumpKernel (physical ε w) * (1 + radius (physical ε w))) := by
  have hexp : -(d : ℝ) - 1 = -((d + 1 : ℕ) : ℝ) := by push_cast; ring
  have herr : Summable (fun w : {w : Site d // w ≠ 0} =>
      (radius (physical 1 w.val) ^ (d + 1))⁻¹) := by
    have hs := LatticeProb.Euclidean.Summability.nonzero_radial_error_summable_real d hd
    refine hs.congr (fun w => ?_)
    rw [hexp, Real.rpow_eq_pow, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have hsub : Summable (fun w : {w : Site d // w ≠ 0} =>
      jumpKernel (physical ε w.val) * (1 + radius (physical ε w.val))) := by
    refine (herr.mul_left ((ε ^ (d + 2))⁻¹ * (1 + ε))).of_norm_bounded ?_
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (jumpKernel_nonneg _)
      (add_nonneg zero_le_one (radius_nonneg _)))]
    exact jumpKernel_weight_le hε w.property
  have hzero : jumpKernel (physical ε (0 : Site d)) *
      (1 + radius (physical ε (0 : Site d))) = 0 := by
    rw [(physical_eq_zero_iff hε 0).mpr rfl, jumpKernel_zero, zero_mul]
  have hsupp : Function.support (fun w : Site d =>
      jumpKernel (physical ε w) * (1 + radius (physical ε w))) ⊆ {w | w ≠ 0} := by
    intro w hw
    change w ≠ 0
    intro hz
    subst w
    exact hw hzero
  exact ((hasSum_subtype_iff_of_support_subset hsupp).mp hsub.hasSum).summable

/-- The unweighted Euclidean jump kernel is summable. -/
theorem summable_jumpKernel (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun w : Site d => jumpKernel (physical ε w)) := by
  refine (summable_jumpKernel_weight hd hε).of_nonneg_of_le
    (fun w => jumpKernel_nonneg _) ?_
  intro w
  exact le_mul_of_one_le_right (jumpKernel_nonneg _) (by
    linarith [radius_nonneg (physical ε w)])

/-- The first physical moment of the critical jump kernel is summable. -/
theorem summable_jumpKernel_firstMoment (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun w : Site d =>
      jumpKernel (physical ε w) * radius (physical ε w)) := by
  refine (summable_jumpKernel_weight hd hε).of_nonneg_of_le
    (fun w => mul_nonneg (jumpKernel_nonneg _) (radius_nonneg _)) ?_
  intro w
  exact mul_le_mul_of_nonneg_left (by linarith : radius (physical ε w) ≤
    1 + radius (physical ε w)) (jumpKernel_nonneg _)

/-- Finite support on the integer lattice gives a uniform absolute bound. -/
theorem exists_bound_of_finite_support {h : Site d → ℝ}
    (hh : Function.HasFiniteSupport h) : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |h q| ≤ M := by
  classical
  refine ⟨∑ q ∈ hh.toFinset, |h q|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro q
  by_cases hq : h q = 0
  · rw [hq, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · exact Finset.single_le_sum (s := hh.toFinset) (f := fun q => |h q|)
      (fun _ _ => abs_nonneg _) (by
      simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hq)

/-- The linear slope is evaluated at the physical increment `εw`. -/
theorem linearFn_add (ε : ℝ) (p : Fin d → ℝ) (q w : Site d) :
    linearFn ε p (q + w) = linearFn ε p q + linearFn ε p w := by
  simp only [linearFn, physical, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

/-- A coordinatewise slope estimate uses the Euclidean radius of the physical increment. -/
theorem abs_linearFn_le (ε : ℝ) (p : Fin d → ℝ) (w : Site d) :
    |linearFn ε p w| ≤ (∑ i, |p i|) * radius (physical ε w) := by
  calc
    |linearFn ε p w| ≤ ∑ i, |p i * physical ε w i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |p i| * |physical ε w i| := by simp only [abs_mul]
    _ ≤ ∑ i, |p i| * radius (physical ε w) := by
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (abs_coord_le_radius _ i) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Bounded functions have increments controlled by the kernel's first-moment weight. -/
theorem bounded_increment_bound {ε : ℝ} {h : Site d → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hh : ∀ q, |h q| ≤ M) (q w : Site d) :
    |h (q + w) - h q| ≤ (2 * M) * (1 + radius (physical ε w)) := by
  have hdiff : |h (q + w) - h q| ≤ 2 * M := by
    calc
      _ ≤ |h (q + w)| + |h q| := abs_sub _ _
      _ ≤ M + M := add_le_add (hh _) (hh _)
      _ = _ := by ring
  exact hdiff.trans (le_mul_of_one_le_right (by positivity) (by
    linarith [radius_nonneg (physical ε w)]))

/-- Affine plus bounded functions have a uniform Euclidean first-moment increment bound. -/
theorem affine_increment_bound (ε : ℝ) (p : Fin d → ℝ) {φ : Site d → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hφ : ∀ q, |φ q| ≤ M) (q w : Site d) :
    |(linearFn ε p (q + w) + φ (q + w)) - (linearFn ε p q + φ q)| ≤
      ((∑ i, |p i|) + 2 * M) * (1 + radius (physical ε w)) := by
  rw [linearFn_add]
  have htriangle : |(linearFn ε p q + linearFn ε p w + φ (q + w)) -
      (linearFn ε p q + φ q)| ≤ |linearFn ε p w| + |φ (q + w) - φ q| := by
    have heq : (linearFn ε p q + linearFn ε p w + φ (q + w)) -
        (linearFn ε p q + φ q) = linearFn ε p w + (φ (q + w) - φ q) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hdiff : |φ (q + w) - φ q| ≤ 2 * M := by
    exact (abs_sub _ _).trans (by linarith [hφ (q + w), hφ q])
  have hs : 0 ≤ ∑ i, |p i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hr := radius_nonneg (physical ε w)
  exact htriangle.trans ((add_le_add (abs_linearFn_le ε p w) hdiff).trans (by nlinarith))

/-- The defining generator series is absolutely summable under a first-moment increment bound.
This is the common estimate used for bounded and affine plus bounded functions. -/
theorem summable_generator_of_increment_bound (hd : 1 ≤ d) {ε lam C : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {h : Site d → ℝ}
    (hC : 0 ≤ C) (hh : ∀ q w, |h (q + w) - h q| ≤ C *
      (1 + radius (physical ε w))) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w)) := by
  refine ((summable_jumpKernel_weight hd hε).mul_left (lam⁻¹ * C)).of_norm_bounded ?_
  intro w
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte, norm_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le) hC)
      (mul_nonneg (jumpKernel_nonneg _) (add_nonneg zero_le_one (radius_nonneg _)))
  · simp only [hw, ↓reduceDIte, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg (jumpKernel_nonneg _)]
    calc
      _ ≤ lam⁻¹ * (C * (1 + radius (physical ε w))) * jumpKernel (physical ε w) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (ha _).2 (hh q w) (abs_nonneg _)
            (inv_nonneg.mpr hlam.le)) (jumpKernel_nonneg _)
      _ = _ := by ring

/-- Absolute summability of the generator on bounded data. -/
theorem summable_generator_bounded (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {h : Site d → ℝ}
    (hh : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |h q| ≤ M) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w)) := by
  obtain ⟨M, hM, hh⟩ := hh
  exact summable_generator_of_increment_bound hd hε hlam ha (C := 2 * M)
    (mul_nonneg (by norm_num) hM) (bounded_increment_bound hM hh) q

/-- Absolute summability of the generator for the physical linear slope plus bounded data. -/
theorem summable_generator_affine (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) {φ : Site d → ℝ}
    (hφ : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |φ q| ≤ M) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * ((linearFn ε p (q + w) + φ (q + w)) -
        (linearFn ε p q + φ q)) * jumpKernel (physical ε w)) := by
  obtain ⟨M, hM, hφ⟩ := hφ
  exact summable_generator_of_increment_bound hd hε hlam ha
    (C := (∑ i, |p i|) + 2 * M) (h := fun q => linearFn ε p q + φ q)
    (add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity))
    (affine_increment_bound ε p hM hφ) q

end

end LongRange
