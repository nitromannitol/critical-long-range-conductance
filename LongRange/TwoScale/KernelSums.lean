import LongRange.Appendix.Kappa
import LongRange.Model.Lattice

/-!
# Kernel sums for deterministic errors

The Taylor remainder and the exterior linear growth are controlled by the Euclidean
radial bounds of Proposition A.1.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The small-jump Taylor remainder has a scale-independent lattice sum. -/
theorem kernel_remainder_sum_bound (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ d * ∑ w ∈ unitBallIndices d ε,
        jumpKernel (physical ε w) * radius (physical ε w) ^ (2 + σ) ≤ C := by
  by_cases hd : d = 0
  · subst d
    exact ⟨1, zero_lt_one, fun ε _ => by
      simp only [LatticeSums.unit_ball_zero, Finset.sum_empty, mul_zero]; norm_num⟩
  have hα : 0 ≤ (d : ℝ) - σ := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
    linarith
  obtain ⟨C, hC, hb⟩ := (lattice_sums d).1 ((d : ℝ) - σ) hα
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have heq (w : Site d) (hw : w ∈ unitBallIndices d ε) :
      jumpKernel (physical ε w) * radius (physical ε w) ^ (2 + σ) =
        1 / radius (physical ε w) ^ ((d : ℝ) - σ) := by
    have hz := unitBallIndices_physical_ne_zero hε.1 hw
    have hr := radius_pos hz
    rw [jumpKernel_of_ne_zero hz, ← Real.rpow_natCast, ← Real.rpow_neg hr.le,
      ← Real.rpow_add hr, one_div, ← Real.rpow_neg hr.le]
    congr 1
    push_cast
    ring
  simp_rw [Finset.sum_congr rfl heq]
  simpa only [if_pos (show (d : ℝ) - σ < d by linarith)] using (hb ε hε).1

/-- Outside the unit ball, the kernel with linear growth is the sum of two radial powers. -/
lemma kernel_linear_growth_eq {d : ℕ} {z : Fin d → ℝ} (hz : 1 < radius z) :
    jumpKernel z * (1 + radius z) =
      1 / radius z ^ ((d : ℝ) + 2) + 1 / radius z ^ ((d : ℝ) + 1) := by
  have hr : 0 < radius z := lt_trans zero_lt_one hz
  have hn : z ≠ 0 := by
    intro h
    simp only [h, radius, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero] at hz
    linarith
  rw [jumpKernel_of_ne_zero hn]
  have hp : radius z ^ ((d : ℝ) + 1) * radius z = radius z ^ (d + 2) := by
    rw [← Real.rpow_add_one hr.ne', ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast, ← hp]
  field_simp [hr.ne', (Real.rpow_pos_of_pos hr ((d : ℝ) + 1)).ne']

/-- The large-jump kernel with linear growth is summable and uniformly bounded after scaling. -/
theorem kernel_tail_sum_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      Summable (fun w : Site d => if 1 < radius (physical ε w) then
        jumpKernel (physical ε w) * (1 + radius (physical ε w)) else 0) ∧
      ε ^ d * ∑' w : Site d, (if 1 < radius (physical ε w) then
        jumpKernel (physical ε w) * (1 + radius (physical ε w)) else 0) ≤ C := by
  obtain ⟨A, hA, ha⟩ := (lattice_sums d).1 ((d : ℝ) + 2) (by positivity)
  obtain ⟨B, hB, hb⟩ := (lattice_sums d).1 ((d : ℝ) + 1) (by positivity)
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro ε hε
  obtain ⟨hsa, hba⟩ := (ha ε hε).2 (by linarith)
  obtain ⟨hsb, hbb⟩ := (hb ε hε).2 (by linarith)
  let f := fun w : Site d => if 1 < radius (physical ε w) then
    jumpKernel (physical ε w) * (1 + radius (physical ε w)) else 0
  let g := fun w : Site d =>
    (if 1 ≤ radius (physical ε w) then
      1 / radius (physical ε w) ^ ((d : ℝ) + 2) else 0) +
    (if 1 ≤ radius (physical ε w) then
      1 / radius (physical ε w) ^ ((d : ℝ) + 1) else 0)
  have hfg : ∀ w, f w ≤ g w := by
    intro w
    dsimp [f, g]
    by_cases hw : 1 < radius (physical ε w)
    · rw [if_pos hw, if_pos hw.le, if_pos hw.le, kernel_linear_growth_eq hw]
    · rw [if_neg hw]
      split_ifs <;> positivity
  have hf0 : ∀ w, 0 ≤ f w := by
    intro w
    dsimp [f]
    split_ifs with hw
    · rw [kernel_linear_growth_eq hw]
      positivity
    · exact le_rfl
  have hsg : Summable g := hsa.add hsb
  have hsf : Summable f := Summable.of_nonneg_of_le hf0 hfg hsg
  refine ⟨hsf, ?_⟩
  calc
    ε ^ d * ∑' w, f w ≤ ε ^ d * ∑' w, g w :=
      mul_le_mul_of_nonneg_left (hsf.tsum_le_tsum hfg hsg) (pow_nonneg hε.1.le d)
    _ ≤ A + B := by
      rw [show (∑' w, g w) = _ + _ from hsa.tsum_add hsb, mul_add]
      exact add_le_add hba hbb

/-- Separated lattice subsets have a summable boundary kernel with inverse-square decay. -/
theorem boundary_kernel_sum_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ ρ : ℝ, ε ≤ ρ →
      ∀ (y : Site d) (S : Set (Site d)),
        (∀ x ∈ S, ρ ≤ radius (physical ε (y - (x : Site d)))) →
        Summable (fun x : S => jumpKernel (physical ε (y - (x : Site d)))) ∧
        ε ^ d * ∑' x : S, jumpKernel (physical ε (y - (x : Site d))) ≤ C * ρ ^ (-2 : ℝ) := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε ρ hρ y S _
    have hρ0 : 0 ≤ ρ := hε.le.trans hρ
    have hz (x : S) : physical ε (y - (x : Site 0)) = 0 := Subsingleton.elim _ _
    simp only [hz, jumpKernel_zero, summable_zero, tsum_zero, mul_zero, true_and]
    positivity
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  let C := Euclidean.Shell.shellConstant d * 24
  have hC : 0 < C := mul_pos (Euclidean.Shell.shellConstant_pos hd1) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro ε hε ρ hερ y S hsep
  have hρ : 0 < ρ := hε.trans_le hερ
  let t := ε / ρ
  have ht : 0 < t := div_pos hε hρ
  have ht1 : t ≤ 1 := (div_le_one hρ).mpr hερ
  have hr (w : Site d) : radius (physical ε w) = ρ * radius (physical t w) := by
    rw [radius_physical_eq_mul hε.le, radius_physical_eq_mul ht.le]
    dsimp [t]
    field_simp
  have hsep' (x : S) : 1 ≤ radius (physical t (y - (x : Site d))) := by
    have h := hsep x x.property
    rw [hr] at h
    exact (le_mul_iff_one_le_right hρ).mp h
  have hterm (x : S) : jumpKernel (physical ε (y - (x : Site d))) =
      (ρ ^ (d + 2))⁻¹ * radius (physical t (y - (x : Site d))) ^ (-((d : ℝ) + 2)) := by
    have hz : physical ε (y - (x : Site d)) ≠ 0 := by
      intro hz
      have h := hsep x x.property
      rw [hz] at h
      simp only [radius, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, Real.sqrt_zero] at h
      exact (not_le_of_gt hρ) h
    rw [jumpKernel_of_ne_zero hz, hr, mul_pow, mul_inv,
      Real.rpow_neg (radius_nonneg _)]
    norm_cast
  have hfinite (u : Finset S) :
      ∑ x ∈ u, jumpKernel (physical ε (y - (x : Site d))) ≤ C * ρ ^ (-2 : ℝ) / ε ^ d := by
    let v := u.image (fun x : S => y - (x : Site d))
    have hi : Function.Injective (fun x : S => y - (x : Site d)) := by
      intro a b hab
      exact Subtype.ext (sub_right_injective hab)
    have hb := Euclidean.Estimates.exterior_finset_le hd1
      (α := (d : ℝ) + 2) (by linarith) ht (one_le_one_div ht ht1) v
    have hs : (∑ x ∈ u, jumpKernel (physical ε (y - (x : Site d)))) =
        (ρ ^ (d + 2))⁻¹ * ∑ w ∈ v,
          (if 1 ≤ radius (physical t w) then
            radius (physical t w) ^ (-((d : ℝ) + 2)) else 0) := by
      rw [Finset.sum_image (fun a _ b _ h => hi h), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [if_pos (hsep' x), hterm]
    rw [hs]
    calc
      _ ≤ (ρ ^ (d + 2))⁻¹ * (t ^ (-((d : ℝ) + 2)) *
          (Euclidean.Shell.shellConstant d * ((1 + 1 / (2 : ℝ)) *
            ((4 : ℝ) ^ (2 : ℝ) * (1 / t) ^ (-(2 : ℝ)))))) := by
        have hsub : (d : ℝ) + 2 - d = 2 := by ring
        rw [hsub] at hb
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * ρ ^ (-2 : ℝ) / ε ^ d := by
        rw [Euclidean.Estimates.one_div_rpow_neg_eq ht]
        simp only [Real.rpow_neg ht.le, Real.rpow_neg hρ.le]
        rw [show (d : ℝ) + 2 = ((d + 2 : ℕ) : ℝ) by push_cast; rfl]
        simp only [Real.rpow_natCast, Real.rpow_two]
        dsimp [t, C]
        simp only [div_pow, pow_add, pow_two]
        field_simp [hρ.ne', hε.ne']
        ring
  have hn : ∀ x : S, 0 ≤ jumpKernel (physical ε (y - (x : Site d))) := by
    intro x
    rw [hterm]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hρ.le _))
      (Real.rpow_nonneg (radius_nonneg _) _)
  have hs := summable_of_sum_le hn hfinite
  refine ⟨hs, ?_⟩
  have hb := hs.tsum_le_of_sum_le hfinite
  calc
    ε ^ d * ∑' x : S, jumpKernel (physical ε (y - (x : Site d))) =
        (∑' x : S, jumpKernel (physical ε (y - (x : Site d)))) * ε ^ d := mul_comm _ _
    _ ≤ C * ρ ^ (-2 : ℝ) := (le_div_iff₀ (pow_pos hε d)).mp hb

/-- Euclidean distance to the domain gives the boundary estimate in the source normalization. -/
theorem boundary_kernel_sum_dist_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ (y : Site d) (U : Set (Fin d → ℝ)),
        let δ := Metric.infDist (WithLp.toLp 2 (physical ε y))
          (WithLp.toLp 2 '' U)
        0 < δ →
        Summable (fun x : latticeSet ε U => jumpKernel (physical ε (y - (x : Site d)))) ∧
        ε ^ d * ∑' x : latticeSet ε U, jumpKernel (physical ε (y - (x : Site d))) ≤
          C * (δ + ε) ^ (-2 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := boundary_kernel_sum_bound d
  refine ⟨4 * C, mul_pos (by norm_num) hC, ?_⟩
  intro ε hε y U δ hδ
  have hdist (x : latticeSet ε U) : δ ≤ radius (physical ε (y - (x : Site d))) := by
    have h := Metric.infDist_le_dist_of_mem
      (x := WithLp.toLp 2 (physical ε y))
      (Set.mem_image_of_mem (WithLp.toLp 2)
        (show physical ε (x : Site d) ∈ U from x.property))
    rw [dist_eq_norm, ← WithLp.toLp_sub, ← radius_norm] at h
    convert h using 1
    congr 1
    funext k
    simp only [physical, Pi.sub_apply, Int.cast_sub, mul_sub]
  have hsep : ∀ x ∈ latticeSet ε U,
      max ε δ ≤ radius (physical ε (y - (x : Site d))) := by
    intro x hx
    have hdx := hdist ⟨x, hx⟩
    have hn : y - (x : Site d) ≠ 0 := by
      intro h
      rw [h] at hdx
      have hz : physical ε (0 : Site d) = 0 := by
        funext k
        simp only [physical, Pi.zero_apply, Int.cast_zero, mul_zero]
      rw [hz] at hdx
      simp only [radius, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, Real.sqrt_zero] at hdx
      exact (not_le_of_gt hδ) hdx
    apply max_le _ hdx
    rw [radius_physical_eq_mul hε.le]
    exact le_mul_of_one_le_right hε.le (lattice_radius_ge_one hn)
  obtain ⟨hs, hbound⟩ := hb ε hε (max ε δ) (le_max_left _ _) y (latticeSet ε U) hsep
  refine ⟨hs, hbound.trans ?_⟩
  have hmax : 0 < max ε δ := hε.trans_le (le_max_left _ _)
  have hsum : 0 < δ + ε := add_pos hδ hε
  have hsum_le : δ + ε ≤ 2 * max ε δ := by
    linarith only [le_max_left ε δ, le_max_right ε δ]
  have halg : (max ε δ) ^ (-2 : ℝ) ≤ 4 * (δ + ε) ^ (-2 : ℝ) := by
    simp only [Real.rpow_neg hmax.le, Real.rpow_neg hsum.le, Real.rpow_two]
    rw [← one_div, ← one_div, ← div_eq_mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hmax) (sq_pos_of_pos hsum)).mpr
    have hsquare := mul_self_le_mul_self hsum.le hsum_le
    nlinarith only [hsquare]
  calc
    C * (max ε δ) ^ (-2 : ℝ) ≤ C * (4 * (δ + ε) ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left halg hC.le
    _ = 4 * C * (δ + ε) ^ (-2 : ℝ) := by ring

end
end LongRange
