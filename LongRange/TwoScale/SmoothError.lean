import LongRange.TwoScale.KernelSums
import LatticeProb.Analysis.TaylorHolder
import LatticeProb.Analysis.Elliptic.Holder

/-!
# The deterministic smooth error

Taylor's formula separates the small jumps into a quadratic term and a Hölder error.
Coordinate symmetry contracts the quadratic term to the Euclidean Laplacian, while
radial kernel estimates control the error and the exterior tail.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The first-order Taylor remainder at a physical displacement. -/
def smoothRemainder (v : (Fin d → ℝ) → ℝ) (x z : Fin d → ℝ) : ℝ :=
  v (x + z) - v x - fderiv ℝ v x z

/-- A bilinear form on coordinate vectors expands in the standard coordinate basis. -/
lemma bilinear_eq_coordinate_sum
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (z : Fin d → ℝ) :
    A z z = ∑ i, ∑ j, A (Pi.single i 1) (Pi.single j 1) * z i * z j := by
  classical
  have hz : z = ∑ i : Fin d, z i • Pi.single i (1 : ℝ) := pi_eq_sum_univ' z
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The normalized small-jump Hessian sum is exactly the Laplacian divided by `2d`. -/
theorem smooth_quadratic_sum {ε : ℝ} (hd : 1 ≤ d)
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (v : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    ε ^ d / kappa d ε * ∑ w ∈ unitBallIndices d ε,
      jumpKernel (physical ε w) *
        ((1 / 2) * iteratedFDeriv ℝ 2 v x ![physical ε w, physical ε w]) =
      Elliptic.laplacian v x / (2 * d) := by
  classical
  have hexp (z : Fin d → ℝ) :
      iteratedFDeriv ℝ 2 v x ![z, z] =
        ∑ i, ∑ j, Elliptic.secondPartial i j v x * z i * z j := by
    simpa only [Elliptic.secondPartial, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      bilinear_eq_coordinate_sum (fderiv ℝ (fderiv ℝ v) x) z
  have hterm (i j : Fin d) :
      ε ^ d / kappa d ε * ∑ w ∈ unitBallIndices d ε,
        jumpKernel (physical ε w) *
          (1 / 2 * (Elliptic.secondPartial i j v x * physical ε w i * physical ε w j)) =
        (1 / 2 * Elliptic.secondPartial i j v x) *
          (if i = j then 1 / (d : ℝ) else 0) := by
    rw [← second_moment_normalized hd hε i j]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  calc
    _ = ∑ i : Fin d, ∑ j : Fin d, ε ^ d / kappa d ε *
        ∑ w ∈ unitBallIndices d ε, jumpKernel (physical ε w) *
          (1 / 2 * (Elliptic.secondPartial i j v x * physical ε w i *
            physical ε w j)) := by
      simp_rw [hexp, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hterm]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      rw [Elliptic.laplacian, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The mean-kernel smooth error is summable and differs from the normalized
Laplacian by at most a dimension- and Hölder-exponent-dependent multiple of `κ⁻¹`. -/
theorem smooth_error_bound (d : ℕ) (hd : 1 ≤ d) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : (Fin d → ℝ) → ℝ) (B₀ B₁ B₂ M : ℝ),
      ContDiff ℝ 2 v → (∀ x, |v x| ≤ B₀) →
      (∀ x, ‖fderiv ℝ v x‖ ≤ B₁) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B₂) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        M * radius (x - y) ^ σ) →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ q : Site d,
        Summable (fun w : Site d => jumpKernel (physical ε w) *
          smoothRemainder v (physical ε q) (physical ε w)) ∧
        |ε ^ d / kappa d ε * ∑' w : Site d, jumpKernel (physical ε w) *
          smoothRemainder v (physical ε q) (physical ε w) -
          Elliptic.laplacian v (physical ε q) / (2 * d)| ≤
          C * (B₀ + B₁ + B₂ + M) / kappa d ε := by
  classical
  obtain ⟨A, hA, ha⟩ := kernel_remainder_sum_bound d hσ hσ1
  obtain ⟨B, hB, hb⟩ := kernel_tail_sum_bound d
  refine ⟨A + 2 * B, by positivity, ?_⟩
  intro v B₀ B₁ B₂ M hv hv0 hv1 hv2 hvH ε hε q
  have hB₀ : 0 ≤ B₀ := (abs_nonneg _).trans (hv0 0)
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hv1 0)
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans (hv2 0)
  have hM : 0 ≤ M := by
    let i : Fin d := ⟨0, hd⟩
    let z : Fin d → ℝ := Pi.single i 1
    have hz : z ≠ 0 := by
      intro h
      have hi := congrFun h i
      simp only [z, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hi
    have h := (norm_nonneg _).trans (hvH z 0)
    rw [sub_zero] at h
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos (radius_pos hz) σ)
  let x := physical ε q
  let s := unitBallIndices d ε
  let f := fun w : Site d => jumpKernel (physical ε w) *
    smoothRemainder v x (physical ε w)
  let Q := fun w : Site d => if w ∈ s then jumpKernel (physical ε w) *
    ((1 / 2) * iteratedFDeriv ℝ 2 v x ![physical ε w, physical ε w]) else 0
  let N := fun w : Site d => if w ∈ s then
    jumpKernel (physical ε w) * radius (physical ε w) ^ (2 + σ) else 0
  let T := fun w : Site d => if 1 < radius (physical ε w) then
    jumpKernel (physical ε w) * (1 + radius (physical ε w)) else 0
  have hQ : Summable Q := summable_of_ne_finset_zero (s := s) (by
    intro w hw
    simp only [Q, if_neg hw])
  have hN : Summable N := summable_of_ne_finset_zero (s := s) (by
    intro w hw
    simp only [N, if_neg hw])
  obtain ⟨hT, hTb⟩ := hb ε hε
  have hJ (w : Site d) : 0 ≤ jumpKernel (physical ε w) := by
    unfold jumpKernel
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
  have hdom (w : Site d) : ‖f w - Q w‖ ≤ M * N w + (2 * B₀ + B₁) * T w := by
    by_cases hw : w ∈ s
    · have hr := (mem_unitBallIndices hε.1 w).mp hw |>.2
      have ht : ¬1 < radius (physical ε w) := not_lt.mpr hr
      simp only [f, Q, N, T, if_pos hw, if_neg ht, mul_zero, add_zero]
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJ w)]
      calc
        _ ≤ jumpKernel (physical ε w) *
            (M * radius (physical ε w) ^ (2 + σ)) :=
          mul_le_mul_of_nonneg_left
            (TaylorHolder.remainder_sub_quadratic_le hv ⟨hσ.le, hσ1⟩ hvH x
              (physical ε w)) (hJ w)
        _ = _ := by ring
    · simp only [Q, N, if_neg hw, sub_zero, mul_zero, zero_add]
      by_cases ht : 1 < radius (physical ε w)
      · simp only [f, T, if_pos ht, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJ w)]
        calc
          _ ≤ jumpKernel (physical ε w) *
              (2 * B₀ + B₁ * radius (physical ε w)) :=
            mul_le_mul_of_nonneg_left (TaylorHolder.remainder_le_linear hv0 hv1 x _)
              (hJ w)
          _ ≤ (2 * B₀ + B₁) *
              (jumpKernel (physical ε w) * (1 + radius (physical ε w))) := by
            have hr := radius_nonneg (physical ε w)
            have hp := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB₀) hr
            have hh : 2 * B₀ + B₁ * radius (physical ε w) ≤
                (2 * B₀ + B₁) * (1 + radius (physical ε w)) := by
              nlinarith only [hp, hB₁]
            exact (mul_le_mul_of_nonneg_left hh (hJ w)).trans_eq (by ring)
      · have hw0 : w = 0 := by
          by_contra hn
          exact hw ((mem_unitBallIndices hε.1 w).mpr ⟨hn, le_of_not_gt ht⟩)
        have hz : physical ε w = 0 := by
          subst w
          ext i
          simp only [physical, Pi.zero_apply, Int.cast_zero, mul_zero]
        simp only [f, hz, jumpKernel_zero, zero_mul, norm_zero, T, if_neg ht, mul_zero,
          le_refl]
  have hg : Summable (fun w => M * N w + (2 * B₀ + B₁) * T w) :=
    (hN.mul_left M).add (hT.mul_left (2 * B₀ + B₁))
  have he : Summable (fun w => f w - Q w) := hg.of_norm_bounded hdom
  have hf : Summable f := by
    simpa only [sub_add_cancel] using he.add hQ
  have hsumN : ∑' w, N w = ∑ w ∈ s,
      jumpKernel (physical ε w) * radius (physical ε w) ^ (2 + σ) := by
    rw [tsum_eq_sum (s := s) (fun w hw => by simp only [N, if_neg hw])]
    apply Finset.sum_congr rfl
    intro w hw
    exact if_pos hw
  have hsumQ : ∑' w, Q w = ∑ w ∈ s, jumpKernel (physical ε w) *
      ((1 / 2) * iteratedFDeriv ℝ 2 v x ![physical ε w, physical ε w]) := by
    rw [tsum_eq_sum (s := s) (fun w hw => by simp only [Q, if_neg hw])]
    apply Finset.sum_congr rfl
    intro w hw
    exact if_pos hw
  have hnear : ε ^ d * ∑' w, N w ≤ A := by
    rw [hsumN]
    exact ha ε hε
  have herror : |∑' w, (f w - Q w)| ≤
      M * ∑' w, N w + (2 * B₀ + B₁) * ∑' w, T w := by
    have h := tsum_of_norm_bounded hg.hasSum hdom
    rw [Summable.tsum_add (hN.mul_left M) (hT.mul_left (2 * B₀ + B₁)),
      tsum_mul_left, tsum_mul_left] at h
    exact h
  have hscale : ε ^ d * |∑' w, (f w - Q w)| ≤
      M * A + (2 * B₀ + B₁) * B := by
    calc
      _ ≤ ε ^ d * (M * ∑' w, N w + (2 * B₀ + B₁) * ∑' w, T w) :=
        mul_le_mul_of_nonneg_left herror (pow_nonneg hε.1.le d)
      _ = M * (ε ^ d * ∑' w, N w) +
          (2 * B₀ + B₁) * (ε ^ d * ∑' w, T w) := by ring
      _ ≤ M * A + (2 * B₀ + B₁) * B := add_le_add
        (mul_le_mul_of_nonneg_left hnear hM)
        (mul_le_mul_of_nonneg_left hTb (by positivity))
  refine ⟨hf, ?_⟩
  have hquad : ε ^ d / kappa d ε * ∑' w, Q w =
      Elliptic.laplacian v x / (2 * d) := by
    rw [hsumQ]
    exact smooth_quadratic_sum hd hε v x
  change |ε ^ d / kappa d ε * ∑' w, f w -
    Elliptic.laplacian v x / (2 * d)| ≤ _
  rw [← hquad, ← mul_sub, ← hf.tsum_sub hQ, abs_mul,
    abs_of_nonneg (div_nonneg (pow_nonneg hε.1.le d) (kappa_pos hd hε).le),
    div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (kappa_pos hd hε)).mpr
  apply hscale.trans
  nlinarith only [hA.le, hB.le, hB₀, hB₁, hB₂, hM,
    mul_nonneg hA.le hB₀, mul_nonneg hA.le hB₁, mul_nonneg hA.le hB₂,
    mul_nonneg hB.le hB₁, mul_nonneg hB.le hB₂, mul_nonneg hB.le hM]

end
end LongRange
