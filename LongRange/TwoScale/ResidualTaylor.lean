import LongRange.TwoScale.ResidualDefs
import LongRange.Calculus.Summability

/-!
# Taylor and boundary splitting of the generator

The coordinate slopes cancel the linear Taylor term exactly. Absolute convergence of the
bounded and affine generator series justifies this cancellation inside the lattice sum.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Subtracting the coordinate slope generators leaves the Taylor remainder minus the
exterior defect at an interior lattice point. -/
theorem generator_zeroExtension_sub_gradient (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} {v : (Fin d → ℝ) → ℝ} {B₀ B₁ : ℝ}
    (hB₀ : ∀ x, |v x| ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁)
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    generator ε a (zeroExtension ε U v) q -
        ∑ i, gradientCoeff ε v i q * generator ε a (linearFn ε (Pi.single i 1)) q =
      ε ^ d / kappa d ε * ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * jumpKernel (physical ε w) *
          (smoothRemainder v (physical ε q) (physical ε w) - exteriorDefect ε U v (q + w)) := by
  classical
  have hderiv_nonneg : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0)
  have hnonneg : 0 ≤ B₀ := (abs_nonneg _).trans (hB₀ 0)
  have hbound : ∀ r, |zeroExtension ε U v r| ≤ B₀ := by
    intro r
    unfold zeroExtension
    split_ifs
    · exact hB₀ _
    · simpa only [abs_zero] using hnonneg
  let F := fun w : Site d => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * (zeroExtension ε U v (q + w) - zeroExtension ε U v q) *
      jumpKernel (physical ε w)
  let G := fun (i : Fin d) (w : Site d) => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) *
      (linearFn ε (Pi.single i 1) (q + w) - linearFn ε (Pi.single i 1) q) *
      jumpKernel (physical ε w)
  have hF : Summable F := summable_generator_bounded hd hε hlam ha
    ⟨B₀ + B₁, add_nonneg hnonneg hderiv_nonneg, fun r =>
      (hbound r).trans (le_add_of_nonneg_right hderiv_nonneg)⟩ q
  have hG (i : Fin d) : Summable (G i) := by
    simpa only [G, add_zero] using
      (summable_generator_affine hd hε hlam ha (Pi.single i 1)
        (φ := fun _ => 0) ⟨0, le_rfl, by intro r; simp only [abs_zero, le_refl]⟩ q)
  have hsum : Summable (fun w => ∑ i, gradientCoeff ε v i q * G i w) :=
    summable_sum (fun i _ => (hG i).mul_left _)
  have hcoord (w : Site d) :
      ∑ i, gradientCoeff ε v i q *
        (linearFn ε (Pi.single i 1) (q + w) - linearFn ε (Pi.single i 1) q) =
      fderiv ℝ v (physical ε q) (physical ε w) := by
    simp only [linearFn_add, add_sub_cancel_left]
    have hlin (i : Fin d) : linearFn ε (Pi.single i 1) w = physical ε w i := by
      simp [linearFn, Pi.single_apply]
    simp_rw [hlin]
    conv_rhs => rw [pi_eq_sum_univ' (physical ε w), map_sum]
    simp only [map_smul, smul_eq_mul, gradientCoeff, Elliptic.partialDeriv, mul_comm]
  have hphysical (w : Site d) : physical ε (q + w) = physical ε q + physical ε w := by
    ext i
    simp only [physical, Pi.add_apply, Int.cast_add, mul_add]
  have hinterior : zeroExtension ε U v q = v (physical ε q) :=
    if_pos (mem_latticeSet.mp hq)
  change ε ^ d / kappa d ε * (∑' w, F w) -
    ∑ i, gradientCoeff ε v i q * (ε ^ d / kappa d ε * ∑' w, G i w) = _
  have hswap : (∑ i, gradientCoeff ε v i q *
      (ε ^ d / kappa d ε * ∑' w, G i w)) =
      ε ^ d / kappa d ε * ∑' w, ∑ i, gradientCoeff ε v i q * G i w := by
    rw [Summable.tsum_finsetSum (fun i _ => (hG i).mul_left _)]
    simp only [tsum_mul_left, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hswap, ← mul_sub, ← hF.tsum_sub hsum]
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : w = 0
  · simp only [F, G, hw, ↓reduceDIte, mul_zero, Finset.sum_const_zero, sub_zero]
  · simp only [F, G, hw, ↓reduceDIte]
    rw [show (∑ i, gradientCoeff ε v i q *
        (a (edgeAdd q w hw) *
          (linearFn ε (Pi.single i 1) (q + w) - linearFn ε (Pi.single i 1) q) *
            jumpKernel (physical ε w))) =
        a (edgeAdd q w hw) * jumpKernel (physical ε w) *
          ∑ i, gradientCoeff ε v i q *
            (linearFn ε (Pi.single i 1) (q + w) - linearFn ε (Pi.single i 1) q) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [hcoord, hinterior]
    unfold smoothRemainder exteriorDefect
    rw [hphysical]
    ring

end

end LongRange
