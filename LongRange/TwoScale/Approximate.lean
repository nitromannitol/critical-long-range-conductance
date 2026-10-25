import LongRange.TwoScale.ResidualDefs
import LongRange.Corrector.Support
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Support and approximation of the two-scale solution

The approximate solution is supported in the physical domain. Its discrete L² distance
from the sampled smooth function is controlled by the correctors and the derivative bound.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The sampled zero extension vanishes outside the lattice domain. -/
theorem zeroExtension_supportedIn (ε : ℝ) (U : Set (Fin d → ℝ))
    (v : (Fin d → ℝ) → ℝ) : SupportedIn ε U (zeroExtension ε U v) := by
  intro q hq
  exact if_neg hq

/-- Supported correctors give a supported approximate solution. -/
theorem approxSolution_supportedIn {ε : ℝ} {U : Set (Fin d → ℝ)}
    {v : (Fin d → ℝ) → ℝ} {φ : Fin d → Site d → ℝ}
    (hφ : ∀ i, SupportedIn ε U (φ i)) : SupportedIn ε U (approxSolution ε U v φ) := by
  intro q hq
  simp only [approxSolution, zeroExtension_supportedIn ε U v q hq, hφ _ q hq,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- A bound on the derivative operator bounds each sampled coordinate derivative. -/
theorem abs_gradientCoeff_le {ε : ℝ} {v : (Fin d → ℝ) → ℝ} {B₁ : ℝ}
    (hB₁ : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁) (i : Fin d) (q : Site d) :
    |gradientCoeff ε v i q| ≤ B₁ := by
  have h := (fderiv ℝ v (physical ε q)).le_opNorm (Pi.single i 1)
  simpa only [gradientCoeff, Elliptic.partialDeriv, Real.norm_eq_abs,
    Pi.norm_single, norm_one, mul_one] using h.trans (by
      simpa only [Pi.norm_single, norm_one, mul_one] using hB₁ (physical ε q))

/-- The discrete norm depends only on values in the lattice domain. -/
theorem l2Norm_congr {ε : ℝ} {U : Set (Fin d → ℝ)} {g h : Site d → ℝ}
    (hgh : ∀ q ∈ latticeSet ε U, g q = h q) : l2Norm ε U g = l2Norm ε U h := by
  unfold l2Norm l2NormSq
  congr 2
  apply tsum_congr
  intro q
  rw [hgh q q.property]

/-- On a finite lattice domain the discrete norm is a scaled Euclidean norm. -/
theorem l2Norm_eq_euclidean {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (g : Site d → ℝ) [Fintype (latticeSet ε U)] :
    l2Norm ε U g = Real.sqrt (ε ^ d) *
      ‖(WithLp.toLp 2 (fun q : latticeSet ε U => g q) :
        EuclideanSpace ℝ (latticeSet ε U))‖ := by
  simp only [l2Norm, l2NormSq, tsum_fintype, Real.sqrt_mul (pow_nonneg hε.le d),
    EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]

/-- Triangle inequality for the discrete L² norm on a bounded domain. -/
theorem l2Norm_add_le {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (g h : Site d → ℝ) :
    l2Norm ε U (fun q => g q + h q) ≤ l2Norm ε U g + l2Norm ε U h := by
  letI := (latticeSet_finite hε hU).fintype
  rw [l2Norm_eq_euclidean hε, l2Norm_eq_euclidean hε, l2Norm_eq_euclidean hε,
    ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact norm_add_le (WithLp.toLp 2 (fun q : latticeSet ε U => g q))
    (WithLp.toLp 2 (fun q : latticeSet ε U => h q))

/-- A finite sum satisfies the discrete L² triangle inequality. -/
theorem l2Norm_finset_sum_le {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {ι : Type*} (s : Finset ι) (g : ι → Site d → ℝ) :
    l2Norm ε U (fun q => ∑ i ∈ s, g i q) ≤ ∑ i ∈ s, l2Norm ε U (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2Norm, l2NormSq]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (l2Norm_add_le hε hU _ _).trans (add_le_add_right ih _)

/-- Multiplication by a uniformly bounded coefficient is bounded on discrete L². -/
theorem l2Norm_mul_le {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {B : ℝ} (hB : 0 ≤ B) (c g : Site d → ℝ)
    (hc : ∀ q, |c q| ≤ B) :
    l2Norm ε U (fun q => c q * g q) ≤ B * l2Norm ε U g := by
  letI := (latticeSet_finite hε hU).fintype
  have hs : ∑ q : latticeSet ε U, (c q * g q) ^ 2 ≤
      B ^ 2 * ∑ q : latticeSet ε U, g q ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    rw [mul_pow]
    have hc2 : c q ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (c q)) hB).2 (hc q)
    exact mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
  unfold l2Norm l2NormSq
  rw [tsum_fintype, tsum_fintype]
  calc
    _ ≤ Real.sqrt (ε ^ d * (B ^ 2 * ∑ q : latticeSet ε U, g q ^ 2)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs (pow_nonneg hε.le d))
    _ = B * Real.sqrt (ε ^ d * ∑ q : latticeSet ε U, g q ^ 2) := by
      rw [← mul_assoc, mul_comm (ε ^ d), mul_assoc, Real.sqrt_mul (sq_nonneg B),
        Real.sqrt_sq hB]

/-- The two-scale correction is bounded by the derivative bound times corrector norms. -/
theorem l2Norm_approxSolution_sub_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {v : (Fin d → ℝ) → ℝ} {B₁ : ℝ} (hB₁ : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁)
    (φ : Fin d → Site d → ℝ) :
    l2Norm ε U (fun q => approxSolution ε U v φ q - v (physical ε q)) ≤
      B₁ * ∑ i, l2Norm ε U (φ i) := by
  have hB : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0)
  rw [l2Norm_congr (h := fun q => ∑ i, gradientCoeff ε v i q * φ i q) (by
    intro q hq
    have hmem : physical ε q ∈ U := hq
    simp only [approxSolution, zeroExtension, if_pos hmem, add_sub_cancel_left])]
  calc
    _ ≤ ∑ i, l2Norm ε U (fun q => gradientCoeff ε v i q * φ i q) :=
      l2Norm_finset_sum_le hε hU Finset.univ _
    _ ≤ ∑ i, B₁ * l2Norm ε U (φ i) := Finset.sum_le_sum (fun i _ =>
      l2Norm_mul_le hε hU hB _ _ (abs_gradientCoeff_le hB₁ i))
    _ = _ := (Finset.mul_sum _ _ _).symm

end

end LongRange
