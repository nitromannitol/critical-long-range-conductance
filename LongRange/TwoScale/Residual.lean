import LongRange.TwoScale.ResidualTaylor
import LongRange.TwoScale.Approximate
import LongRange.Calculus.Linearity
import LongRange.Calculus.Generator

/-!
# Residual decomposition of the two-scale expansion

The discrete product rule and the corrector equation cancel the linear Taylor terms.
Absolute convergence separates the remaining smooth, boundary, and corrector errors.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Bounded smooth data and bounded derivatives make the weighted Taylor series summable. -/
theorem summable_residual_smooth (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {v : (Fin d → ℝ) → ℝ} {B₀ B₁ : ℝ} (hB₀ : ∀ x, |v x| ≤ B₀)
    (hB₁ : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * jumpKernel (physical ε w) *
        smoothRemainder v (physical ε q) (physical ε w)) := by
  let S := fun w : Site d => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)
  classical
  change Summable S
  have hB0 : 0 ≤ B₀ := (abs_nonneg _).trans (hB₀ 0)
  have hB1 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0)
  refine ((summable_jumpKernel_weight hd hε).mul_left
    (lam⁻¹ * (2 * B₀ + B₁))).of_norm_bounded ?_
  intro w
  have hJ := jumpKernel_nonneg (physical ε w)
  have hr := radius_nonneg (physical ε w)
  by_cases hw : w = 0
  · simp only [S, hw, ↓reduceDIte, norm_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le)
      (add_nonneg (mul_nonneg (by norm_num) hB0) hB1))
      (mul_nonneg (jumpKernel_nonneg _) (add_nonneg zero_le_one (radius_nonneg _)))
  · simp only [S, hw, ↓reduceDIte, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg hJ]
    have hrem := TaylorHolder.remainder_le_linear hB₀ hB₁
      (physical ε q) (physical ε w)
    have hb : |smoothRemainder v (physical ε q) (physical ε w)| ≤
        (2 * B₀ + B₁) * (1 + radius (physical ε w)) := by
      exact hrem.trans (by nlinarith [mul_nonneg hB0 hr])
    calc
      _ ≤ lam⁻¹ * jumpKernel (physical ε w) *
          ((2 * B₀ + B₁) * (1 + radius (physical ε w))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (ha _).2 hJ) hb
          (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr hlam.le) hJ)
      _ = _ := by ring

/-- Bounded smooth data make the exterior-defect series absolutely summable. -/
theorem summable_residual_boundary (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (U : Set (Fin d → ℝ)) {v : (Fin d → ℝ) → ℝ} {B₀ : ℝ}
    (hB₀ : ∀ x, |v x| ≤ B₀) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * jumpKernel (physical ε w) * exteriorDefect ε U v (q + w)) := by
  classical
  let T := fun w : Site d => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) * exteriorDefect ε U v (q + w)
  change Summable T
  have hB0 : 0 ≤ B₀ := (abs_nonneg _).trans (hB₀ 0)
  refine ((summable_jumpKernel hd hε).mul_left (lam⁻¹ * (2 * B₀))).of_norm_bounded ?_
  intro w
  have hJ := jumpKernel_nonneg (physical ε w)
  by_cases hw : w = 0
  · simp only [T, hw, ↓reduceDIte, norm_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le)
      (mul_nonneg (by norm_num) hB0)) (jumpKernel_nonneg _)
  · have hz : |zeroExtension ε U v (q + w)| ≤ B₀ := by
      unfold zeroExtension
      split_ifs
      · exact hB₀ _
      · simpa only [abs_zero] using hB0
    have hb : |exteriorDefect ε U v (q + w)| ≤ 2 * B₀ :=
      (abs_sub _ _).trans ((add_le_add (hB₀ _) hz).trans_eq (by ring))
    simp only [T, hw, ↓reduceDIte, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg hJ]
    calc
      _ ≤ lam⁻¹ * jumpKernel (physical ε w) * (2 * B₀) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (ha _).2 hJ) hb
          (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr hlam.le) hJ)
      _ = _ := by ring

/-- Summing the product rules gives the corrector error and the linear forcing. -/
theorem generator_corrector_sum (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (v : (Fin d → ℝ) → ℝ) (φ : Fin d → Site d → ℝ)
    (hφ : ∀ i, IsCorrectorSolution ε U a (Pi.single i 1) (φ i))
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    (∑ i, generator ε a (fun x => gradientCoeff ε v i x * φ i x) q) =
      -(∑ i, gradientCoeff ε v i q *
        generator ε a (linearFn ε (Pi.single i 1)) q) + correctorError ε a v φ q := by
  classical
  let C := fun (i : Fin d) (w : Site d) => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) *
      (gradientCoeff ε v i (q + w) - gradientCoeff ε v i q) * φ i (q + w)
  have hC (i : Fin d) : Summable (C i) :=
    summable_generator_product_correction ε a (gradientCoeff ε v i)
      ((hφ i).1.hasFiniteSupport hε hU) q
  have hmul (i : Fin d) :
      generator ε a (fun x => gradientCoeff ε v i x * φ i x) q =
        -(gradientCoeff ε v i q * generator ε a (linearFn ε (Pi.single i 1)) q) +
          ε ^ d / kappa d ε * ∑' w, C i w := by
    rw [generator_mul hd hε hlam ha _ ((hφ i).1.hasFiniteSupport hε hU),
      (hφ i).generator_eq_neg hd hε hU hlam ha hq, mul_neg]
  have hcor : (∑ i, ε ^ d / kappa d ε * ∑' w, C i w) =
      correctorError ε a v φ q := by
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hC i)]
    unfold correctorError
    congr 1
    apply tsum_congr
    intro w
    by_cases hw : w = 0
    · simp only [C, hw, ↓reduceDIte, Finset.sum_const_zero]
    · simp only [C, hw, ↓reduceDIte, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  simp_rw [hmul]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hcor]

/-- Product expansion and the corrector equations identify the approximate generator. -/
theorem generator_approxSolution (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (v : (Fin d → ℝ) → ℝ) (φ : Fin d → Site d → ℝ)
    (hφ : ∀ i, IsCorrectorSolution ε U a (Pi.single i 1) (φ i))
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    generator ε a (approxSolution ε U v φ) q =
      generator ε a (zeroExtension ε U v) q -
        (∑ i, gradientCoeff ε v i q *
          generator ε a (linearFn ε (Pi.single i 1)) q) + correctorError ε a v φ q := by
  classical
  have hzero : SupportedIn ε U (zeroExtension ε U v) := by
    intro x hx
    exact if_neg hx
  have hprod (i : Fin d) : SupportedIn ε U (fun x => gradientCoeff ε v i x * φ i x) := by
    intro x hx
    change gradientCoeff ε v i x * φ i x = 0
    rw [(hφ i).1 x hx, mul_zero]
  have hsum : SupportedIn ε U (fun x => ∑ i, gradientCoeff ε v i x * φ i x) := by
    intro x hx
    exact Finset.sum_eq_zero (fun i _ => hprod i x hx)
  have hbounded := fun (g : Site d → ℝ) (hg : SupportedIn ε U g) =>
    summable_generator_bounded hd hε hlam ha
      (exists_bound_of_finite_support (hg.hasFiniteSupport hε hU)) q
  have hadd := generator_add ε a q (hbounded _ hzero) (hbounded _ hsum)
  have hterms (i : Fin d) : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) *
        (gradientCoeff ε v i (q + w) * φ i (q + w) - gradientCoeff ε v i q * φ i q) *
          jumpKernel (physical ε w)) :=
    hbounded (fun x => gradientCoeff ε v i x * φ i x) (hprod i)
  have hfinite : generator ε a (fun x => ∑ i, gradientCoeff ε v i x * φ i x) q =
      ∑ i, generator ε a (fun x => gradientCoeff ε v i x * φ i x) q :=
    generator_finset_sum ε a (Finset.univ : Finset (Fin d))
      (fun i x => gradientCoeff ε v i x * φ i x) q (fun i _ => hterms i)
  have happgen : generator ε a (approxSolution ε U v φ) q =
      generator ε a (zeroExtension ε U v) q +
        ∑ i, generator ε a (fun x => gradientCoeff ε v i x * φ i x) q :=
    hadd.trans (congrArg (fun t => generator ε a (zeroExtension ε U v) q + t) hfinite)
  have hproducts := generator_corrector_sum hd hε hU hlam ha v φ hφ hq
  calc
    _ = generator ε a (zeroExtension ε U v) q +
        ∑ i, generator ε a (fun x => gradientCoeff ε v i x * φ i x) q := happgen
    _ = generator ε a (zeroExtension ε U v) q +
        (-(∑ i, gradientCoeff ε v i q *
          generator ε a (linearFn ε (Pi.single i 1)) q) + correctorError ε a v φ q) :=
      congrArg (fun t => generator ε a (zeroExtension ε U v) q + t) hproducts
    _ = _ := (add_assoc _ _ _).symm

/-- The residual of the two-scale approximation splits into the smooth, boundary, and
corrector errors, with the corrector contribution to the mass term retained explicitly. -/
theorem residual_identity (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (μ : ℝ)
    (f v : (Fin d → ℝ) → ℝ) {B₀ B₁ : ℝ}
    (hB₀ : ∀ x, |v x| ≤ B₀) (hB₁ : ∀ x, ‖fderiv ℝ v x‖ ≤ B₁)
    (φ : Fin d → Site d → ℝ) (hφ : ∀ i, IsCorrectorSolution ε U a (Pi.single i 1) (φ i))
    {u : Site d → ℝ} (hu : SupportedIn ε U u)
    (heq : ∀ q ∈ latticeSet ε U, μ * u q - generator ε a u q = f (physical ε q))
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    μ * (u q - approxSolution ε U v φ q) -
        generator ε a (fun x => u x - approxSolution ε U v φ x) q =
      smoothError ε a μ f v q + boundaryDefect ε a (exteriorDefect ε U v) q +
        correctorError ε a v φ q - μ * ∑ i, gradientCoeff ε v i q * φ i q := by
  classical
  have hbounded := fun (g : Site d → ℝ) (hg : SupportedIn ε U g) =>
    summable_generator_bounded hd hε hlam ha
      (exists_bound_of_finite_support (hg.hasFiniteSupport hε hU)) q
  have happ := approxSolution_supportedIn (v := v) (fun i => (hφ i).1)
  have hsub := generator_sub ε a q (hbounded u hu) (hbounded _ happ)
  have happgen := generator_approxSolution hd hε hU hlam ha v φ hφ hq
  let S := fun w : Site d => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)
  let T := fun w : Site d => if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) * exteriorDefect ε U v (q + w)
  have hS : Summable S := summable_residual_smooth hd hε hlam ha hB₀ hB₁ q
  have hT : Summable T := summable_residual_boundary hd hε hlam ha U hB₀ q
  have htaylor := generator_zeroExtension_sub_gradient hd hε hlam ha hB₀ hB₁ hq
  have hsplit : generator ε a (zeroExtension ε U v) q -
      ∑ i, gradientCoeff ε v i q * generator ε a (linearFn ε (Pi.single i 1)) q =
        ε ^ d / kappa d ε * ∑' w, S w +
          boundaryDefect ε a (exteriorDefect ε U v) q := by
    rw [htaylor]
    have he : (fun w : Site d => if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * jumpKernel (physical ε w) *
          (smoothRemainder v (physical ε q) (physical ε w) -
            exteriorDefect ε U v (q + w))) = (fun w => S w - T w) := by
      funext w
      by_cases hw : w = 0 <;> simp only [S, T, hw, ↓reduceDIte] <;> ring
    rw [he, hS.tsum_sub hT]
    change _ = _ + -(ε ^ d / kappa d ε) * ∑' w, T w
    ring
  have hinterior : zeroExtension ε U v q = v (physical ε q) :=
    if_pos (mem_latticeSet.mp hq)
  rw [hsub, happgen]
  have hequ := heq q hq
  change μ * (u q - (zeroExtension ε U v q +
      ∑ i, gradientCoeff ε v i q * φ i q)) - _ =
    (f (physical ε q) - μ * v (physical ε q) +
      ε ^ d / kappa d ε * ∑' w, S w) + _ + _ - _
  rw [hinterior]
  linarith only [hsplit, hequ]

end

end LongRange
