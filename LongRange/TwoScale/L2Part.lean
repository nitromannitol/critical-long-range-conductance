import LongRange.TwoScale.SmoothSplit
import LongRange.TwoScale.SmoothError
import LongRange.TwoScale.Approximate

/-!
# The bounded part of the residual

The deterministic smooth defect and the corrector term admit discrete L² bounds.
The conductance fluctuation enters through its given L² estimate.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- A pointwise bound controls the squared norm by the physical lattice volume. -/
lemma l2NormSq_le_count {ε M : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hM : 0 ≤ M) (g : Site d → ℝ)
    (hg : ∀ q ∈ latticeSet ε U, |g q| ≤ M) :
    l2NormSq ε U g ≤ ε ^ d * (latticeSet ε U).ncard * M ^ 2 := by
  classical
  letI := (latticeSet_finite hε hU).fintype
  unfold l2NormSq
  rw [tsum_fintype, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε.le d)
  calc
    _ ≤ ∑ _q : latticeSet ε U, M ^ 2 := Finset.sum_le_sum (fun q _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).2 (hg q q.property))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Set.fintypeCard_eq_ncard,
        nsmul_eq_mul]

/-- A diameter bound turns a uniform pointwise bound into a uniform L² bound. -/
lemma l2Norm_le_of_count {ε M V : ℝ} (hε : 0 < ε) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hM : 0 ≤ M)
    (hV : ε ^ d * (latticeSet ε U).ncard ≤ V) (g : Site d → ℝ)
    (hg : ∀ q ∈ latticeSet ε U, |g q| ≤ M) :
    l2Norm ε U g ≤ M * Real.sqrt V := by
  calc
    _ ≤ Real.sqrt (V * M ^ 2) := Real.sqrt_le_sqrt
      ((l2NormSq_le_count hε hU hM g hg).trans
        (mul_le_mul_of_nonneg_right hV (sq_nonneg M)))
    _ = _ := by rw [mul_comm V, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

/-- The smooth residual minus the mass corrector has a uniform discrete L² bound. -/
theorem l2Part_bound (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (lam R B : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Fin d → ℝ)), IsOpen U →
      ∀ _hU : Bornology.IsBounded U, euclideanDiam U ≤ R →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (μ m₀ : ℝ), 0 ≤ μ → μ ≤ B →
      m₀ ∈ Set.Icc lam lam⁻¹ → ∀ (f v ū : (Fin d → ℝ) → ℝ),
      ContDiff ℝ 2 v → (∀ x, |v x| ≤ B) →
      (∀ x, ‖fderiv ℝ v x‖ ≤ B) → (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) → Set.EqOn v ū U →
      (∀ x ∈ U, μ * ū x - m₀ / (2 * d) * Elliptic.laplacian ū x = f x) →
      ∀ (φ : Fin d → Site d → ℝ) (K F : ℝ),
      (∀ i, l2NormSq ε U (φ i) ≤ K) →
      l2Norm ε U (smoothFluctuation ε a m₀ v) ≤ F →
      l2Norm ε U (fun q => smoothError ε a μ f v q -
        μ * ∑ i, gradientCoeff ε v i q * φ i q) ≤
          C * (1 / kappa d ε + F + Real.sqrt K) := by
  classical
  obtain ⟨V, hV, hcount⟩ := ncard_latticeSet_le d R
  obtain ⟨D, hD, hdef⟩ := smooth_error_bound d hd hσ hσ1
  let A := lam⁻¹ * D * (4 * |B|) * Real.sqrt V
  let T := (d : ℝ) * B ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨A + 1 + T, by positivity, ?_⟩
  intro U hUo hU hdiam ε hε a ha μ m₀ hμ hμB hm f v ū hv hv0 hv1 hv2 hvH heq hpde
    φ K F hφ hF
  have hB : 0 ≤ B := hμ.trans hμB
  have hk := kappa_pos hd hε
  have hvol : ε ^ d * (latticeSet ε U).ncard ≤ V := by
    have hc := mul_le_mul_of_nonneg_left (hcount U hU hdiam ε hε)
      (pow_nonneg hε.1.le d)
    have hid : ε ^ d * (V * ε ^ (-(d : ℝ))) = V := by
      rw [Real.rpow_neg hε.1.le, Real.rpow_natCast]
      field_simp [ne_of_gt hε.1]
    exact hc.trans_eq hid
  let g := fun q : Site d => m₀ * (ε ^ d / kappa d ε *
    ∑' w : Site d, jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w) -
        Elliptic.laplacian v (physical ε q) / (2 * d))
  have hg : l2Norm ε U g ≤ A / kappa d ε := by
    have hb : 0 ≤ lam⁻¹ * (D * (4 * B) / kappa d ε) := by positivity
    have h := l2Norm_le_of_count hε.1 hU hb hvol g (by
      intro q _
      dsimp only [g]
      rw [abs_mul, abs_of_nonneg (hlam.le.trans hm.1)]
      have hdq := (hdef v B B B B hv hv0 hv1 hv2 hvH ε hε q).2
      have hsum : B + B + B + B = 4 * B := by ring
      rw [hsum] at hdq
      exact mul_le_mul hm.2 hdq (abs_nonneg _) (inv_nonneg.mpr hlam.le))
    apply h.trans_eq
    dsimp only [A]
    rw [abs_of_nonneg hB]
    ring
  have hcorr : l2Norm ε U (fun q =>
      -μ * ∑ i, gradientCoeff ε v i q * φ i q) ≤ T * Real.sqrt K := by
    have hs : l2Norm ε U (fun q => ∑ i, gradientCoeff ε v i q * φ i q) ≤
        (d : ℝ) * (B * Real.sqrt K) := by
      calc
        _ ≤ ∑ i, l2Norm ε U (fun q => gradientCoeff ε v i q * φ i q) :=
          l2Norm_finset_sum_le hε.1 hU Finset.univ _
        _ ≤ ∑ _i : Fin d, B * Real.sqrt K := Finset.sum_le_sum (fun i _ =>
          (l2Norm_mul_le hε.1 hU hB _ _ (abs_gradientCoeff_le hv1 i)).trans
            (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hφ i)) hB))
        _ = _ := by simp
    have h := (l2Norm_mul_le hε.1 hU hμ (fun _ => -μ) _ (by
      intro q; simp only [abs_neg, abs_of_nonneg hμ, le_refl])).trans
        (mul_le_mul_of_nonneg_left hs hμ)
    apply h.trans
    dsimp only [T]
    calc
      _ ≤ B * ((d : ℝ) * (B * Real.sqrt K)) :=
        mul_le_mul_of_nonneg_right hμB (by positivity)
      _ = _ := by ring
  rw [l2Norm_congr (h := fun q =>
    (g q + smoothFluctuation ε a m₀ v q) +
      (-μ * ∑ i, gradientCoeff ε v i q * φ i q)) (by
        intro q hq
        rw [smoothError_eq_split hd hε.1 hlam ha hUo μ m₀ heq hpde hv0 hv1 hq]
        dsimp only [g]
        ring)]
  have htotal := (l2Norm_add_le hε.1 hU _ _).trans
    (add_le_add ((l2Norm_add_le hε.1 hU _ _).trans (add_le_add hg hF)) hcorr)
  have hF0 : 0 ≤ F := (Real.sqrt_nonneg _).trans hF
  apply htotal.trans
  have hki : 0 ≤ 1 / kappa d ε := by positivity
  have hK := Real.sqrt_nonneg K
  rw [div_eq_mul_one_div A]
  nlinarith only [mul_nonneg hA hF0, mul_nonneg hA hK,
    mul_nonneg hT hki, mul_nonneg hT hF0, hki, hK]

end
end LongRange
