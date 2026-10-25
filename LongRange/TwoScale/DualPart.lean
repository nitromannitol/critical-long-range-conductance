import LongRange.TwoScale.CorrectorPairing
import LongRange.TwoScale.BoundaryDefect
import LongRange.Continuum.BoundaryLipschitz
import LongRange.Poincare.Inequality
import LatticeProb.Analysis.TaylorHolder

/-!
# Dual estimate for the boundary and corrector errors

The boundary estimate and coefficient variation estimate combine after applying
Poincaré to the test function. All displacement bounds use the Euclidean radius.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The combined boundary and corrector residual is bounded in the critical dual norm. -/
theorem dualPart_bound (hd : 1 ≤ d) (lam R B : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Fin d → ℝ)), IsOpen U → Bornology.IsBounded U →
      U.Nonempty → euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v →
      (∀ x, ‖fderiv ℝ v x‖ ≤ B) → (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x, R < radius x → v x = 0) → (∀ x ∈ frontier U, v x = 0) →
      ∀ (φ : Fin d → Site d → ℝ) (K : ℝ), (∀ i, SupportedIn ε U (φ i)) →
      (∀ i, h1CritSq ε (φ i) + l2NormSq ε U (φ i) ≤ K) →
      ∀ ψ : Site d → ℝ, SupportedIn ε U ψ →
        |ε ^ d * ∑' q, (boundaryDefect ε a (exteriorDefect ε U v) q +
            correctorError ε a v φ q) * ψ q| ≤
          C * (1 / Real.sqrt (kappa d ε) + Real.sqrt K) *
            Real.sqrt (h1CritSq ε ψ) := by
  classical
  obtain ⟨Cb, hCb, hb⟩ := boundary_defect_bound d R
  obtain ⟨Ce, hCe, he⟩ := correctorError_pairing_le hd
  obtain ⟨Cp, hCp, hp⟩ := poincare d hd R
  let A := lam⁻¹ * Real.sqrt Cb * |B|
  let D := Ce * lam⁻¹ * (2 * |B|) * d * Real.sqrt (1 + Cp)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨A + D + 1, by positivity, ?_⟩
  intro U hUo hU hne hdiam ε hε a ha v hv hDv hD₂v hR h0 φ K hφ hK ψ hψ
  have hB : 0 ≤ B := (norm_nonneg _).trans (hDv 0)
  have henergy : 0 ≤ h1CritSq ε ψ :=
    mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) (kappa_nonneg hε.1.le))
      (tsum_nonneg (fun _ => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))
  have hbound := hb ε hε lam hlam U hU a ha (exteriorDefect ε U v) B hd
    (exteriorDefect_eq_zero_on_latticeSet ε U v)
    (by
      intro y hy
      simp only [exteriorDefect, zeroExtension, hR _ hy]
      split <;> simp)
    (exteriorDefect_le_boundaryDistance hne
      (hv.of_le (by norm_num)) hDv h0) ψ hψ
  have hsub : (∑' q : latticeSet ε U,
      boundaryDefect ε a (exteriorDefect ε U v) q * ψ q) =
      ∑' q, boundaryDefect ε a (exteriorDefect ε U v) q * ψ q := by
    apply tsum_subtype_eq_of_support_subset
      (f := fun q => boundaryDefect ε a (exteriorDefect ε U v) q * ψ q)
    intro q hq
    by_contra hn
    exact hq (by simp only [hψ q hn, mul_zero])
  rw [hsub] at hbound
  have hbfinal : |ε ^ d * ∑' q,
      boundaryDefect ε a (exteriorDefect ε U v) q * ψ q| ≤
      A * (1 / Real.sqrt (kappa d ε)) * Real.sqrt (h1CritSq ε ψ) := by
    have hs : Real.sqrt (Cb * B ^ 2 / kappa d ε) =
        Real.sqrt Cb * |B| / Real.sqrt (kappa d ε) := by
      rw [Real.sqrt_div (mul_nonneg hCb.le (sq_nonneg B)),
        Real.sqrt_mul hCb.le, Real.sqrt_sq_eq_abs]
    rw [hs] at hbound
    simpa only [A, div_eq_mul_inv, one_mul, mul_assoc] using hbound
  have hgrad (i : Fin d) (q : Site d) : |gradientCoeff ε v i q| ≤ 2 * B := by
    have h := (fderiv ℝ v (physical ε q)).le_opNorm (Pi.single i 1)
    have hh : |gradientCoeff ε v i q| ≤ B := by
      have heval : |gradientCoeff ε v i q| ≤ ‖fderiv ℝ v (physical ε q)‖ := by
        simpa only [gradientCoeff, Elliptic.partialDeriv, Pi.norm_single,
          norm_one, mul_one, Real.norm_eq_abs] using h
      exact heval.trans (hDv _)
    linarith
  have hinc (i : Fin d) (q w : Site d) :
      |gradientCoeff ε v i (q + w) - gradientCoeff ε v i q| ≤
        (2 * B) * min (radius (physical ε w)) 1 := by
    have h := TaylorHolder.partial_sub_le_min hv hDv hD₂v
      (physical ε q) (physical ε w) i
    have hadd : physical ε (q + w) = physical ε q + physical ε w := by
      ext j
      simp only [physical, Pi.add_apply, Int.cast_add, mul_add]
    change |fderiv ℝ v (physical ε (q + w)) (Pi.single i 1) -
      fderiv ℝ v (physical ε q) (Pi.single i 1)| ≤ _
    rw [hadd]
    refine h.trans ?_
    by_cases hr : radius (physical ε w) ≤ 1
    · rw [min_eq_left hr]
      exact (min_le_left _ _).trans (by nlinarith [radius_nonneg (physical ε w)])
    · rw [min_eq_right (le_of_not_ge hr), mul_one]
      exact min_le_right _ _
  have he' := he ε hε U hU lam hlam a ha v (2 * B) (by positivity)
    hgrad hinc φ hφ ψ hψ
  have hsum : (∑ i, Real.sqrt (h1CritSq ε (φ i) + l2NormSq ε U (φ i))) ≤
      d * Real.sqrt K := by
    calc
      _ ≤ ∑ _i : Fin d, Real.sqrt K := Finset.sum_le_sum (fun i _ =>
        Real.sqrt_le_sqrt (hK i))
      _ = _ := by simp
  have htest : Real.sqrt (h1CritSq ε ψ + l2NormSq ε U ψ) ≤
      Real.sqrt (1 + Cp) * Real.sqrt (h1CritSq ε ψ) := by
    calc
      _ ≤ Real.sqrt ((1 + Cp) * h1CritSq ε ψ) :=
        Real.sqrt_le_sqrt (by nlinarith [hp U hUo hU hdiam ε hε ψ hψ])
      _ = _ := Real.sqrt_mul (by positivity) _
  have hefinal : |ε ^ d * ∑' q, correctorError ε a v φ q * ψ q| ≤
      D * Real.sqrt K * Real.sqrt (h1CritSq ε ψ) := by
    calc
      _ ≤ Ce * lam⁻¹ * (2 * B) * (d * Real.sqrt K) *
          (Real.sqrt (1 + Cp) * Real.sqrt (h1CritSq ε ψ)) :=
        he'.trans (mul_le_mul
          (mul_le_mul_of_nonneg_left hsum (by positivity)) htest
          (Real.sqrt_nonneg _) (by positivity))
      _ = _ := by dsimp [D]; rw [abs_of_nonneg hB]; ring
  have hf := hψ.hasFiniteSupport hε.1 hU
  have hs₁ : Summable (fun q => boundaryDefect ε a (exteriorDefect ε U v) q * ψ q) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right _ hf)
  have hs₂ : Summable (fun q => correctorError ε a v φ q * ψ q) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right _ hf)
  simp_rw [add_mul]
  rw [hs₁.tsum_add hs₂, mul_add]
  calc
    _ ≤ |ε ^ d * ∑' q, boundaryDefect ε a (exteriorDefect ε U v) q * ψ q| +
        |ε ^ d * ∑' q, correctorError ε a v φ q * ψ q| := abs_add_le _ _
    _ ≤ A * (1 / Real.sqrt (kappa d ε)) * Real.sqrt (h1CritSq ε ψ) +
        D * Real.sqrt K * Real.sqrt (h1CritSq ε ψ) := add_le_add hbfinal hefinal
    _ ≤ _ := by
      have hk : 0 ≤ 1 / Real.sqrt (kappa d ε) := by positivity
      have hs := Real.sqrt_nonneg K
      have hcoeff : A * (1 / Real.sqrt (kappa d ε)) + D * Real.sqrt K ≤
          (A + D + 1) * (1 / Real.sqrt (kappa d ε) + Real.sqrt K) := by
        nlinarith
      simpa only [add_mul] using
        mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg (h1CritSq ε ψ))

end

end LongRange
