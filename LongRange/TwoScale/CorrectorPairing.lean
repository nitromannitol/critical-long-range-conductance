import LongRange.TwoScale.ProductEstimate
import LongRange.TwoScale.ResidualDefs
import LongRange.Calculus.Green
import LongRange.Calculus.Commutator

/-!
# Dual estimate for the corrector error

The coefficient variation is the commutator of multiplication with the discrete energy.
The product estimate and energy Cauchy--Schwarz control its pairing with a supported test.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Coefficient variation paired with a test equals the energy commutator. -/
theorem pairing_coeff_variation_eq (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {b φ ψ : Site d → ℝ}
    (hφ : Function.HasFiniteSupport φ) (hψ : Function.HasFiniteSupport ψ) :
    ε ^ d * ∑' q, (ε ^ d / kappa d ε * ∑' w : Site d,
      if hw : w = 0 then 0 else a (edgeAdd q w hw) * jumpKernel (physical ε w) *
        (b (q + w) - b q) * φ (q + w)) * ψ q =
      bilinForm ε a φ (fun x => b x * ψ x) -
        bilinForm ε a (fun x => b x * φ x) ψ := by
  rw [bilinForm_mul_sub_mul hd hε hlam ha b hφ hψ]
  congr 1
  exact tsum_congr (fun q => mul_comm _ _)

/-- The critical seminorm is nonnegative at nonnegative scales. -/
private lemma crit_nonneg {ε : ℝ} (hε : 0 ≤ ε) (u : Site d → ℝ) :
    0 ≤ h1CritSq ε u := by
  exact mul_nonneg (div_nonneg (pow_nonneg hε _) (kappa_nonneg hε))
    (tsum_nonneg (fun _ => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))

/-- The local squared mass is nonnegative at nonnegative scales. -/
private lemma mass_nonneg {ε : ℝ} (hε : 0 ≤ ε) (U : Set (Fin d → ℝ))
    (u : Site d → ℝ) : 0 ≤ l2NormSq ε U u := by
  exact mul_nonneg (pow_nonneg hε _) (tsum_nonneg (fun _ => sq_nonneg _))

/-- Ellipticity and Cauchy--Schwarz bound the energy by critical seminorms. -/
private lemma abs_bilinForm_le_crit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {u w : Site d → ℝ}
    (hu : Function.HasFiniteSupport u) (hw : Function.HasFiniteSupport w) :
    |bilinForm ε a u w| ≤ lam⁻¹ * Real.sqrt (h1CritSq ε u) *
      Real.sqrt (h1CritSq ε w) := by
  have hi : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hb (f : Site d → ℝ) (hf : Function.HasFiniteSupport f) :
      Real.sqrt (bilinForm ε a f f) ≤
        Real.sqrt lam⁻¹ * Real.sqrt (h1CritSq ε f) := by
    apply (Real.sqrt_le_sqrt ((bilinForm_self_bounds hd hε hlam ha hf).2.trans
      (mul_le_mul_of_nonneg_right (by linarith : lam⁻¹ / 2 ≤ lam⁻¹)
        (crit_nonneg hε.le f)))).trans_eq
    exact Real.sqrt_mul hi _
  calc
    _ ≤ Real.sqrt (bilinForm ε a u u) * Real.sqrt (bilinForm ε a w w) :=
      abs_bilinForm_le hd hε hlam ha hu hw
    _ ≤ (Real.sqrt lam⁻¹ * Real.sqrt (h1CritSq ε u)) *
        (Real.sqrt lam⁻¹ * Real.sqrt (h1CritSq ε w)) :=
      mul_le_mul (hb u hu) (hb w hw) (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = (Real.sqrt lam⁻¹ * Real.sqrt lam⁻¹) *
        (Real.sqrt (h1CritSq ε u) * Real.sqrt (h1CritSq ε w)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hi]; ring

/-- Summing the coefficient variations gives the exact dual corrector error. -/
private lemma correctorError_pairing_eq (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (v : (Fin d → ℝ) → ℝ)
    (φ : Fin d → Site d → ℝ) (ψ : Site d → ℝ)
    (hφ : ∀ i, Function.HasFiniteSupport (φ i))
    (hψ : Function.HasFiniteSupport ψ) :
    ε ^ d * ∑' q, correctorError ε a v φ q * ψ q =
      ∑ i, (bilinForm ε a (φ i) (fun x => gradientCoeff ε v i x * ψ x) -
        bilinForm ε a (fun x => gradientCoeff ε v i x * φ i x) ψ) := by
  classical
  let c := fun (i : Fin d) (q : Site d) => ε ^ d / kappa d ε *
    ∑' w : Site d, if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * jumpKernel (physical ε w) *
        (gradientCoeff ε v i (q + w) - gradientCoeff ε v i q) * φ i (q + w)
  have hc (q : Site d) : correctorError ε a v φ q = ∑ i, c i q := by
    dsimp only [c]
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ =>
      summable_generator_product_correction ε a (gradientCoeff ε v i) (hφ i) q)]
    unfold correctorError
    congr 1
    apply tsum_congr
    intro w
    by_cases hw : w = 0
    · simp only [hw, ↓reduceDIte, Finset.sum_const_zero]
    · simp only [hw, ↓reduceDIte, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hc, Finset.sum_mul]
  have hcs (i : Fin d) : Summable (fun q => c i q * ψ q) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right (c i) hψ)
  rw [Summable.tsum_finsetSum (fun i _ => hcs i), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    pairing_coeff_variation_eq hd hε hlam ha (hφ i) hψ)

/-- The corrector error has a uniform dual bound controlled by the product estimate. -/
theorem correctorError_pairing_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ U : Set (Fin d → ℝ),
      Bornology.IsBounded U → ∀ lam : ℝ, 0 < lam → ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (v : (Fin d → ℝ) → ℝ) (B : ℝ), 0 ≤ B →
      (∀ i q, |gradientCoeff ε v i q| ≤ B) →
      (∀ i q w, |gradientCoeff ε v i (q + w) - gradientCoeff ε v i q| ≤
        B * min (radius (physical ε w)) 1) →
      ∀ φ : Fin d → Site d → ℝ, (∀ i, SupportedIn ε U (φ i)) →
      ∀ ψ : Site d → ℝ, SupportedIn ε U ψ →
        |ε ^ d * ∑' q, correctorError ε a v φ q * ψ q| ≤
          C * lam⁻¹ * B * (∑ i, Real.sqrt (h1CritSq ε (φ i) + l2NormSq ε U (φ i))) *
            Real.sqrt (h1CritSq ε ψ + l2NormSq ε U ψ) := by
  classical
  obtain ⟨K, hK, hprod⟩ := h1CritSq_mul_le hd
  refine ⟨2 * Real.sqrt K, mul_pos (by norm_num) (Real.sqrt_pos.mpr hK), ?_⟩
  intro ε hε U hU lam hlam a ha v B hB hb hinc φ hφ ψ hψ
  have hfin (i) := (hφ i).hasFiniteSupport hε.1 hU
  have hψfin := hψ.hasFiniteSupport hε.1 hU
  have hi : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hs (f : Site d → ℝ) :
      Real.sqrt (h1CritSq ε f) ≤ Real.sqrt (h1CritSq ε f + l2NormSq ε U f) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (mass_nonneg hε.1.le U f))
  have hm (i : Fin d) (f : Site d → ℝ) (hf : SupportedIn ε U f) :
      Real.sqrt (h1CritSq ε (fun x => gradientCoeff ε v i x * f x)) ≤
        Real.sqrt K * B * Real.sqrt (h1CritSq ε f + l2NormSq ε U f) := by
    have hh := Real.sqrt_le_sqrt (hprod ε hε U hU (gradientCoeff ε v i) f B hB
      (hb i) (hinc i) hf)
    rw [Real.sqrt_mul (mul_nonneg hK.le (sq_nonneg B)),
      Real.sqrt_mul hK.le, Real.sqrt_sq hB] at hh
    exact hh
  have hterm (i : Fin d) :
      |bilinForm ε a (φ i) (fun x => gradientCoeff ε v i x * ψ x) -
        bilinForm ε a (fun x => gradientCoeff ε v i x * φ i x) ψ| ≤
      (2 * Real.sqrt K) * lam⁻¹ * B *
        Real.sqrt (h1CritSq ε (φ i) + l2NormSq ε U (φ i)) *
          Real.sqrt (h1CritSq ε ψ + l2NormSq ε U ψ) := by
    have hfψ : Function.HasFiniteSupport (fun x => gradientCoeff ε v i x * ψ x) :=
      Function.HasFiniteSupport.mul_right _ hψfin
    have hfφ : Function.HasFiniteSupport (fun x => gradientCoeff ε v i x * φ i x) :=
      Function.HasFiniteSupport.mul_right _ (hfin i)
    have hleft := abs_bilinForm_le_crit hd hε.1 hlam ha (hfin i) hfψ
    have hright := abs_bilinForm_le_crit hd hε.1 hlam ha hfφ hψfin
    have hl := mul_le_mul (mul_le_mul_of_nonneg_left (hs (φ i)) hi)
      (hm i ψ hψ) (Real.sqrt_nonneg _)
      (mul_nonneg hi (Real.sqrt_nonneg _))
    have hr := mul_le_mul (mul_le_mul_of_nonneg_left (hm i (φ i) (hφ i)) hi)
      (hs ψ) (Real.sqrt_nonneg _)
      (mul_nonneg hi (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
        (Real.sqrt_nonneg _)))
    calc
      _ ≤ |bilinForm ε a (φ i) (fun x => gradientCoeff ε v i x * ψ x)| +
          |bilinForm ε a (fun x => gradientCoeff ε v i x * φ i x) ψ| :=
        abs_sub _ _
      _ ≤ _ := (add_le_add (hleft.trans hl) (hright.trans hr)).trans_eq (by ring)
  rw [correctorError_pairing_eq hd hε.1 hlam ha v φ ψ hfin hψfin]
  calc
    _ ≤ ∑ i, |bilinForm ε a (φ i) (fun x => gradientCoeff ε v i x * ψ x) -
        bilinForm ε a (fun x => gradientCoeff ε v i x * φ i x) ψ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (2 * Real.sqrt K) * lam⁻¹ * B *
        Real.sqrt (h1CritSq ε (φ i) + l2NormSq ε U (φ i)) *
          Real.sqrt (h1CritSq ε ψ + l2NormSq ε U ψ) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

end
end LongRange
