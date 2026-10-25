import LongRange.TwoScale.Closing
import LongRange.TwoScale.Blocks
import LongRange.Corrector.Definition

/-!
# The deterministic estimate on one logarithmic block

Corrector and fluctuation control on a block give the solution error at the inverse
square root of the block index. The comparison uses the Euclidean normalization.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice TwoScale

noncomputable section

variable {d : ℕ}

/-- Corrector and fluctuation bounds on one block imply the homogenization estimate,
with a constant independent of the block and both control parameters. -/
theorem block_estimate (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (lam R B : ℝ)
    (hlam : 0 < lam) {U : Set (Fin d → ℝ)} (hUo : IsOpen U) (hU : Bornology.IsBounded U)
    (hne : U.Nonempty) (hR : euclideanDiam U ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Kc Kf : ℝ), 0 ≤ Kc → 0 ≤ Kf → ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (μ m₀ : ℝ), 0 ≤ μ → μ ≤ B →
      m₀ ∈ Set.Icc lam lam⁻¹ →
      ∀ (f v ū : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) →
      (∀ x, R < radius x → v x = 0) → (∀ x ∈ frontier U, v x = 0) → Set.EqOn v ū U →
      (∀ x ∈ U, μ * ū x - m₀ / (2 * d) * LatticeProb.Elliptic.laplacian ū x = f x) →
      ∀ m : ℕ, 1 ≤ m →
      (∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1), blockIndex U ε hε.1 = m →
        ∀ (i : Fin d) (φ : Site d → ℝ), IsCorrectorSolution ε U a (Pi.single i 1) φ →
          h1CritSq ε φ + l2NormSq ε U φ ≤ Kc / m) →
      (∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1), blockIndex U ε hε.1 = m →
        l2Norm ε U (smoothFluctuation ε a m₀ v) ≤ Kf / Real.sqrt m) →
      ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1), blockIndex U ε hε.1 = m →
      ∀ u : Site d → ℝ, SupportedIn ε U u →
      (∀ q ∈ latticeSet ε U, μ * u q - generator ε a u q = f (physical ε q)) →
        l2Norm ε U (fun q => u q - ū (physical ε q)) ≤
          C * (1 + Real.sqrt Kc + Kf) / Real.sqrt m := by
  classical
  obtain ⟨C₈, hC₈, hestimate⟩ := two_scale_estimate hd hσ hσ1 lam R B hlam
  obtain ⟨c, Cb, hc, _hCb, hcompare⟩ := kappa_comparable hd hU hUo hne
  refine ⟨C₈ * (1 / Real.sqrt c + 1), mul_pos hC₈ (by positivity), ?_⟩
  intro Kc Kf hKc hKf a ha μ m₀ hμ hμB hm₀ f v ū hv hvB hv₁ hv₂ hvσ
    hvR hvfront heq hpde m hm hcorrector hfluct ε hε hblock u hu heqn
  have hex (i : Fin d) : ∃ φ, IsCorrectorSolution ε U a (Pi.single i 1) φ := by
    obtain ⟨hex, hiff⟩ := corrector_wellDefined hd hε hU hlam ha (Pi.single i 1)
    exact ⟨hex.choose, (hiff hex.choose).mp hex.choose_spec.1⟩
  choose φ hφ using hex
  have hbound := hestimate U hUo hU hne hR ε hε a ha μ m₀ hμ hμB hm₀
    f v ū hv hvB hv₁ hv₂ hvσ hvR hvfront heq hpde φ (Kc / m)
    (Kf / Real.sqrt m) hφ (fun i => hcorrector ε hε hblock i (φ i) (hφ i))
    (hfluct ε hε hblock) u hu heqn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hk : c * (m : ℝ) ≤ kappa d ε := by
    simpa only [hblock] using (hcompare ε hε).1
  have hroot : Real.sqrt c * Real.sqrt (m : ℝ) ≤ Real.sqrt (kappa d ε) := by
    simpa only [Real.sqrt_mul hc.le] using Real.sqrt_le_sqrt hk
  have hinv : 1 / Real.sqrt (kappa d ε) ≤
      (1 / Real.sqrt c) / Real.sqrt (m : ℝ) := by
    rw [div_div]
    exact one_div_le_one_div_of_le (mul_pos hsqrtc hsqrtm) hroot
  have hsum : 1 / Real.sqrt (kappa d ε) + Real.sqrt (Kc / (m : ℝ)) +
      Kf / Real.sqrt (m : ℝ) ≤
      (1 / Real.sqrt c + Real.sqrt Kc + Kf) / Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_div hKc, add_div, add_div]
    linarith only [hinv]
  have habsorb : 1 / Real.sqrt c + Real.sqrt Kc + Kf ≤
      (1 / Real.sqrt c + 1) * (1 + Real.sqrt Kc + Kf) := by
    have hprod := mul_nonneg (by positivity : 0 ≤ 1 / Real.sqrt c)
      (add_nonneg (Real.sqrt_nonneg Kc) hKf)
    nlinarith only [hprod]
  calc
    _ ≤ C₈ * (1 / Real.sqrt (kappa d ε) + Real.sqrt (Kc / (m : ℝ)) +
        Kf / Real.sqrt (m : ℝ)) := hbound
    _ ≤ C₈ * ((1 / Real.sqrt c + Real.sqrt Kc + Kf) / Real.sqrt (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hC₈.le
    _ ≤ C₈ * (((1 / Real.sqrt c + 1) * (1 + Real.sqrt Kc + Kf)) /
        Real.sqrt (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right habsorb hsqrtm.le) hC₈.le
    _ = _ := by ring

end
end LongRange
