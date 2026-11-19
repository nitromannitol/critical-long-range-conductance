import LatticeProb.External.GilbargTrudinger

/-!
# Uniform Schauder bound for the homogenized solution

The cited boundary regularity, Schauder estimate and supremum estimate give a
`C^{2,σ}` bound uniform in the elliptic coefficient, mass, datum and solution.
The constant is chosen before those four quantities.
-/

namespace LongRange

open LatticeProb.Elliptic

/-- The three cited Gilbarg–Trudinger inputs give a uniform homogeneous Dirichlet
`C^{2,σ}` estimate in terms of the datum's `C^{0,σ}` norm on the closure. -/
theorem homogenized_c2Holder_bound
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    {d : ℕ} (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a₀ μ : ℝ),
      a₀ ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
      ∀ f u : (Fin d → ℝ) → ℝ, c0HolderNorm σ (closure U) f < ⊤ →
        IsClassicalDirichletSolution U μ a₀ f u →
        c2HolderNorm σ U u ≤ ENNReal.ofReal C * c0HolderNorm σ (closure U) f := by
  obtain ⟨C₁, hC₁, hschauder⟩ := h66 d hd σ hσ hσ1 U hU Λ hΛ
  obtain ⟨C₂, hC₂, hsup⟩ := h37 d hd U hU.1 hU.2.1 hU.2.2.1
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hproduct : 0 ≤ C₂ * Λ := (mul_pos hC₂ hΛpos).le
  refine ⟨C₁ * (C₂ * Λ + 1), mul_pos hC₁ (by positivity), ?_⟩
  intro a₀ μ ha hμ f u hf hu
  have hapos : 0 < a₀ := lt_of_lt_of_le (inv_pos.mpr hΛpos) ha.1
  have hregular := h619 d hd σ hσ hσ1 U hU a₀ μ hapos hμ.1 f u hf hu
  have hfbound : supNorm U f ≤ c0HolderNorm σ (closure U) f := by
    calc
      supNorm U f ≤ supNorm (closure U) f := biSup_mono fun _ hx => subset_closure hx
      _ ≤ c0HolderNorm σ (closure U) f := le_self_add
  have hdivision : C₂ / a₀ ≤ C₂ * Λ := by
    apply (div_le_iff₀ hapos).mpr
    have hmul : 1 ≤ Λ * a₀ := by
      calc
        1 = Λ * Λ⁻¹ := (mul_inv_cancel₀ hΛpos.ne').symm
        _ ≤ Λ * a₀ := mul_le_mul_of_nonneg_left ha.1 hΛpos.le
    nlinarith
  have hubound : supNorm U u ≤
      ENNReal.ofReal (C₂ * Λ) * c0HolderNorm σ (closure U) f := by
    calc
      supNorm U u ≤ ENNReal.ofReal (C₂ / a₀) * supNorm U f :=
        hsup a₀ μ hapos hμ.1 f u (lt_of_le_of_lt hfbound hf) hu
      _ ≤ ENNReal.ofReal (C₂ * Λ) * c0HolderNorm σ (closure U) f :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hdivision) hfbound
  calc
    c2HolderNorm σ U u ≤
        ENNReal.ofReal C₁ * (supNorm U u + c0HolderNorm σ (closure U) f) :=
      hschauder a₀ μ ha hμ f u hf hu hregular
    _ ≤ ENNReal.ofReal C₁ *
        (ENNReal.ofReal (C₂ * Λ) * c0HolderNorm σ (closure U) f +
          c0HolderNorm σ (closure U) f) :=
      mul_le_mul_right (add_le_add hubound le_rfl) _
    _ = ENNReal.ofReal (C₁ * (C₂ * Λ + 1)) * c0HolderNorm σ (closure U) f := by
      rw [ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_add hproduct zero_le_one,
        ENNReal.ofReal_one, mul_assoc, add_mul, one_mul]

end LongRange
