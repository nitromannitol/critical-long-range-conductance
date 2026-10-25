import LongRange.TwoScale.L2Part
import LongRange.TwoScale.DualPart
import LongRange.TwoScale.Residual
import LongRange.TwoScale.EnergyEstimate

/-!
# The deterministic two-scale estimate

The residual decomposition and Poincaré inequality close the energy estimate on one scale.
The approximation error is then bounded by the discrete norms of the correctors.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The two-scale approximation controls the solution error by the fluctuation and
corrector bounds, uniformly over domains with the prescribed diameter. -/
theorem two_scale_estimate (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (lam R B : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Fin d → ℝ)), IsOpen U → Bornology.IsBounded U →
      U.Nonempty → euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (μ m₀ : ℝ), 0 ≤ μ → μ ≤ B →
      m₀ ∈ Set.Icc lam lam⁻¹ → ∀ (f v ū : (Fin d → ℝ) → ℝ), ContDiff ℝ 2 v →
      (∀ x, |v x| ≤ B) → (∀ x, ‖fderiv ℝ v x‖ ≤ B) →
      (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ) →
      (∀ x, R < radius x → v x = 0) → (∀ x ∈ frontier U, v x = 0) → Set.EqOn v ū U →
      (∀ x ∈ U, μ * ū x - m₀ / (2 * d) * Elliptic.laplacian ū x = f x) →
      ∀ (φ : Fin d → Site d → ℝ) (K F : ℝ),
      (∀ i, IsCorrectorSolution ε U a (Pi.single i 1) (φ i)) →
      (∀ i, h1CritSq ε (φ i) + l2NormSq ε U (φ i) ≤ K) →
      l2Norm ε U (smoothFluctuation ε a m₀ v) ≤ F →
      ∀ u : Site d → ℝ, SupportedIn ε U u →
      (∀ q ∈ latticeSet ε U, μ * u q - generator ε a u q = f (physical ε q)) →
        l2Norm ε U (fun q => u q - ū (physical ε q)) ≤
          C * (1 / Real.sqrt (kappa d ε) + Real.sqrt K + F) := by
  classical
  obtain ⟨C₁, hC₁, hfirst⟩ := l2Part_bound hd hσ hσ1 lam R B hlam
  obtain ⟨C₂, hC₂, hdual⟩ := dualPart_bound hd lam R B hlam
  obtain ⟨Cp, hCp, hp⟩ := poincare d hd R
  let D := Real.sqrt Cp * (2 / lam) * (C₁ * Real.sqrt Cp + C₂)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D + |B| * d + 1, by positivity, ?_⟩
  intro U hUo hU hne hdiam ε hε a ha μ m₀ hμ hμB hm f v ū hv hv0 hv1 hv2 hvH
    hR hboundary heq hpde φ K F hφ hK hF u hu huEq
  have hB : 0 ≤ B := hμ.trans hμB
  have henergy (g : Site d → ℝ) : 0 ≤ h1CritSq ε g := by
    unfold h1CritSq
    exact mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le)
      (tsum_nonneg (fun _ => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))
  have hφL (i : Fin d) : l2NormSq ε U (φ i) ≤ K := by
    have := hK i
    linarith only [this, henergy (φ i)]
  have hφs (i : Fin d) : SupportedIn ε U (φ i) := (hφ i).1
  let h := fun q => u q - approxSolution ε U v φ q
  have hh : SupportedIn ε U h := by
    intro q hq
    dsimp only [h]
    rw [hu q hq, approxSolution_supportedIn hφs q hq, sub_self]
  have hres (q : Site d) (hq : q ∈ latticeSet ε U) :
      μ * h q - generator ε a h q =
        (smoothError ε a μ f v q - μ * ∑ i, gradientCoeff ε v i q * φ i q) +
          (boundaryDefect ε a (exteriorDefect ε U v) q + correctorError ε a v φ q) := by
    have hr := residual_identity hd hε.1 hU hlam ha μ f v hv0 hv1 φ hφ hu huEq hq
    dsimp only [h]
    linarith only [hr]
  have hfirst' := hfirst U hUo hU hdiam ε hε a ha μ m₀ hμ hμB hm f v ū hv
    hv0 hv1 hv2 hvH heq hpde φ K F hφL hF
  have hdual' := hdual U hUo hU hne hdiam ε hε a ha v hv hv1 hv2 hR hboundary
    φ K hφs hK
  have hclose := (energy_estimate_of_poincare_of_nonneg hd hε hlam hμ
    (by positivity : 0 ≤ C₂ * (1 / Real.sqrt (kappa d ε) + Real.sqrt K))
    hCp.le hU ha hh hres hfirst' hdual' (hp U hUo hU hdiam ε hε)).2
  have hk : 0 < kappa d ε := kappa_pos hd hε
  have hs : Real.sqrt (kappa d ε) ≤ kappa d ε :=
    Real.sqrt_le_self_iff.mpr (Or.inr (one_le_kappa hd hε))
  have hinv : 1 / kappa d ε ≤ 1 / Real.sqrt (kappa d ε) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr hk) hs
  let T := 1 / Real.sqrt (kappa d ε) + Real.sqrt K + F
  have hF0 : 0 ≤ F := (Real.sqrt_nonneg _).trans hF
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hfirstT : 1 / kappa d ε + F + Real.sqrt K ≤ T := by
    dsimp only [T]
    linarith only [hinv]
  have hdualT : 1 / Real.sqrt (kappa d ε) + Real.sqrt K ≤ T := by
    dsimp only [T]
    linarith only [hF0]
  have hhT : l2Norm ε U h ≤ D * T := by
    apply hclose.trans
    calc
      _ ≤ Real.sqrt Cp * (2 / lam) *
          (C₁ * T * Real.sqrt Cp + C₂ * T) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfirstT hC₁.le) (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left hdualT hC₂.le)
      _ = _ := by dsimp only [D]; ring
  have hsum : (∑ i, l2Norm ε U (φ i)) ≤ (d : ℝ) * Real.sqrt K := by
    calc
      _ ≤ ∑ _i : Fin d, Real.sqrt K :=
        Finset.sum_le_sum (fun i _ => Real.sqrt_le_sqrt (hφL i))
      _ = _ := by simp
  have happ : l2Norm ε U (fun q => approxSolution ε U v φ q - v (physical ε q)) ≤
      B * d * Real.sqrt K := by
    exact (l2Norm_approxSolution_sub_le hε.1 hU hv1 φ).trans
      ((mul_le_mul_of_nonneg_left hsum hB).trans_eq (by ring))
  rw [l2Norm_congr (h := fun q => h q +
    (approxSolution ε U v φ q - v (physical ε q))) (by
      intro q hq
      rw [← heq (show physical ε q ∈ U from hq)]
      dsimp only [h]
      ring)]
  apply ((l2Norm_add_le hε.1 hU _ _).trans (add_le_add hhT happ)).trans
  have hKT : Real.sqrt K ≤ T := by
    dsimp only [T]
    have hi : 0 ≤ 1 / Real.sqrt (kappa d ε) := by positivity
    linarith only [hi, hF0]
  calc
    _ ≤ D * T + (B * d) * T :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hKT (by positivity))
    _ ≤ (D + |B| * d + 1) * T := by
      rw [abs_of_nonneg hB]
      nlinarith only [hT]

end

end LongRange
