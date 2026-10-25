import LongRange.HeatKernel.UniformOnDiagonal
import LongRange.HeatKernel.Truncated
import LongRange.HeatKernel.PropositionA
import LatticeProb.Analysis.NashProfile
import LatticeProb.Analysis.CriticalProfile
import LatticeProb.External.ChenKimKumagaiWang
import LatticeProb.Analysis.NashProduct

/-!
# Uniform truncated Nash and Davies bounds

One on-diagonal constant controls every elliptic conductance field. Meyer comparison,
the critical Nash profile and Euclidean tents preserve this uniformity in the truncated
Nash inequality and Davies estimate.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Graph.LongRangeKernel
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- Positivity comparison transfers unit heat decay to the truncated walk. -/
theorem truncHeat_onDiagonal_uniform
    (hMSC : External.MuruganSaloffCosteUniform) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ (t : ℝ≥0) (x y : Site d),
        ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y} ≤
          C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) *
            Real.exp (B * ρ ^ (-(2 : ℝ)) * t) := by
  obtain ⟨C, hC, hc⟩ := unitHeat_onDiagonal_uniform hMSC d hd hlam
  obtain ⟨B, hB, hb⟩ := removed_intensity_le hd hlam
  refine ⟨C, B, hC, hB, ?_⟩
  intro a ha ρ hρ t x y
  have h := (unitRates hd hlam a ha).transitionKernel_le_of_truncation
    (truncRates hd hlam a ha ρ) rfl (truncRates_q_le hd hlam a ha ρ)
    (mul_nonneg hB.le (Real.rpow_nonneg (zero_lt_one.trans_le hρ).le _))
    (hb a ha ρ hρ) t x y
  have ht := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht
  calc
    _ ≤ Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        ((unitRates hd hlam a ha).transitionKernel t x).real {y} := ht
    _ ≤ Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
        (C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left (hc a ha t x y) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Truncated heat decay implies the explicit critical Nash inequality. -/
theorem truncHeat_nash_uniform (hMSC : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ B : ℝ, 0 < B ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ ρ : ℝ, 1 ≤ ρ →
      External.ckkwNashInequality (truncRates hd hlam a ha ρ)
        (fun r ↦ (4 * Real.exp 2 * K ^ (2 / (d : ℝ)))⁻¹ * nashRate d r)
        (B * ρ ^ (-(2 : ℝ))) := by
  obtain ⟨C, B, hC, hB, hheat⟩ := truncHeat_onDiagonal_uniform hMSC hd hlam
  obtain ⟨D, hD, hprofile⟩ := criticalProfile_comparison d
  let K := max 1 (C * D)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨K, hK, B, hB, ?_⟩
  intro a ha ρ hρ f hf₂ hf₁ hf hn
  have hδ : 0 ≤ B * ρ ^ (-(2 : ℝ)) := by positivity
  have hpos : ∀ t > 0, 0 < K * criticalProfile d t :=
    fun t ht ↦ mul_pos hKpos (criticalProfile_pos d ht)
  have hmono : AntitoneOn (fun t ↦ K * criticalProfile d t) (Set.Ioi 0) := by
    intro s hs t ht hst
    exact mul_le_mul_of_nonneg_left
      ((criticalProfile_strictAntiOn hd).antitoneOn hs ht hst) hKpos.le
  have hbound (t : ℝ≥0) (ht : 0 < t) (x y : Site d) :
      External.ckkwKernel (truncRates hd hlam a ha ρ) t x y ≤
        (K * criticalProfile d t) * Real.exp (B * ρ ^ (-(2 : ℝ)) * t) := by
    apply (hheat a ha ρ hρ t x y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ C * (D * criticalProfile d t) :=
        mul_le_mul_of_nonneg_left (hprofile t ht) hC.le
      _ ≤ K * criticalProfile d t := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right 1 (C * D))
          (criticalProfile_pos d ht).le
  have hupper := hNash (Site d) (truncRates hd hlam a ha ρ)
    (truncRates_symm hd hlam a ha ρ) _ _ hδ hpos hmono hbound f hf₂ hf₁ hf hn
  have hlower := nashRate_le_ckkwNashProfile hd hK hn
  have henergy : 0 ≤ External.ckkwEnergy (truncRates hd hlam a ha ρ) f := by
    unfold External.ckkwEnergy
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun i ↦ tsum_nonneg
      (fun j ↦ mul_nonneg ((truncRates hd hlam a ha ρ).q_nonneg i j) (sq_nonneg _))))
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg henergy (mul_nonneg hδ hn.le))).mp (hlower.trans hupper)

/-- Finitely supported Euclidean tents give the truncated Davies estimate. -/
theorem truncHeat_davies_uniform (hMSC : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (d : ℕ) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹, ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ σ : ℝ, 0 ≤ σ → ∀ t : ℝ≥0, 0 < t → ∀ x y,
      ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y} ≤
        A * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
          Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
          Real.exp (-(σ * radius (physical 1 (y - x)) / ρ) +
            B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2) := by
  obtain ⟨K, hK, B₀, hB₀, hnash⟩ := truncHeat_nash_uniform hMSC hNash hd hlam
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let α := (4 * Real.exp 2 * K ^ (2 / (d : ℝ)))⁻¹
  have hα : 0 < α := by dsimp only [α]; positivity
  obtain ⟨A₀, a₀, hA₀, ha₀, hdav⟩ := hDavies (max 2 (d : ℝ)) 1
    (fun _ ↦ 1) (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d)
    (le_trans (by norm_num) (le_max_left _ _)) le_rfl (nashProfile_productProfile hd hα).1 1
    (by norm_num)
  obtain ⟨D, hD, hscale⟩ := criticalProfile_scale d (mul_pos hα ha₀)
  obtain ⟨T, hT, htent⟩ := tent_ckkwLambdaSq_le hd hlam
  obtain ⟨C, E, hC, hE, hheat⟩ := truncHeat_onDiagonal_uniform hMSC hd hlam
  obtain ⟨F, hF, hprofile⟩ := criticalProfile_comparison d
  let A := A₀ * D + C * F
  let B := B₀ + E + 2 * T
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hB₀B : B₀ ≤ B := by dsimp only [B]; linarith
  have hEB : E ≤ B := by dsimp only [B]; linarith
  have hTB : 2 * T ≤ B := by dsimp only [B]; linarith
  refine ⟨A, B, hA, hB, ?_⟩
  intro a ha ρ hρ σ hσ t ht x y
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have htR : 0 < (t : ℝ) := ht
  have hφ : 0 < criticalProfile d t := criticalProfile_pos d htR
  have hlog : 0 ≤ 1 + Real.log ρ := by positivity [Real.log_nonneg hρ]
  have hexp₀ : Real.exp (B₀ * ρ ^ (-(2 : ℝ)) * t) ≤
      Real.exp (B * ρ ^ (-(2 : ℝ)) * t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB₀B (by positivity)) t.coe_nonneg
  by_cases hxy : x = y
  · subst y
    have hr : radius (physical 1 (x - x)) = 0 := by
      simp [physical, radius]
    rw [hr, mul_zero, zero_div, neg_zero, zero_add]
    have hfirst : External.ckkwKernel (truncRates hd hlam a ha ρ) t x x ≤
        A * criticalProfile d t * Real.exp (B * ρ ^ (-(2 : ℝ)) * t) := by
      calc
        _ ≤ C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) *
            Real.exp (E * ρ ^ (-(2 : ℝ)) * t) := hheat a ha ρ hρ t x x
        _ ≤ (C * F) * criticalProfile d t *
            Real.exp (B * ρ ^ (-(2 : ℝ)) * t) := by
          apply mul_le_mul
          · simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left (hprofile t htR) hC.le
          · apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hEB (by positivity)) t.coe_nonneg
          · positivity
          · positivity
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith [mul_pos hA₀ hD]) hφ.le
    exact hfirst.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_exp (by positivity)))
  · let r := radius (physical 1 (y - x))
    have hr : 0 < r := zero_lt_one.trans_le (one_le_radius_displacement hxy)
    have hs : 0 ≤ σ / ρ := div_nonneg hσ hρpos.le
    have hfinite := tent_ckkwLambdaSq_ne_top hd hlam a ha x r hs hρ
    have hbound := hdav (fun r ↦ α * nashRate d r)
      (fun r ↦ α * nashRateStar d r) (fun t ↦ nashProfile d (α * t))
      (ckkwInverseProfile_nashRate hd hα) (nashProfile_productProfile hd hα).2
      (fun r hr ↦ nashRateStar_scaled_pos d hα hr)
      (nashRateStar_scaled_monotoneOn hd hα)
      (nashRateStar_scaled_div_monotoneOn hd hα)
      (by
        intro r hr
        simpa only [inv_one, one_mul] using nashRate_scaled_comparison hd hα hr)
      (Site d) (truncRates hd hlam a ha ρ) (truncRates_symm hd hlam a ha ρ)
      (B₀ * ρ ^ (-(2 : ℝ))) (by positivity) (hnash a ha ρ hρ)
      (tent x r (σ / ρ)) (tent_hasFiniteSupport x hr _) hfinite t ht x y
    have hpeak : |tent x r (σ / ρ) y - tent x r (σ / ρ) x| = σ * r / ρ := by
      rw [tent_center x hr.le, sub_zero, tent_peak, abs_of_nonneg (mul_nonneg hs hr.le)]
      ring
    rw [hpeak] at hbound
    have hlambda := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (htent a ha x r (σ / ρ) hs ρ hρ)
    rw [ENNReal.toReal_ofReal (by positivity)] at hlambda
    have hpen : (1 + (1 : ℝ)) *
        (External.ckkwLambdaSq (truncRates hd hlam a ha ρ) (tent x r (σ / ρ))).toReal * t ≤
        B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2 := by
      have heq : 2 * (σ / ρ) * ρ = 2 * σ := by field_simp
      rw [heq] at hlambda
      calc
        _ ≤ 2 * (T * (σ / ρ) ^ 2 * Real.exp (2 * σ) *
            (1 + Real.log ρ)) * t := by
          norm_num only [one_add_one_eq_two]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlambda (by norm_num)) t.coe_nonneg
        _ = (2 * T) * σ ^ 2 * Real.exp (2 * σ) *
            (1 + Real.log ρ) * t / ρ ^ 2 := by ring
        _ ≤ _ := by gcongr
    have hprof : nashProfile d (α * (a₀ * t)) ≤ D * criticalProfile d t := by
      apply (nashProfile_comparison hd (mul_pos hα (mul_pos ha₀ htR))).2.trans
      simpa only [criticalProfile, mul_assoc] using hscale t htR
    calc
      _ ≤ A₀ * nashProfile d (α * (a₀ * t)) *
          Real.exp (B₀ * ρ ^ (-(2 : ℝ)) * t) *
          Real.exp (-(σ * r / ρ) + (1 + (1 : ℝ)) *
            (External.ckkwLambdaSq (truncRates hd hlam a ha ρ)
              (tent x r (σ / ρ))).toReal * t) := hbound
      _ ≤ (A₀ * D) * criticalProfile d t *
          Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
          Real.exp (-(σ * r / ρ) +
            B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2) := by
        apply mul_le_mul
        · apply mul_le_mul
          · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprof hA₀.le
          · exact hexp₀
          · positivity
          · positivity
        · exact Real.exp_le_exp.mpr (add_le_add_right hpen _)
        · positivity
        · positivity
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith [mul_pos hC hF]) hφ.le

/-- Unit conductances in dimension one satisfy the common truncated Davies bound. -/
theorem truncHeat_davies_one
    (hMSC : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ σ : ℝ, 0 ≤ σ → ∀ t : ℝ≥0, 0 < t → ∀ x y : Site 1,
      ((truncRates (by norm_num : 1 ≤ 1) (by norm_num : (0 : ℝ) < 1)
        (fun _ : Edge 1 => (1 : ℝ)) (by intro _; norm_num) ρ).transitionKernel t x).real
          {y} ≤ A * (t * (1 + Real.log (1 + t))) ^ (-(1 / (2 : ℝ))) *
          Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
          Real.exp (-(σ * radius (physical 1 (y - x)) / ρ) +
            B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := truncHeat_davies_uniform hMSC hNash hDavies
    1 (by norm_num) (by norm_num : (0 : ℝ) < 1)
  refine ⟨A, B, hA, hB, ?_⟩
  intro ρ hρ σ hσ t ht x y
  simpa only [Nat.cast_one] using
    hbound (fun _ : Edge 1 => (1 : ℝ)) (by intro _; norm_num) ρ hρ σ hσ t ht x y

end

end LongRange
