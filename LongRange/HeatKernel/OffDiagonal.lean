import LongRange.HeatKernel.Truncated
import LongRange.HeatKernel.PropositionA
import LatticeProb.Analysis.NashProfile
import LatticeProb.Analysis.CriticalProfile
import LatticeProb.External.ChenKimKumagaiWang

/-!
# Davies bounds for the truncated walk

The cited Nash implication transfers truncated heat decay to the explicit Nash rate.
The cited Davies estimate then applies to finitely supported Euclidean tents.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Graph.LongRangeKernel
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- The product constants are positive throughout the range `l > 3`. -/
theorem nash_product_data (d : ℕ) :
    External.ckkwProductData (fun _ ↦ 1)
      (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d) := by
  refine ⟨3, by norm_num, ?_⟩
  intro l hl
  have hpos : 0 < l := by linarith
  have hsub : 0 < l - 1 := by linarith
  exact ⟨by norm_num, mul_pos (by positivity) (pow_pos (div_pos (pow_pos hpos _) hsub) _)⟩

/-- Truncated heat decay implies the explicit critical Nash inequality. -/
theorem truncHeat_nash (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash) (hd : 1 ≤ d)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
        Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
          (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ B : ℝ, 0 < B ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      External.ckkwNashInequality (truncRates hd hlam a ha ρ)
        (fun r ↦ (4 * Real.exp 2 * K ^ (2 / (d : ℝ)))⁻¹ * nashRate d r)
        (B * ρ ^ (-(2 : ℝ))) := by
  obtain ⟨C, B, hC, hB, hheat⟩ := truncHeat_ckkw_onDiagonal hMSC hd hlow hlam a ha
  obtain ⟨D, hD, hprofile⟩ := criticalProfile_comparison d
  let K := max 1 (C * D)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨K, hK, B, hB, ?_⟩
  intro ρ hρ f hf₂ hf₁ hf hn
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
    apply (hheat ρ hρ t x y).trans
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
theorem truncHeat_davies (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
        Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
          (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y)
    (hprod : ∀ α : ℝ, 0 < α →
      External.ckkwProductProfile (fun t ↦ nashProfile d (α * t)) (fun _ ↦ 1)
        (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d))
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ σ : ℝ, 0 ≤ σ → ∀ t : ℝ≥0, 0 < t → ∀ x y,
      ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y} ≤
        A * (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2)) *
          Real.exp (B * ρ ^ (-(2 : ℝ)) * t) *
          Real.exp (-(σ * radius (physical 1 (y - x)) / ρ) +
            B * σ ^ 2 * Real.exp (2 * σ) * (1 + Real.log ρ) * t / ρ ^ 2) := by
  obtain ⟨K, hK, B₀, hB₀, hnash⟩ := truncHeat_nash hMSC hNash hd hlow hlam a ha
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let α := (4 * Real.exp 2 * K ^ (2 / (d : ℝ)))⁻¹
  have hα : 0 < α := by dsimp only [α]; positivity
  obtain ⟨A₀, a₀, hA₀, ha₀, hdav⟩ := hDavies (max 2 (d : ℝ)) 1
    (fun _ ↦ 1) (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d)
    (le_trans (by norm_num) (le_max_left _ _)) le_rfl (nash_product_data d) 1
    (by norm_num)
  obtain ⟨D, hD, hscale⟩ := criticalProfile_scale d (mul_pos hα ha₀)
  obtain ⟨T, hT, htent⟩ := tent_ckkwLambdaSq_le hd hlam
  obtain ⟨C, E, hC, hE, hheat⟩ := truncHeat_ckkw_onDiagonal hMSC hd hlow hlam a ha
  obtain ⟨F, hF, hprofile⟩ := criticalProfile_comparison d
  let A := A₀ * D + C * F
  let B := B₀ + E + 2 * T
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hB₀B : B₀ ≤ B := by dsimp only [B]; linarith
  have hEB : E ≤ B := by dsimp only [B]; linarith
  have hTB : 2 * T ≤ B := by dsimp only [B]; linarith
  refine ⟨A, B, hA, hB, ?_⟩
  intro ρ hρ σ hσ t ht x y
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
            Real.exp (E * ρ ^ (-(2 : ℝ)) * t) := hheat ρ hρ t x x
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
      (ckkwInverseProfile_nashRate hd hα) (hprod α hα)
      (fun r hr ↦ nashRateStar_scaled_pos d hα hr)
      (nashRateStar_scaled_monotoneOn hd hα)
      (nashRateStar_scaled_div_monotoneOn hd hα)
      (by
        intro r hr
        simpa only [inv_one, one_mul] using nashRate_scaled_comparison hd hα hr)
      (Site d) (truncRates hd hlam a ha ρ) (truncRates_symm hd hlam a ha ρ)
      (B₀ * ρ ^ (-(2 : ℝ))) (by positivity) (hnash ρ hρ)
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

/-- The unit heat kernel satisfies the minimum bound of Proposition B.2. -/
theorem unitHeat_offDiagonal (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d)
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
        Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
          (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y)
    (hprod : ∀ α : ℝ, 0 < α →
      External.ckkwProductProfile (fun t ↦ nashProfile d (α * t)) (fun _ ↦ 1)
        (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d))
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x y, x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * min ((1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
          (t * Real.log (2 + radius (physical 1 (y - x))) /
            radius (physical 1 (y - x)) ^ (d + 2)) := by
  obtain ⟨Ca, hCa, hdiag⟩ := unitHeat_onDiagonal hMSC hd hlow hlam a ha
  obtain ⟨A, B, hA, hB, hdav⟩ := truncHeat_davies hMSC hNash hDavies hd hlow
    hprod hlam a ha
  obtain ⟨C, hC, hoff⟩ := offDiagonal_of_truncated_bounds hd
    (fun t x y ↦ ((unitRates hd hlam a ha).transitionKernel t x).real {y})
    (fun ρ t x y ↦ ((truncRates hd hlam a ha ρ).transitionKernel t x).real {y})
    hdiag (fun ρ hρ t x y ↦ unitHeat_le_trunc_add hd hlam a ha hρ t x y)
    (fun ρ hρ hρ₁ t x y hxy ↦ truncHeat_zero_of_lt_one hd hlam a ha hρ hρ₁ t x y hxy)
    hdav
  refine ⟨max Ca C, lt_of_lt_of_le hCa (le_max_left _ _), ?_⟩
  intro t ht x y hxy
  rw [mul_min_of_nonneg _ _ (le_of_lt (lt_of_lt_of_le hCa (le_max_left _ _)))]
  apply le_min
  · apply (hdiag t x y).trans
    have hlog : 0 ≤ Real.log (2 + (t : ℝ)) := Real.log_nonneg (by linarith [t.coe_nonneg])
    exact mul_le_mul_of_nonneg_right (le_max_left Ca C)
      (Real.rpow_nonneg (by positivity) _)
  · have hsp : 0 ≤ (t : ℝ) * Real.log (2 + radius (physical 1 (y - x))) /
        radius (physical 1 (y - x)) ^ (d + 2) := by
      apply div_nonneg
      · exact mul_nonneg t.coe_nonneg
          (zero_le_one.trans (one_le_log_two_add (one_le_radius_displacement hxy)))
      · exact pow_nonneg (radius_nonneg _) _
    have ho := hoff t ht x y hxy
    rw [mul_assoc, mul_div_assoc] at ho
    exact ho.trans (mul_le_mul_of_nonneg_right (le_max_right Ca C) hsp)

end

end LongRange
