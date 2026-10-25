import LongRange.TwoScale.BlockEstimate
import LongRange.TwoScale.FluctuationEvent
import LongRange.TwoScale.BlockEvent
import LongRange.TwoScale.MinimalScale
import LongRange.Continuum.Package

/-!
# Quantitative homogenization

The continuum extension and the two measurable block events imply the main error
estimate beyond an exponentially integrable minimal scale.
-/

namespace LongRange

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice TwoScale

noncomputable section

/-- The minimal scale tail has constants determined entirely by the block tail constants. -/
theorem measure_minimalScale_tail_explicit {Ω : Type*} [MeasurableSpace Ω]
    {G : ℕ → Set Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {C c K : ℝ} (hC : 0 < C) (hc : 0 < c) (hK : 0 < K)
    (hP : ∀ m : ℕ, P (G m)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * m)))) :
    ∀ s : ℝ, 1 ≤ s →
      P {ω | ENNReal.ofReal s < minimalScale G K ω} ≤
        ENNReal.ofReal (((C / (1 - Real.exp (-c)) + 1) * Real.exp c) *
          Real.exp (-(c / K * s))) := by
  have hden : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
    linarith
  let A : ℝ := C / (1 - Real.exp (-c))
  have hA : 0 < A := div_pos hC hden
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hexp : Real.exp c * Real.exp (-(c / K * s)) =
      Real.exp (c - c * (s / K)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_cases hlarge : K ≤ s
  · let N : ℕ := ⌊s / K⌋₊
    have hN : 1 ≤ N := Nat.le_floor ((le_div_iff₀ hK).mpr (by simpa using hlarge))
    have hNs : K * N ≤ s := by
      have hf := (le_div_iff₀ hK).mp (Nat.floor_le (div_nonneg hspos.le hK.le))
      simpa only [mul_comm] using hf
    have hsubset : {ω | ENNReal.ofReal s < minimalScale G K ω} ⊆
        {ω | ENNReal.ofReal (K * N) < minimalScale G K ω} := by
      intro ω hω
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hNs) hω
    have hfloor : s / K < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hexple : Real.exp (-(c * N)) ≤ Real.exp (c - c * (s / K)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_lt_mul_of_pos_left hfloor hc]
    calc
      _ ≤ P {ω | ENNReal.ofReal (K * N) < minimalScale G K ω} := measure_mono hsubset
      _ ≤ ENNReal.ofReal (C * Real.exp (-(c * N)) / (1 - Real.exp (-c))) :=
        measure_minimalScale_tail_block hC hc hP hN
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc, hexp]
        have halg : C * Real.exp (-(c * N)) / (1 - Real.exp (-c)) =
            A * Real.exp (-(c * N)) := by dsimp [A]; ring
        rw [halg]
        exact (mul_le_mul_of_nonneg_left hexple hA.le).trans
          (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
  · have hratio : s / K < 1 := (div_lt_one hK).mpr (lt_of_not_ge hlarge)
    have hexpone : 1 ≤ Real.exp (c - c * (s / K)) := by
      apply Real.one_le_exp
      nlinarith [mul_lt_mul_of_pos_left hratio hc]
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc, hexp]
        exact one_le_mul_of_one_le_of_one_le (by linarith) hexpone


/-- Quantitative homogenization with an exponential minimal-scale tail. -/
theorem main_theorem
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (d : ℕ) (hd : 1 ≤ d) (lam σ μ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    (U : Set (Fin d → ℝ)) (hU : LatticeProb.Elliptic.IsC2HolderDomain σ U) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ f : (Fin d → ℝ) → ℝ,
        LatticeProb.Elliptic.c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M →
      ∀ ū : (Fin d → ℝ) → ℝ, LatticeProb.Elliptic.IsClassicalDirichletSolution U μ
          (meanConductance P hd a / (2 * d)) f ū →
      ∃ 𝒳 : Ω → ENNReal, Measurable 𝒳 ∧
        (∀ s : ℝ, 1 ≤ s →
          P {ω | ENNReal.ofReal s < 𝒳 ω} ≤ ENNReal.ofReal (C * Real.exp (-(c * s)))) ∧
        ∀ ω, ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → 𝒳 ω ≤ ENNReal.ofReal |Real.log ε| →
          ∀ u : Site d → ℝ, SupportedIn ε U u →
            (∀ q ∈ latticeSet ε U, μ * u q - generator ε (a ω) u q = f (physical ε q)) →
            l2Norm ε U (fun q => u q - ū (physical ε q)) ≤ C / Real.sqrt |Real.log ε| := by
  classical
  by_cases hlam : 0 < lam
  · let Λ := max 1 (max (2 * (d : ℝ) / lam) μ)
    have hΛ : 1 ≤ Λ := le_max_left _ _
    have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
    have hΛd : 2 * (d : ℝ) / lam ≤ Λ :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hμΛ : μ ≤ Λ := (le_max_right _ _).trans (le_max_right _ _)
    obtain ⟨Cp, Rp, hCp, _hRp, _hUR, hext⟩ :=
      continuum_extension h619 h66 h37 h637 hd hσ.1 hσ.2 hU hΛ
    let B := max (Cp * max M 0) μ + 1
    let R := max Rp (euclideanDiam U)
    have hB : Cp * max M 0 ≤ B := (le_max_left _ _).trans (by dsimp [B]; linarith)
    have hμB : μ ≤ B := (le_max_right _ _).trans (by dsimp [B]; linarith)
    obtain ⟨Cb, hCb, hblock⟩ := block_estimate hd hσ.1 hσ.2.le lam R B hlam
      hU.1 hU.2.2.1 hU.2.1.nonempty (le_max_right _ _)
    obtain ⟨Cc, cc, hCc, hcc, hcorr⟩ := block_corrector_event hd lam hlam
      hU.1 hU.2.2.1 hU.2.1.nonempty
    obtain ⟨Cf, cf, hCf, hcf, hfluct⟩ := block_fluctuation_event hd hσ.1 hσ.2.le
      lam B hlam hU.1 hU.2.2.1 hU.2.1.nonempty
    let K := 1 + Real.log 3 + |Real.log (cubeSide U)|
    have hK : 0 < K := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
      dsimp [K]
      positivity
    let c := min cc cf
    have hc : 0 < c := lt_min hcc hcf
    let Ct := ((Cc + Cf) / (1 - Real.exp (-c)) + 1) * Real.exp c
    have hden : 0 < 1 - Real.exp (-c) := by
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
      linarith
    have hCt : 0 < Ct := by dsimp [Ct]; positivity
    let Ce := Cb * (1 + Real.sqrt Cc + Cf) * Real.sqrt K
    have hCe : 0 < Ce := by dsimp [Ce]; positivity
    refine ⟨max Ct Ce, c / K, hCt.trans_le (le_max_left _ _), div_pos hc hK, ?_⟩
    intro Ω _ P a hA f hf ū hū
    letI : IsProbabilityMeasure P := hA.isProbabilityMeasure
    have hD : (1 : ℝ) ≤ 2 * d := by exact_mod_cast (by omega : 1 ≤ 2 * d)
    have hDpos : (0 : ℝ) < 2 * d := zero_lt_one.trans_le hD
    have hmean := hA.mean_mem_Icc
    have ha₀ : meanConductance P hd a / (2 * d) ∈ Set.Icc Λ⁻¹ Λ := by
      constructor
      · have hi : (lam / (2 * (d : ℝ)))⁻¹ ≤ Λ := by
          simpa only [inv_div] using hΛd
        exact ((inv_le_comm₀ (div_pos hlam hDpos) hΛpos).mp hi).trans
          (div_le_div_of_nonneg_right hmean.1 hDpos.le)
      · calc
          _ ≤ lam⁻¹ / (2 * d) := div_le_div_of_nonneg_right hmean.2 hDpos.le
          _ ≤ lam⁻¹ := div_le_self (inv_nonneg.mpr hlam.le) hD
          _ ≤ 2 * (d : ℝ) / lam := by
            rw [inv_eq_one_div]
            exact div_le_div_of_nonneg_right hD hlam.le
          _ ≤ Λ := hΛd
    obtain ⟨v, hv, hvR, heq, hvfront, hv0, hv1, hv2, hvH⟩ :=
      hext _ μ ha₀ ⟨hμ, hμΛ⟩ f ū (max M 0) (le_max_right _ _)
        (hf.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) hū
    have hv0' := fun x => (hv0 x).trans hB
    have hv1' := fun x => (hv1 x).trans hB
    have hv2' := fun x => (hv2 x).trans hB
    have hvH' : ∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
        B * radius (x - y) ^ σ := fun x y => (hvH x y).trans
          (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (radius_nonneg _) _))
    choose Gc hGc htc hgoodc using hcorr P a hA
    choose Gf hGf htf hgoodf using hfluct P a hA v hv hv0' hv1' hv2' hvH'
    let G := fun m => Gc m ∩ Gf m
    have hG : ∀ m, MeasurableSet (G m) := fun m => (hGc m).inter (hGf m)
    have ht : ∀ m : ℕ, P (G m)ᶜ ≤
        ENNReal.ofReal ((Cc + Cf) * Real.exp (-(c * m))) := by
      intro m
      have hec : Real.exp (-(cc * m)) ≤ Real.exp (-(c * m)) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg m))
      have hef : Real.exp (-(cf * m)) ≤ Real.exp (-(c * m)) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg m))
      calc
        _ ≤ P (Gc m)ᶜ + P (Gf m)ᶜ := by
          rw [show (G m)ᶜ = (Gc m)ᶜ ∪ (Gf m)ᶜ from Set.compl_inter _ _]
          exact measure_union_le _ _
        _ ≤ ENNReal.ofReal (Cc * Real.exp (-(cc * m))) +
            ENNReal.ofReal (Cf * Real.exp (-(cf * m))) := add_le_add (htc m) (htf m)
        _ = ENNReal.ofReal (Cc * Real.exp (-(cc * m)) +
            Cf * Real.exp (-(cf * m))) := by rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          calc
            _ ≤ Cc * Real.exp (-(c * m)) + Cf * Real.exp (-(c * m)) :=
              add_le_add (mul_le_mul_of_nonneg_left hec hCc.le)
                (mul_le_mul_of_nonneg_left hef hCf.le)
            _ = _ := by ring
    refine ⟨minimalScale G K, measurable_minimalScale hG K, ?_, ?_⟩
    · intro s hs
      exact (measure_minimalScale_tail_explicit (add_pos hCc hCf) hc hK ht s hs).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left Ct Ce)
          (Real.exp_nonneg _)))
    · intro ω ε hε hscale u hu heqn
      let m := blockIndex U ε hε.1
      have hm : 1 ≤ m := (blockIndex_spec U hε.1).1
      have hlog := (block_log_bounds
        (cubeSide_pos_and_fits hd hU.2.2.1 hU.1 hU.2.1.nonempty).1 hε).1
      have hlogle : |Real.log ε| ≤ K * m := by linarith only [hlog]
      have hgood := mem_of_minimalScale_le hK hm
        (hscale.trans (ENNReal.ofReal_le_ofReal hlogle))
      have hb := hblock Cc Cf hCc.le hCf.le (a ω) (hA.bounds ω) μ
        (meanConductance P hd a) hμ hμB hmean f v ū hv hv0' hv1' hv2' hvH'
        (fun x hx => hvR x ((le_max_left Rp (euclideanDiam U)).trans hx.le))
        hvfront heq hū.2.2.2 m hm (hgoodc m ω hgood.1) (hgoodf m ω hgood.2)
        ε hε rfl u hu heqn
      have hlogpos : 0 < |Real.log ε| := abs_pos.mpr (ne_of_lt (Real.log_neg hε.1 hε.2))
      have hslog : 0 < Real.sqrt |Real.log ε| := Real.sqrt_pos.mpr hlogpos
      have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm))
      have hs : Real.sqrt |Real.log ε| ≤ Real.sqrt K * Real.sqrt (m : ℝ) := by
        simpa only [Real.sqrt_mul hK.le] using Real.sqrt_le_sqrt hlogle
      have hfactor : 0 ≤ Cb * (1 + Real.sqrt Cc + Cf) := by positivity
      calc
        _ ≤ Cb * (1 + Real.sqrt Cc + Cf) / Real.sqrt (m : ℝ) := hb
        _ ≤ Ce / Real.sqrt |Real.log ε| := by
          apply (div_le_div_iff₀ hsm hslog).mpr
          dsimp [Ce]
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hfactor
        _ ≤ _ := div_le_div_of_nonneg_right (le_max_right Ct Ce) hslog.le
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hlam hA.lam_pos).elim

end
end LongRange
