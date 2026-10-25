import LongRange.Dirichlet.Proposition
import LongRange.TwoScale.BlockComparison
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Measurable block corrector events

Finite intersections of the measurable variables in Proposition 5.1 control all scales
in one logarithmic block through its fixed physical cube representative.
-/

namespace LongRange

open MeasureTheory LatticeProb TwoScale Filter

open scoped Topology

noncomputable section

variable {d : ℕ}

/-- Physical coordinate cubes are open. -/
theorem cube_isOpen (w : ℝ) (L : ℕ) : IsOpen (cube (d := d) w L) := by
  have heq : cube (d := d) w L =
      ⋂ i : Fin d, {x : Fin d → ℝ | |x i| < w * 3 ^ L / 2} := by
    ext x
    simp only [cube, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (continuous_apply i).abs continuous_const

/-- Polynomial factors times the square root of a triadic representative vanish. -/
lemma block_representative_decay {w : ℝ} (hw : 0 < w) (B : ℝ) :
    ∃ N : ℕ, ∀ m ≥ N,
      (m : ℝ) ^ 2 * (B * (w / 3 ^ m) ^ (1 / 2 : ℝ)) ≤ 1 := by
  have hr : (1 : ℝ) < (3 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 2 hr).mul_const
    (B * w ^ (1 / 2 : ℝ))
  have ht' : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 /
      ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ m * (B * w ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul] using ht
  have he := ht'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun m hm => ?_⟩
  have h := (hN m hm).le
  calc
    _ = (m : ℝ) ^ 2 / ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ m *
        (B * w ^ (1 / 2 : ℝ)) := by
      rw [Real.div_rpow hw.le (by positivity) _,
        ← Real.rpow_pow_comm (show (0 : ℝ) ≤ 3 by norm_num)]
      ring
    _ ≤ 1 := h

/-- An exponential stochastic bound controls a larger deterministic threshold. -/
lemma measure_exceed_le_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {θ r : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hX : OsBound P 1 θ X) (hscale : (m : ℝ) * θ ≤ r) :
    P {ω | r < X ω} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  have htail := hX m (by exact_mod_cast hm)
  rw [Real.rpow_one] at htail
  apply (measure_mono ?_).trans htail
  intro ω hω
  exact hscale.trans_lt (hω.trans_le (le_max_left _ _))

/-- Step 5: measurable block events control every coordinate corrector in the block. -/
theorem block_corrector_event (hd : 1 ≤ d) (lam : ℝ) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hUo : IsOpen U) (hU : Bornology.IsBounded U)
    (hne : U.Nonempty) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a → ∀ m : ℕ,
      ∃ G : Set Ω, MeasurableSet G ∧
        P Gᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * m))) ∧
        ∀ ω ∈ G, ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
          blockIndex U ε hε.1 = m → ∀ (i : Fin d) (φ : Site d → ℝ),
          IsCorrectorSolution ε U (a ω) (Pi.single i 1) φ →
            h1CritSq ε φ + l2NormSq ε U φ ≤ C / m := by
  classical
  have hw := (cubeSide_pos_and_fits hd hU hUo hne).1
  obtain ⟨A, L, hA, hcompare⟩ := block_corrector_comparison hd hUo hU hne lam hlam
  let V := cube (d := d) (cubeSide U) L
  have hVo : IsOpen V := cube_isOpen _ _
  have hV : Bornology.IsBounded V := cube_isBounded _ _
  obtain ⟨K, hK, hbound⟩ := corrector_domain_bound d lam V hVo hV
  obtain ⟨k, hk, hκ⟩ := TwoScale.le_kappa hd hw
  let B := K / k + K
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨N, hN⟩ := block_representative_decay hw B
  let D := A * (K / k + 2)
  have hD : 0 < D := by dsimp [D]; positivity
  let C := max (2 * d * Real.exp (N + 1)) D
  have hC : 0 < C := hD.trans_le (le_max_right _ _)
  refine ⟨C, 1, hC, zero_lt_one, ?_⟩
  intro Ω _ P a hAss m
  letI : IsProbabilityMeasure P := hAss.isProbabilityMeasure
  by_cases hlarge : N + 1 ≤ m
  · by_cases hblock : ∃ ε : ℝ, ∃ hε : ε ∈ Set.Ioo (0 : ℝ) 1,
        blockIndex U ε hε.1 = m
    · obtain ⟨ε₀, hε₀, hm₀⟩ := hblock
      have hrep : cubeSide U / 3 ^ m ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa only [hm₀] using (representative_mem_block hw hε₀).choose
      let ε := cubeSide U / 3 ^ m
      have hm : 1 ≤ m := by omega
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hindex' : blockIndex U ε hrep.1 = m :=
        blockIndex_representative hw hm
      have hκm : k * m ≤ kappa d ε := by
        simpa only [hindex'] using hκ ε hrep
      have hκpos := kappa_pos hd hrep
      have hkκ : k ≤ kappa d ε := by
        have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
        exact (show k ≤ k * (m : ℝ) by nlinarith only [hk, hmone]).trans hκm
      have hdecay := hN m (by omega)
      have hsmall : (m : ℝ) * (B * ε ^ (1 / 2 : ℝ)) ≤ 1 / m := by
        apply (le_div_iff₀ hmpos).mpr
        nlinarith only [hdecay]
      have hpow : ε ^ d ≤ ε ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_ge hrep.1 hrep.2.le
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hrpow : ε ^ ((d : ℝ) / 2) ≤ ε ^ (1 / 2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge hrep.1 hrep.2.le
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hscale₁ : K * ε ^ d / kappa d ε ≤ B * ε ^ (1 / 2 : ℝ) := by
        calc
          _ ≤ K * ε ^ d / k :=
            div_le_div_of_nonneg_left (by positivity) hk hkκ
          _ ≤ K * ε ^ (1 / 2 : ℝ) / k :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK.le) hk.le
          _ ≤ B * ε ^ (1 / 2 : ℝ) := by
            have ht := Real.rpow_nonneg hrep.1.le (1 / 2 : ℝ)
            change K * ε ^ (1 / 2 : ℝ) / k ≤
              (K / k + K) * ε ^ (1 / 2 : ℝ)
            calc
              _ = (K / k) * ε ^ (1 / 2 : ℝ) := by ring
              _ ≤ _ := by nlinarith only [mul_nonneg hK.le ht]
      have hscale₂ : K * ε ^ ((d : ℝ) / 2) ≤ B * ε ^ (1 / 2 : ℝ) := by
        apply (mul_le_mul_of_nonneg_left hrpow hK.le).trans
        have ht := Real.rpow_nonneg hrep.1.le (1 / 2 : ℝ)
        dsimp [B]
        nlinarith only [mul_nonneg (div_pos hK hk).le ht]
      have hexists (i : Fin d) : ∃ Φ : Ω → Site d → ℝ,
          ∀ ω, IsCorrectorSolution ε V (a ω) (Pi.single i 1) (Φ ω) := by
        have he (ω : Ω) : ∃ φ : Site d → ℝ,
            IsCorrectorSolution ε V (a ω) (Pi.single i 1) φ := by
          obtain ⟨φ, hφ, _⟩ :=
            (corrector_wellDefined hd hrep hV hlam (hAss.bounds ω) (Pi.single i 1)).1
          exact ⟨φ, (corrector_wellDefined hd hrep hV hlam
            (hAss.bounds ω) (Pi.single i 1)).2 φ |>.mp hφ⟩
        exact ⟨fun ω => (he ω).choose, fun ω => (he ω).choose_spec⟩
      choose Φ hΦ using hexists
      have hvariables (i : Fin d) := hbound P a hAss ε hrep i (Φ i) (hΦ i)
      choose X Y hmX hmY hoX hoY hnorm using hvariables
      let G : Set Ω := ⋂ i : Fin d, {ω | X i ω ≤ 1 / m} ∩ {ω | Y i ω ≤ 1 / m}
      have hG : MeasurableSet G := by
        apply MeasurableSet.iInter
        intro i
        exact (measurableSet_le (hmX i) measurable_const).inter
          (measurableSet_le (hmY i) measurable_const)
      have htailX (i : Fin d) :
          P {ω | 1 / (m : ℝ) < X i ω} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
        measure_exceed_le_exp hm (hoX i)
          ((mul_le_mul_of_nonneg_left hscale₁ hmpos.le).trans hsmall)
      have htailY (i : Fin d) :
          P {ω | 1 / (m : ℝ) < Y i ω} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
        measure_exceed_le_exp hm ((hoY i).of_exponent_le (by norm_num))
          ((mul_le_mul_of_nonneg_left hscale₂ hmpos.le).trans hsmall)
      refine ⟨G, hG, ?_, ?_⟩
      · have hcompl : Gᶜ = ⋃ i : Fin d,
            ({ω | 1 / (m : ℝ) < X i ω} ∪ {ω | 1 / (m : ℝ) < Y i ω}) := by
          ext ω
          simp only [G, Set.mem_compl_iff, Set.mem_iInter, Set.mem_inter_iff,
            Set.mem_setOf_eq, not_forall, not_and_or, not_le, Set.mem_iUnion,
            Set.mem_union]
        rw [hcompl]
        calc
          _ ≤ ∑ i : Fin d, P ({ω | 1 / (m : ℝ) < X i ω} ∪
              {ω | 1 / (m : ℝ) < Y i ω}) := measure_iUnion_fintype_le P _
          _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (-(m : ℝ))) +
              ENNReal.ofReal (Real.exp (-(m : ℝ)))) := by
            apply Finset.sum_le_sum
            intro i _
            exact (measure_union_le _ _).trans (add_le_add (htailX i) (htailY i))
          _ = ENNReal.ofReal (2 * d * Real.exp (-(m : ℝ))) := by
            simp only [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
            rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            congr 1
            ring
          _ ≤ ENNReal.ofReal (C * Real.exp (-(1 * (m : ℝ)))) := by
            apply ENNReal.ofReal_le_ofReal
            have he : 1 ≤ Real.exp (N + 1) := Real.one_le_exp_iff.mpr (by positivity)
            have htwo : 0 ≤ (2 * d : ℝ) := by positivity
            have hfactor : (2 * d : ℝ) ≤ C :=
              (show (2 * d : ℝ) ≤ 2 * d * Real.exp (N + 1) by
                nlinarith only [he, htwo]).trans (le_max_left _ _)
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
      · intro ω hω δ hδ hδm i φ hφ
        have hωi := Set.mem_iInter.mp hω i
        have hnorm' : h1CritSq ε (Φ i ω) + l2NormSq ε V (Φ i ω) ≤
            (K / k + 2) / m := by
          have hκdiv : K / kappa d ε ≤ (K / k) / m := by
            calc
              _ ≤ K / (k * m) :=
                div_le_div_of_nonneg_left hK.le (mul_pos hk hmpos) hκm
              _ = _ := by ring
          have hn := hnorm i ω
          change X i ω ≤ 1 / m ∧ Y i ω ≤ 1 / m at hωi
          have heq : (K / k + 2) / (m : ℝ) = (K / k) / m + 1 / m + 1 / m := by
            ring
          rw [heq]
          linarith only [hn, hκdiv, hωi.1, hωi.2]
        have hrepΦ : IsCorrectorSolution
            (cubeSide U / 3 ^ blockIndex U δ hδ.1)
            (cube (cubeSide U / 3 ^ blockIndex U δ hδ.1)
              (blockIndex U δ hδ.1 + L)) (a ω) (Pi.single i 1) (Φ i ω) := by
          rw [hδm, cube_representative_eq]
          exact hΦ i ω
        have hc := hcompare δ hδ (a ω) (hAss.bounds ω) (Pi.single i 1)
          φ (Φ i ω) hφ hrepΦ
        rw [hδm, cube_representative_eq] at hc
        apply hc.trans
        calc
          _ ≤ A * ((K / k + 2) / m) := mul_le_mul_of_nonneg_left hnorm' hA.le
          _ = D / m := by dsimp [D]; ring
          _ ≤ C / m := div_le_div_of_nonneg_right (le_max_right _ _) hmpos.le
    · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
      · simp only [Set.compl_univ, measure_empty]
        exact bot_le
      · intro ω _ ε hε hm
        exact (hblock ⟨ε, hε, hm⟩).elim
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · have hmN : (m : ℝ) ≤ N + 1 := by exact_mod_cast (by omega : m ≤ N + 1)
      have he : 1 ≤ Real.exp (N + 1) * Real.exp (-(m : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
      have hdreal : (1 : ℝ) ≤ 2 * d := by exact_mod_cast (by omega : 1 ≤ 2 * d)
      have hc : 1 ≤ C * Real.exp (-(m : ℝ)) := by
        calc
          _ ≤ Real.exp (N + 1) * Real.exp (-(m : ℝ)) := he
          _ ≤ (2 * d * Real.exp (N + 1)) * Real.exp (-(m : ℝ)) := by
            gcongr
            nlinarith only [hdreal, Real.exp_pos (N + 1)]
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
      simpa only [Set.compl_empty, measure_univ, one_mul, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal hc
    · intro ω hω
      exact hω.elim

end

end LongRange
