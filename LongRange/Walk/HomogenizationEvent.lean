import LongRange.TwoScale.MainTheorem

/-!
# Almost sure homogenization events

Exponential minimal-scale tails give finite thresholds almost surely. The quantitative
homogenization estimate therefore implies convergence, simultaneously for countably many data.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Euclidean.Lattice

namespace LongRange

/-- An exponential upper tail forces an extended nonnegative minimal scale to be finite. -/
theorem ae_minimalScale_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝒳 : Ω → ENNReal) (C c : ℝ) (hc : 0 < c)
    (htail : ∀ s : ℝ, 1 ≤ s →
      P {ω | ENNReal.ofReal s < 𝒳 ω} ≤ ENNReal.ofReal (C * Real.exp (-(c * s)))) :
    ∀ᵐ ω ∂P, 𝒳 ω < ⊤ := by
  have hlim : Tendsto (fun s : ℝ ↦ ENNReal.ofReal (C * Real.exp (-(c * s))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (C * 0)).comp
        ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop hc)).const_mul C)
  have hzero : P {ω | 𝒳 ω = ⊤} = 0 := by
    apply le_antisymm ?_ bot_le
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (measure_mono (fun ω hω ↦ by
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hω]
      exact ENNReal.ofReal_lt_top)).trans (htail s hs)
  simpa only [ae_iff, not_lt, top_le_iff] using hzero

/-- The logarithmic scale diverges when the positive mesh size tends to zero. -/
lemma tendsto_abs_log_nhdsGT_zero :
    Tendsto (fun ε : ℝ ↦ |Real.log ε|) (𝓝[>] 0) atTop := by
  exact tendsto_atTop_mono (fun ε ↦ neg_le_abs (Real.log ε))
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)

/-- Quantitative homogenization implies almost sure convergence for every solution family. -/
theorem ae_tendsto_discrete_solution
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (d : ℕ) (hd : 1 ≤ d) (lam σ μ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    (U : Set (Fin d → ℝ)) (hU : LatticeProb.Elliptic.IsC2HolderDomain σ U) (M : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (ha : AssumptionU P lam a)
    (f ū : (Fin d → ℝ) → ℝ)
    (hf : LatticeProb.Elliptic.c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M)
    (hū : LatticeProb.Elliptic.IsClassicalDirichletSolution U μ
      (meanConductance P hd a / (2 * d)) f ū) :
    ∀ᵐ ω ∂P, ∀ u : ℝ → Site d → ℝ,
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε U (u ε)) →
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet ε U,
        μ * u ε q - generator ε (a ω) (u ε) q = f (physical ε q)) →
      Tendsto (fun ε ↦ l2Norm ε U (fun q ↦ u ε q - ū (physical ε q)))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, c, _, hc, hmain⟩ :=
    LongRange.main_theorem h619 h66 h37 h637 d hd lam σ μ hσ hμ U hU M
  obtain ⟨𝒳, _, htail, hbound⟩ := hmain P a ha f hf ū hū
  filter_upwards [ae_minimalScale_lt_top P 𝒳 C c hc htail] with ω hω
  intro u hs hu
  have hscale : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 𝒳 ω ≤ ENNReal.ofReal |Real.log ε| := by
    filter_upwards [tendsto_abs_log_nhdsGT_zero.eventually_ge_atTop (𝒳 ω).toReal]
      with ε hε
    rw [← ENNReal.ofReal_toReal hω.ne]
    exact ENNReal.ofReal_le_ofReal hε
  have hmesh : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 from
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds)] with ε hpos hlt
    exact ⟨hpos, hlt⟩
  apply squeeze_zero' (Eventually.of_forall (fun ε ↦ Real.sqrt_nonneg _)) ?_
    ((Real.tendsto_sqrt_atTop.comp tendsto_abs_log_nhdsGT_zero).const_div_atTop C)
  filter_upwards [hscale, hmesh] with ε hε hm
  exact hbound ω ε hm hε (u ε) (hs ε hm) (hu ε hm)

/-- Countably many domains and forcings share one almost sure convergence event. -/
theorem ae_tendsto_discrete_solution_countable
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (d : ℕ) (hd : 1 ≤ d) (lam σ μ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ)
    (ha : AssumptionU P lam a)
    {ι : Type*} [Countable ι] (U : ι → Set (Fin d → ℝ))
    (hU : ∀ i, LatticeProb.Elliptic.IsC2HolderDomain σ (U i)) (M : ι → ℝ)
    (f ū : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ i, LatticeProb.Elliptic.c0HolderNorm σ (closure (U i)) (f i) ≤
      ENNReal.ofReal (M i))
    (hū : ∀ i, LatticeProb.Elliptic.IsClassicalDirichletSolution (U i) μ
      (meanConductance P hd a / (2 * d)) (f i) (ū i)) :
    ∀ᵐ ω ∂P, ∀ i, ∀ u : ℝ → Site d → ℝ,
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε (U i) (u ε)) →
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet ε (U i),
        μ * u ε q - generator ε (a ω) (u ε) q = f i (physical ε q)) →
      Tendsto (fun ε ↦ l2Norm ε (U i) (fun q ↦ u ε q - ū i (physical ε q)))
        (𝓝[>] 0) (𝓝 0) := by
  apply ae_all_iff.mpr
  intro i
  exact ae_tendsto_discrete_solution h619 h66 h37 h637 d hd lam σ μ hσ hμ
    (U i) (hU i) (M i) P a ha (f i) (ū i) (hf i) (hū i)

end LongRange
