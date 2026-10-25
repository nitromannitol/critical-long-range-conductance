import LongRange.Walk.FddConvergence

/-!
# Quenched invariance principle

Relative compactness of the walk path laws, tightness of their time marginals, and convergence
of positive-time product tests give weak convergence of the path laws along every null
sequence of scales. The sequential criterion then gives convergence along the epsilon filter.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Cadlag.HalfLine
open scoped NNReal ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- Along any sequence of scales, the walk path laws from the canonical initial laws have
relatively compact range. -/
theorem walk_pathLaws_seq_isCompact (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (hEK : External.EthierKurtzRelativeCompactness) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1) (hgc : HasCompactSupport g)
    (ε : ℕ → Eps) :
    IsCompact (closure (Set.range (fun n => pathLaw (walkRates hd (ε n).property.1 hlam a ha)
      (initialLaw (ε n).val g (ε n).property.1 hg hg0 hg1 : Measure (Site d))
        (walkEmbed (ε n).val)))) := by
  have hK := walk_pathLaws_relativelyCompact hMSC hNash hDavies hEK hd hlam a ha
    (fun ε => (initialLaw ε.val g ε.2.1 hg hg0 hg1 : Measure (Site d)))
    (fun η hη => by
      obtain ⟨R, hR⟩ := initialLaw_tight g hg hg0 hg1 hgc η hη
      exact ⟨R, fun ε => hR ε.val ε.2⟩)
  refine hK.of_isClosed_subset isClosed_closure (closure_mono ?_)
  rintro _ ⟨n, rfl⟩
  exact ⟨ε n, rfl⟩

/-- Along any sequence of scales, each time marginal of the walk path laws is tight. -/
theorem walk_marginals_isTight (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1) (hgc : HasCompactSupport g)
    (ε : ℕ → Eps) (t : Time) :
    IsTightMeasureSet {Measure.map (fun w : D (EuclideanSpace ℝ (Fin d)) => w.1 t)
      (pathLaw (walkRates hd (ε n).property.1 hlam a ha)
        (initialLaw (ε n).val g (ε n).property.1 hg hg0 hg1 : Measure (Site d))
          (walkEmbed (ε n).val) : Measure (D (EuclideanSpace ℝ (Fin d)))) | n} := by
  classical
  let μ' : ℝ → Measure (Site d) := fun ε =>
    if h : 0 < ε then (initialLaw ε g h hg hg0 hg1 : Measure (Site d)) else Measure.dirac 0
  haveI : ∀ ε, IsProbabilityMeasure (μ' ε) := by
    intro ε
    dsimp only [μ']
    split <;> infer_instance
  have hμ' (ε : ℝ) (h : 0 < ε) : μ' ε = (initialLaw ε g h hg hg0 hg1 : Measure (Site d)) :=
    dif_pos h
  have htight : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      μ' ε {x | R < radius (physical ε x)} ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨R, hR⟩ := initialLaw_tight g hg hg0 hg1 hgc η hη
    exact ⟨R, fun ε hε => by rw [hμ' ε hε.1]; exact hR ε hε⟩
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  by_cases htop : η = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => htop ▸ le_top⟩
  have hη' : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨R, hR⟩ := walk_marginal_tight hMSC hNash hDavies hd hlam a ha μ' htight t
    η.toReal hη'
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hn := hR (ε n).val (ε n).property
  rw [hμ' _ (ε n).property.1, ENNReal.ofReal_toReal htop] at hn
  rw [Measure.map_apply (measurable_eval t) Metric.isClosed_closedBall.measurableSet.compl,
    pathLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_halfLinePath _)
      ((measurable_eval t) Metric.isClosed_closedBall.measurableSet.compl)]
  convert hn using 2
  · rfl
  · ext h
    simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      not_le, JumpChain.RegularHistory.halfLinePath_apply, walkEmbed, ← radius_norm,
      Set.mem_setOf_eq]

/-- The quenched invariance principle for any spatial amplitude equal to `sqrt (2 a₀)`. -/
theorem ae_tendsto_walk_pathLaw
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hTK : External.EthierKurtzTrotterKato)
    (hRC : External.EthierKurtzRelativeCompactness)
    (hFdd : External.EthierKurtzConvergenceFromFdd)
    (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hU : AssumptionU P lam a)
    (g : (Fin d → ℝ) → ℝ) (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) (hgc : HasCompactSupport g) (hg1 : ∫ x, g x = 1)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) (s : ℝ)
    (hs : s = Real.sqrt (2 * (meanConductance P hd a / (2 * (d : ℝ))))) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun ε : Eps => pathLaw
          (walkRates hd ε.property.1 hU.lam_pos (a ω) (hU.bounds ω))
          (initialLaw ε.val g ε.property.1 (integrable_initial_density hg hgc) hg0 hg1 :
            Measure (Site d))
          (walkEmbed ε.val))
        epsFilter
        (𝓝 (ProbabilityMeasure.map
          (⟨(initialDensityEuclidean g (integrable_initial_density hg hgc) hg0 hg1 :
            Measure (EuclideanSpace ℝ (Fin d))).prod (B : Measure (BrownianPath d)),
              inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × BrownianPath d))
          (measurable_brownianMixturePath (d := d) s).aemeasurable)) := by
  subst hs
  filter_upwards [ae_tendsto_walk_productTests hTK h619 h66 h37 h637 h614 hd P a hU
    g hg hg0 hgc hg1 B hB] with ξ hξ
  apply tendsto_epsFilter_of_sequences
  intro ε hε
  apply tendsto_of_relativelyCompact_productTests hFdd
  · exact walk_pathLaws_seq_isCompact hMSC hNash hDavies hRC hd hU.lam_pos (a ξ) (hU.bounds ξ)
      g _ hg0 hg1 hgc ε
  · exact walk_marginals_isTight hMSC hNash hDavies hd hU.lam_pos (a ξ) (hU.bounds ξ)
      g _ hg0 hg1 hgc ε
  · intro m ss hss hpos φ
    exact hξ ε hε ss hss hpos φ

/-- Theorem 6.2 (`t.qip`), with the initial position and Brownian motion independent. -/
theorem quenched_invariance_principle_of_cited
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hTK : External.EthierKurtzTrotterKato)
    (hRC : External.EthierKurtzRelativeCompactness)
    (hFdd : External.EthierKurtzConvergenceFromFdd)
    (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (d : ℕ) (hd : 1 ≤ d) (lam : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hU : AssumptionU P lam a)
    (g : (Fin d → ℝ) → ℝ) (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) (hgc : HasCompactSupport g)
    (hg1 : ∫ x, g x = 1)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
  let ρ := Measure.map (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
    (volume.withDensity (fun x => ENNReal.ofReal (g x)))
  let s := Real.sqrt (2 * (meanConductance P hd a / (2 * (d : ℝ))))
  let F : EuclideanSpace ℝ (Fin d) × BrownianPath d →
      D (EuclideanSpace ℝ (Fin d)) := fun p =>
    D.ofContinuous ⟨(fun t => p.1 + s • p.2 t),
      continuous_const.add (p.2.continuous.const_smul s)⟩
  ∃ ρp : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), (ρp : Measure _) = ρ ∧
    ∃ hF : Measurable F,
      ∀ᵐ ω ∂P,
        Tendsto
          (fun ε : Eps => pathLaw
            (walkRates hd ε.property.1 hU.lam_pos (a ω) (hU.bounds ω))
            (initialLaw ε.val g ε.property.1 (integrable_initial_density hg hgc) hg0 hg1 :
              Measure (Site d))
            (walkEmbed ε.val))
          epsFilter
          (𝓝 (ProbabilityMeasure.map
            (⟨(ρp : Measure _).prod (B : Measure (BrownianPath d)),
            inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × BrownianPath d))
              hF.aemeasurable)) := by
  intro ρ s F
  refine ⟨initialDensityEuclidean g (integrable_initial_density hg hgc) hg0 hg1, rfl,
    measurable_brownianMixturePath (d := d) s, ?_⟩
  exact ae_tendsto_walk_pathLaw h619 h66 h37 h637 h614 hTK hRC hFdd hMSC hNash hDavies hd P a hU
    g hg hg0 hgc hg1 B hB s rfl

/-- Theorem 1.2 (`t.walk.intro`): the amplitude `sqrt (ā / d)` equals `sqrt (2 σ̄²)`. -/
theorem quenched_invariance_principle_intro_of_cited
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hTK : External.EthierKurtzTrotterKato)
    (hRC : External.EthierKurtzRelativeCompactness)
    (hFdd : External.EthierKurtzConvergenceFromFdd)
    (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (d : ℕ) (hd : 1 ≤ d) (lam : ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hU : AssumptionU P lam a)
    (g : (Fin d → ℝ) → ℝ) (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) (hgc : HasCompactSupport g)
    (hg1 : ∫ x, g x = 1)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
  let ρ := Measure.map (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
    (volume.withDensity (fun x => ENNReal.ofReal (g x)))
  let s := Real.sqrt (meanConductance P hd a / (d : ℝ))
  let F : EuclideanSpace ℝ (Fin d) × BrownianPath d →
      D (EuclideanSpace ℝ (Fin d)) := fun p =>
    D.ofContinuous ⟨(fun t => p.1 + s • p.2 t),
      continuous_const.add (p.2.continuous.const_smul s)⟩
  ∃ ρp : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)), (ρp : Measure _) = ρ ∧
    ∃ hF : Measurable F,
      ∀ᵐ ω ∂P,
        Tendsto
          (fun ε : Eps => pathLaw
            (walkRates hd ε.property.1 hU.lam_pos (a ω) (hU.bounds ω))
            (initialLaw ε.val g ε.property.1 (integrable_initial_density hg hgc) hg0 hg1 :
              Measure (Site d))
            (walkEmbed ε.val))
          epsFilter
          (𝓝 (ProbabilityMeasure.map
            (⟨(ρp : Measure _).prod (B : Measure (BrownianPath d)),
            inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × BrownianPath d))
              hF.aemeasurable)) := by
  intro ρ s F
  refine ⟨initialDensityEuclidean g (integrable_initial_density hg hgc) hg0 hg1, rfl,
    measurable_brownianMixturePath (d := d) s, ?_⟩
  have hs : s = Real.sqrt (2 * (meanConductance P hd a / (2 * (d : ℝ)))) := by
    show Real.sqrt (meanConductance P hd a / (d : ℝ)) = _
    rw [← mul_div_assoc, mul_div_mul_left _ _ two_ne_zero]
  exact ae_tendsto_walk_pathLaw h619 h66 h37 h637 h614 hTK hRC hFdd hMSC hNash hDavies hd P a hU
    g hg hg0 hgc hg1 B hB s hs

end

end LongRange
