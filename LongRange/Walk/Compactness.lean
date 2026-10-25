import LongRange.Walk.Increments
import LongRange.Walk.Marginals
import LatticeProb.Prob.Cadlag.HalfLine.ChainPathLaw
import LatticeProb.External.EthierKurtzSkorokhod

/-!
# Relative compactness of rescaled walk laws

Marginal tightness and the cubic-root increment estimates verify the hypotheses of
Ethier–Kurtz's relative compactness criterion on Euclidean half-line path space.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice MeasureTheory
open LatticeProb.Cadlag.HalfLine
open scoped Topology NNReal ENNReal

noncomputable section

variable {d : ℕ}

/-- Positive physical scaling embeds the lattice injectively in Euclidean space. -/
theorem walkEmbed_injective {ε : ℝ} (hε : 0 < ε) :
    Function.Injective (walkEmbed (d := d) ε) := by
  intro x y h
  apply physical_injective hε
  exact congrArg WithLp.ofLp h

/-- Tight physical initial laws give relatively compact rescaled walk path laws. -/
theorem walk_pathLaws_relativelyCompact (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies)
    (hEK : External.EthierKurtzRelativeCompactness) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (μ : Set.Ioo (0 : ℝ) 1 → Measure (Site d))
    [∀ ε, IsProbabilityMeasure (μ ε)]
    (htight : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ ε,
      μ ε {x | R < radius (physical ε x)} ≤ ENNReal.ofReal η) :
    IsCompact (closure (Set.range (fun ε : Set.Ioo (0 : ℝ) 1 ↦
      pathLaw (walkRates hd ε.2.1 hlam a ha) (μ ε) (walkEmbed ε)))) := by
  haveI : Nonempty (Set.Ioo (0 : ℝ) 1) :=
    Set.nonempty_Ioo_subtype zero_lt_one
  let μ' : ℝ → Measure (Site d) := fun ε ↦
    if h : ε ∈ Set.Ioo (0 : ℝ) 1 then μ ⟨ε, h⟩ else Measure.dirac 0
  haveI : ∀ ε, IsProbabilityMeasure (μ' ε) := by
    intro ε
    dsimp [μ']
    split <;> infer_instance
  have hμ' (ε : Set.Ioo (0 : ℝ) 1) : μ' ε = μ ε := by
    simp only [μ', dif_pos ε.2]
  have htight' : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      μ' ε {x | R < radius (physical ε x)} ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨R, hR⟩ := htight η hη
    exact ⟨R, fun ε hε ↦ by simpa only [hμ' ⟨ε, hε⟩] using hR ⟨ε, hε⟩⟩
  obtain ⟨K, hK, hinc⟩ := walk_increment_condition hMSC hNash hDavies hd hlam a ha
  obtain ⟨K₀, hK₀, hini⟩ := walk_increment_initial hMSC hNash hDavies hd hlam a ha
  refine hEK (EuclideanSpace ℝ (Fin d)) (Set.Ioo (0 : ℝ) 1)
    (fun _ ↦ JumpChain.RegularHistory (Site d)) (fun _ ↦ inferInstance)
    (fun ε ↦ ⟨(walkRates hd ε.2.1 hlam a ha).regularLaw (μ ε), inferInstance⟩)
    (fun ε h ↦ h.halfLinePath (walkEmbed ε))
    (fun ε ↦ measurable_halfLinePath (walkEmbed ε)) ?_ ?_ ?_
  · intro ε t
    exact JumpChain.RegularHistory.measurable_halfLinePath_eval _
      (measurable_of_countable _) t
  · intro η hη t ht
    obtain ⟨R, hR⟩ := walk_marginal_tight hMSC hNash hDavies hd hlam a ha
      μ' htight' (t : ℝ).toNNReal η hη
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall _ _, ?_⟩
    intro ε
    have hb := hR ε ε.2
    rw [hμ' ε] at hb
    have he : {h : JumpChain.RegularHistory (Site d) |
        (h.halfLinePath (walkEmbed ε)).1 (t : ℝ).toNNReal ∈ Metric.closedBall 0 R} =
        {h | R < radius (physical ε (h.position (t : ℝ).toNNReal))}ᶜ := by
      ext h
      simp only [JumpChain.RegularHistory.halfLinePath_apply, Metric.mem_closedBall,
        dist_zero_right, walkEmbed, ← radius_norm, Set.mem_compl_iff,
        Set.mem_setOf_eq, not_lt]
    rw [he, prob_compl_eq_one_sub]
    · rw [ENNReal.ofReal_sub _ hη.le, ENNReal.ofReal_one]
      exact tsub_le_tsub_left hb 1
    · exact (measurable_of_countable (fun x : Site d ↦
        radius (physical ε x))).comp
          (JumpChain.RegularHistory.measurable_position _) measurableSet_Ioi
  · intro T hT
    refine ⟨1, zero_lt_one,
      (fun _ δ _ ↦ (δ ^ (1 / 3 : ℝ) + K * δ ^ (1 / 3 : ℝ) *
        (1 + Real.log 3)).toNNReal), (fun _ _ _ _ ↦ measurable_const), ?_, ?_, ?_⟩
    · intro ε δ hδ hδ1 t u v ht hu hv
      rw [naturalSigma_halfLinePath_eq _ (walkEmbed_injective ε.2.1)]
      have hp (s r : Time) :
          incrementPower (fun h : JumpChain.RegularHistory (Site d) ↦
            h.halfLinePath (walkEmbed ε)) 1 s r =
            (fun h ↦ ENNReal.ofReal (min (dist (walkEmbed ε (h.position s))
              (walkEmbed ε (h.position r))) 1)) := by
        funext h
        simp only [incrementPower, Real.rpow_one,
          JumpChain.RegularHistory.halfLinePath_apply]
      simp only [hp, ProbabilityMeasure.coe_mk]
      change ∀ᵐ w ∂(walkRates hd ε.2.1 hlam a ha).regularLaw (μ ε),
        ((walkRates hd ε.2.1 hlam a ha).regularLaw (μ ε))⁻[fun h ↦
          ENNReal.ofReal (min (dist (walkEmbed ε (h.position (t + u)))
            (walkEmbed ε (h.position t))) 1) |
              JumpChain.BoundedRates.naturalSigma t] w *
          ENNReal.ofReal (min (dist (walkEmbed ε (w.position t))
            (walkEmbed ε (w.position (t - v)))) 1) ≤
          ((walkRates hd ε.2.1 hlam a ha).regularLaw (μ ε))⁻[fun _ ↦
            ENNReal.ofReal (δ ^ (1 / 3 : ℝ) +
              K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) |
                JumpChain.BoundedRates.naturalSigma t] w
      have hc := hinc ε ε.2 (μ ε) t u δ hδ hδ1 hu
      rw [condLExp_const (JumpChain.BoundedRates.naturalSigma_le t)]
      filter_upwards [hc] with w hw
      exact (mul_le_of_le_one_right' (show ENNReal.ofReal
        (min (dist (walkEmbed ε (w.position t))
          (walkEmbed ε (w.position (t - v)))) 1) ≤ 1 from
            (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans_eq
              ENNReal.ofReal_one)).trans hw
    · simpa only [ENNReal.ofReal, lintegral_const, measure_univ, mul_one,
        iSup_const] using walk_increment_bound_ofReal_tendsto K
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds (walk_increment_bound_ofReal_tendsto K₀)
        (Filter.Eventually.of_forall fun _ ↦ zero_le) ?_
      filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < 1 from
          (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds)] with δ hδ hδ1
      apply iSup_le
      intro ε
      simpa only [incrementPower, Real.rpow_one, ProbabilityMeasure.coe_mk,
        JumpChain.RegularHistory.halfLinePath_apply] using
        hini ε ε.2 (μ ε) δ.toNNReal δ hδ hδ1 (by
          rw [Real.coe_toNNReal _ hδ.le])

end

end LongRange
