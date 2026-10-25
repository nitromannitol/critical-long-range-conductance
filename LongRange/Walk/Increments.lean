import LongRange.Walk.DisplacementTail
import LatticeProb.Prob.JumpChain.IncrementBound

/-!
# Truncated increments of the rescaled walk

The Euclidean embedding transports the displacement tail to the conditional increment
estimate. The cubic-root cutoff also controls the initial increment and vanishes at zero.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice MeasureTheory
open scoped NNReal ENNReal

noncomputable section

variable {d : ℕ}

/-- The physical lattice embedded in Euclidean space with its Euclidean metric. -/
def walkEmbed (ε : ℝ) (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (physical ε x)

/-- Distance in the physical embedding is exactly the Euclidean displacement radius. -/
theorem dist_walkEmbed (ε : ℝ) (y x : Site d) :
    dist (walkEmbed ε y) (walkEmbed ε x) =
      radius (physical ε y - physical ε x) := by
  rw [dist_eq_norm, walkEmbed, walkEmbed, ← WithLp.toLp_sub, ← radius_norm]

/-- The displacement tail gives the uniform conditional increment condition (8.33). -/
theorem walk_increment_condition (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (μ : Measure (Site d)) [IsProbabilityMeasure μ] (t u : ℝ≥0)
      (δ : ℝ), 0 < δ → δ < 1 → (u : ℝ) ≤ δ →
      ((walkRates hd hε.1 hlam a ha).regularLaw μ)⁻[fun h ↦ ENNReal.ofReal
        (min (dist (walkEmbed ε (h.position (t + u)))
          (walkEmbed ε (h.position t))) 1) | JumpChain.BoundedRates.naturalSigma t]
        ≤ᵐ[(walkRates hd hε.1 hlam a ha).regularLaw μ] fun _ ↦ ENNReal.ofReal
          (δ ^ (1 / 3 : ℝ) + K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) := by
  obtain ⟨K, hK, htail⟩ := walk_displacement_tail hMSC hNash hDavies hd hlam a ha
  refine ⟨K, hK.le, ?_⟩
  intro ε hε μ inst t u δ hδ hδ1 hu
  apply JumpChain.BoundedRates.condLExp_increment_cutoff_le
    (walkRates hd hε.1 hlam a ha) (walkEmbed ε)
    (fun u η ↦ K * u * (1 + Real.log (2 + η)) / η ^ 2) ?_ hK.le
    (fun _ _ _ ↦ le_rfl) μ t u hδ hδ1 hu
  intro v x η hη
  simpa only [dist_walkEmbed] using htail ε hε v x η hη

/-- The initial truncated increment satisfies the same uniform cubic-root bound. -/
theorem walk_increment_initial (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (μ : Measure (Site d)) [IsProbabilityMeasure μ] (u : ℝ≥0)
      (δ : ℝ), 0 < δ → δ < 1 → (u : ℝ) ≤ δ →
      (∫⁻ h, ENNReal.ofReal (min (dist (walkEmbed ε (h.position u))
        (walkEmbed ε (h.position 0))) 1)
        ∂(walkRates hd hε.1 hlam a ha).regularLaw μ) ≤ ENNReal.ofReal
          (δ ^ (1 / 3 : ℝ) + K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)) := by
  obtain ⟨K, hK, htail⟩ := walk_displacement_tail hMSC hNash hDavies hd hlam a ha
  refine ⟨K, hK.le, ?_⟩
  intro ε hε μ inst u δ hδ hδ1 hu
  let β : ℝ≥0 → ℝ → ℝ := fun v η ↦ K * v * (1 + Real.log (2 + η)) / η ^ 2
  have ht : ∀ v x η, 0 < η →
      (walkRates hd hε.1 hlam a ha).transitionKernel v x
        {y | η < dist (walkEmbed ε y) (walkEmbed ε x)} ≤ ENNReal.ofReal (β v η) := by
    intro v x η hη
    simpa only [dist_walkEmbed] using htail ε hε v x η hη
  have hb := JumpChain.BoundedRates.lintegral_increment_le
    (walkRates hd hε.1 hlam a ha) (walkEmbed ε) β ht μ 0 u
    (Real.rpow_pos_of_pos hδ (1 / 3 : ℝ))
  simp only [zero_add] at hb
  exact hb.trans (JumpChain.BoundedRates.increment_cutoff_le β hK.le
    (fun _ _ _ ↦ le_rfl) hδ hδ1 u hu)

/-- The deterministic bound for the initial and conditional increments vanishes at zero. -/
theorem walk_increment_bound_tendsto (K : ℝ) :
    Filter.Tendsto (fun δ : ℝ ↦ δ ^ (1 / 3 : ℝ) +
      K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  JumpChain.BoundedRates.tendsto_increment_cutoff K

/-- The extended nonnegative real bound used for expectations also tends to zero. -/
theorem walk_increment_bound_ofReal_tendsto (K : ℝ) :
    Filter.Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (δ ^ (1 / 3 : ℝ) +
      K * δ ^ (1 / 3 : ℝ) * (1 + Real.log 3)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa only [ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (walk_increment_bound_tendsto K)


end

end LongRange
