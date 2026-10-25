import LongRange.Walk.DisplacementTail
import LatticeProb.Prob.JumpChain.PositionLaw

/-!
# Marginal tails of the rescaled walk

The displacement estimate and the initial tail bound control each one-time marginal.
Uniform tightness of the physical initial laws therefore persists at each fixed time.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice MeasureTheory
open scoped NNReal ENNReal

variable {d : ℕ}

/-- The singleton position-law identity extends to every measurable set. -/
theorem regularLaw_position_set (rates : JumpChain.BoundedRates (Site d))
    (μ : Measure (Site d)) [IsProbabilityMeasure μ] (t : ℝ≥0) (s : Set (Site d)) :
    rates.regularLaw μ {h | h.position t ∈ s} =
      ∫⁻ x, rates.transitionKernel t x s ∂μ := by
  have hm := JumpChain.RegularHistory.measurable_position (S := Site d) t
  have he : (rates.regularLaw μ).map (fun h ↦ h.position t) =
      μ.bind (rates.transitionKernel t) := by
    apply Measure.ext_of_singleton
    intro j
    rw [Measure.map_apply hm (measurableSet_singleton j)]
    exact rates.regularLaw_position μ t j
  calc
    _ = ((rates.regularLaw μ).map (fun h ↦ h.position t)) s :=
      (Measure.map_apply hm (Set.to_countable s).measurableSet).symm
    _ = _ := by
      rw [he, Measure.bind_apply (Set.to_countable s).measurableSet (by fun_prop)]

/-- A marginal tail is bounded by the initial tail and the displacement tail. -/
theorem walk_marginal_tail (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (μ : Measure (Site d)) [IsProbabilityMeasure μ] (t : ℝ≥0) (R : ℝ), 0 < R →
      (walkRates hd hε.1 hlam a ha).regularLaw μ
          {h | R < radius (physical ε (h.position t))} ≤
        μ {x | R / 2 < radius (physical ε x)} +
          ENNReal.ofReal (C * t * (1 + Real.log (2 + R / 2)) / (R / 2) ^ 2) := by
  obtain ⟨C, hC, htail⟩ := walk_displacement_tail hMSC hNash hDavies hd hlam a ha
  refine ⟨C, hC, ?_⟩
  intro ε hε μ inst t R hR
  change 0 < ε ∧ ε < 1 at hε
  let s : Set (Site d) := {x | R / 2 < radius (physical ε x)}
  let B := ENNReal.ofReal (C * t * (1 + Real.log (2 + R / 2)) / (R / 2) ^ 2)
  calc
    _ = ∫⁻ x, (walkRates hd hε.1 hlam a ha).transitionKernel t x
        {y | R < radius (physical ε y)} ∂μ :=
      regularLaw_position_set (walkRates hd hε.1 hlam a ha) μ t
        {y | R < radius (physical ε y)}
    _ ≤ ∫⁻ x, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x + B ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ s
      · simp only [Set.indicator_of_mem hx]
        exact (prob_le_one).trans (le_add_right le_rfl)
      · rw [Set.indicator_of_notMem hx, zero_add]
        apply le_trans (measure_mono ?_) (htail ε hε t x (R / 2) (by linarith))
        intro y hy
        have hdif := (le_abs_self _).trans (radius_difference (physical ε y) (physical ε x))
        have hx' : radius (physical ε x) ≤ R / 2 := le_of_not_gt hx
        change R / 2 < radius (physical ε y - physical ε x)
        change R < radius (physical ε y) at hy
        linarith
    _ = μ s + B := by
      rw [lintegral_add_left (by fun_prop), lintegral_indicator
        (Set.to_countable s).measurableSet]
      simp

/-- Uniform tightness of physical initial laws persists at each fixed time. -/
theorem walk_marginal_tight (hMSC : External.MuruganSaloffCoste)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (hd : 1 ≤ d) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (μ : ℝ → Measure (Site d)) [∀ ε, IsProbabilityMeasure (μ ε)]
    (htight : ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      μ ε {x | R < radius (physical ε x)} ≤ ENNReal.ofReal η)
    (t : ℝ≥0) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
      (walkRates hd hε.1 hlam a ha).regularLaw (μ ε)
        {h | R < radius (physical ε (h.position t))} ≤ ENNReal.ofReal η := by
  obtain ⟨C, hC, htail⟩ := walk_marginal_tail hMSC hNash hDavies hd hlam a ha
  obtain ⟨R₀, hR₀⟩ := htight (η / 2) (by linarith)
  let r := max R₀ (max 1 (6 * (C * (t : ℝ)) / η))
  have hr₀ : R₀ ≤ r := le_max_left _ _
  have hr₁ : 1 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hrC : 6 * (C * (t : ℝ)) / η ≤ r :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr₁
  have hCt : 0 ≤ C * (t : ℝ) := mul_nonneg hC.le t.coe_nonneg
  have hlog : 1 + Real.log (2 + r) ≤ 3 * r := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + r by linarith)
    linarith
  have hsmall : C * (t : ℝ) * (1 + Real.log (2 + r)) / r ^ 2 ≤ η / 2 := by
    have hprod : 6 * (C * (t : ℝ)) ≤ r * η := (div_le_iff₀ hη).mp hrC
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    have hmul := mul_le_mul_of_nonneg_left hlog hCt
    have hprod' := mul_le_mul_of_nonneg_right hprod hr.le
    nlinarith
  refine ⟨2 * r, ?_⟩
  intro ε hε
  change 0 < ε ∧ ε < 1 at hε
  have hb := htail ε hε (μ ε) t (2 * r) (by positivity)
  have hhalf : 2 * r / 2 = r := by ring
  rw [hhalf] at hb
  calc
    _ ≤ μ ε {x | r < radius (physical ε x)} +
        ENNReal.ofReal (C * t * (1 + Real.log (2 + r)) / r ^ 2) := hb
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
      apply add_le_add _ (ENNReal.ofReal_le_ofReal hsmall)
      exact (measure_mono (fun x hx ↦ lt_of_le_of_lt hr₀ hx)).trans (hR₀ ε hε)
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end LongRange
