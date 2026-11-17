import LongRangeHeat.KallenbergPaired
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weakly optional times

A strictly positive deterministic shift turns a weakly optional time into a
stopping time for the same raw natural filtration.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set
open scoped Topology NNReal

variable {E Ω : Type} [MetricSpace E] [MeasurableSpace E]

/-- A bounded weakly optional time for the raw natural filtration. -/
def weakNaturalStopping (Y : Ω → D E) (H : ℝ) (τ : Ω → Time) : Prop :=
  (∀ w, (τ w : ℝ) ≤ H) ∧
    ∀ t : Time, MeasurableSet[naturalSigma Y t] {w | τ w < t}

/-- The raw natural information is increasing in time. -/
theorem naturalSigma_mono (Y : Ω → D E) {s t : Time} (hst : s ≤ t) :
    naturalSigma Y s ≤ naturalSigma Y t :=
  iSup_le fun u => iSup_le fun hu => le_iSup_of_le u (le_iSup_of_le (hu.trans hst) le_rfl)

/-- A positive deterministic shift of a weakly optional time is a stopping time. -/
theorem weakNaturalStopping.add_pos {Y : Ω → D E} {H : ℝ} {τ : Ω → Time}
    (hτ : weakNaturalStopping Y H τ) {c : Time} (hc : 0 < c) :
    naturalStopping Y (H + (c : ℝ)) (fun w => τ w + c) := by
  constructor
  · intro w
    change (τ w : ℝ) + (c : ℝ) ≤ H + (c : ℝ)
    linarith [hτ.1 w]
  · intro t
    by_cases hct : c ≤ t
    · let r : ℕ → Time := fun k => (t - c) + c / ((k : Time) + 1)
      have hrle (k : ℕ) : r k ≤ t := by
        have hdiv : c / ((k : Time) + 1) ≤ c := by
          apply NNReal.coe_le_coe.mp
          simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
          exact div_le_self c.2 (by linarith [Nat.cast_nonneg (α := ℝ) k])
        calc
          r k ≤ (t - c) + c := by dsimp only [r]; gcongr
          _ = t := tsub_add_cancel_of_le hct
      have hrgt (k : ℕ) : t - c < r k := by
        exact lt_add_of_pos_right _ (div_pos hc (by positivity))
      have hrlim : Tendsto r atTop (𝓝 (t - c)) := by
        apply NNReal.tendsto_coe.mp
        have hh : Tendsto (fun k : ℕ => (c : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
          simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (c : ℝ)
        have hh' : Tendsto (fun k : ℕ => ((t - c : Time) : ℝ) +
            (c : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 (((t - c : Time) : ℝ) + 0)) :=
          tendsto_const_nhds.add hh
        simpa only [r, NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_one,
          mul_one_div, add_zero] using hh'
      have hevent : {w | τ w + c ≤ t} = ⋂ k : ℕ, {w | τ w < r k} := by
        ext w
        simp only [mem_ofPred_eq, mem_iInter]
        constructor
        · intro hw k
          have hle : τ w ≤ t - c := by
            apply NNReal.coe_le_coe.mp
            rw [NNReal.coe_sub hct]
            have hw' : (τ w : ℝ) + (c : ℝ) ≤ t := by exact_mod_cast hw
            linarith
          exact hle.trans_lt (hrgt k)
        · intro hw
          have hle : τ w ≤ t - c :=
            le_of_tendsto_of_tendsto tendsto_const_nhds hrlim
              (Eventually.of_forall fun k => (hw k).le)
          apply NNReal.coe_le_coe.mp
          have hle' : (τ w : ℝ) ≤ (t : ℝ) - c := by
            simpa only [NNReal.coe_sub hct] using (NNReal.coe_le_coe.mpr hle)
          change (τ w : ℝ) + (c : ℝ) ≤ (t : ℝ)
          linarith
      rw [hevent]
      exact MeasurableSet.iInter fun k => naturalSigma_mono Y (hrle k) _ (hτ.2 (r k))
    · have hevent : {w | τ w + c ≤ t} = ∅ := by
        ext w
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le (lt_of_not_ge hct) (le_add_of_nonneg_left zero_le)
      rw [hevent]
      exact @MeasurableSet.empty Ω (naturalSigma Y t)



/-- Adding a nonnegative deterministic time preserves weak optionality. -/
theorem weakNaturalStopping.add_const {Y : Ω → D E} {H : ℝ} {τ : Ω → Time}
    (hτ : weakNaturalStopping Y H τ) (c : Time) :
    weakNaturalStopping Y (H + (c : ℝ)) (fun w => τ w + c) := by
  constructor
  · intro w
    change (τ w : ℝ) + (c : ℝ) ≤ H + (c : ℝ)
    linarith [hτ.1 w]
  · intro t
    by_cases hct : c < t
    · have heq : {w | τ w + c < t} = {w | τ w < t - c} := by
        ext w
        simp only [mem_ofPred_eq]
        have hc : c ≤ t := hct.le
        have hcoe : ((t - c : Time) : ℝ) = (t : ℝ) - c := NNReal.coe_sub hc
        constructor
        · intro h
          have h' : (τ w : ℝ) + (c : ℝ) < t := by exact_mod_cast h
          apply NNReal.coe_lt_coe.mp
          rw [hcoe]
          linarith
        · intro h
          have h' : (τ w : ℝ) < (t : ℝ) - c := by
            rw [← hcoe]
            exact NNReal.coe_lt_coe.mpr h
          apply NNReal.coe_lt_coe.mp
          change (τ w : ℝ) + (c : ℝ) < (t : ℝ)
          linarith
      rw [heq]
      exact naturalSigma_mono Y (tsub_le_self) _ (hτ.2 (t - c))
    · have heq : {w | τ w + c < t} = ∅ := by
        ext w
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (le_of_not_gt hct).trans (le_add_of_nonneg_left zero_le)
      rw [heq]
      exact @MeasurableSet.empty Ω (naturalSigma Y t)

/-- The minimum of two weakly optional times is weakly optional, with the
bound of its first argument. -/
theorem weakNaturalStopping.min_left {Y : Ω → D E} {H K : ℝ} {σ τ : Ω → Time}
    (hσ : weakNaturalStopping Y H σ) (hτ : weakNaturalStopping Y K τ) :
    weakNaturalStopping Y H (fun w => min (σ w) (τ w)) := by
  constructor
  · intro w
    exact (NNReal.coe_le_coe.mpr (min_le_left (σ w) (τ w))).trans (hσ.1 w)
  · intro t
    have heq : {w | min (σ w) (τ w) < t} = {w | σ w < t} ∪ {w | τ w < t} := by
      ext w
      simp only [mem_ofPred_eq, mem_union, min_lt_iff]
    rw [heq]
    exact (hσ.2 t).union (hτ.2 t)

variable [TopologicalSpace.SeparableSpace E] [BorelSpace E]

omit [TopologicalSpace.SeparableSpace E] in
/-- A weakly optional time of a measurable process is measurable. -/
theorem weakNaturalStopping.measurable [MeasurableSpace Ω] {Y : Ω → D E}
    (hY : Measurable Y) {H : ℝ} {τ : Ω → Time} (hτ : weakNaturalStopping Y H τ) :
    Measurable τ := by
  apply measurable_of_Iio
  intro t
  exact naturalSigma_le Y (fun s => (measurable_eval s).comp hY) t _ (hτ.2 t)

variable {Ωs : ℕ → Type} [m : ∀ n, MeasurableSpace (Ωs n)]

/-- The paired expectation bound extends to weakly optional times. -/
theorem exists_pos_eventually_uniform_weak_paired_expectation
    (P : ∀ n, ProbabilityMeasure (Ωs n)) (Y : ∀ n, Ωs n → D E)
    (hY : ∀ n, Measurable (Y n))
    (h : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : (n : ℕ) → Ωs n → Time,
      (∀ n, naturalStopping (Y n) H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) →
      Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (P n : Measure (Ωs n))
          {w | η ≤ dist ((Y n w).1 (τ n w + u n)) ((Y n w).1 (τ n w))})
          atTop (𝓝 0))
    {H ε : ℝ} (hH : 0 < H) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ σ τ : Ωs n → Time, weakNaturalStopping (Y n) H σ →
      weakNaturalStopping (Y n) H τ → (∀ w, σ w ≤ τ w) →
      (∀ w, (τ w : ℝ) ≤ (σ w : ℝ) + δ) →
      (∫ w, boundedDistance ((Y n w).1 (σ w)) ((Y n w).1 (τ w))
        ∂(P n : Measure (Ωs n))) < ε := by
  obtain ⟨δ, hδ, N, hN⟩ := exists_pos_eventually_uniform_paired_expectation P Y hY
    (show 0 < H + 1 by linarith) (h (H + 1) (by linarith)) (show 0 < ε / 2 by linarith)
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn σ τ hσ hτ hστ hnear
  have hs := hσ.measurable (hY n)
  have ht := hτ.measurable (hY n)
  let c : ℕ → Time := fun k => 1 / ((k : Time) + 1)
  have hc (k : ℕ) : 0 < c k := by dsimp [c]; positivity
  have hcle (k : ℕ) : (c k : ℝ) ≤ 1 := by
    dsimp [c]
    simp only [NNReal.coe_natCast]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have htime (t : Time) : Tendsto (fun k => t + c k) atTop (𝓝[Ici t] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun k => show t ≤ t + c k from le_add_of_nonneg_right zero_le⟩
    apply NNReal.tendsto_coe.mp
    have hh : Tendsto (fun k : ℕ => (t : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [c, NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast] using hh
  have hlim : Tendsto (fun k => ∫ w, boundedDistance ((Y n w).1 (σ w + c k))
      ((Y n w).1 (τ w + c k)) ∂(P n : Measure (Ωs n))) atTop
      (𝓝 (∫ w, boundedDistance ((Y n w).1 (σ w)) ((Y n w).1 (τ w))
        ∂(P n : Measure (Ωs n)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro k
      exact (integrable_boundedDistance_stopped (P n) (hY n)
        (hs.add measurable_const) (ht.add measurable_const)).aestronglyMeasurable
    · exact integrable_const 1
    · exact fun k => Eventually.of_forall fun w => norm_boundedDistance_le_one _ _
    · refine Eventually.of_forall fun w => ?_
      exact continuous_boundedDistance.continuousAt.tendsto.comp
        ((((Y n w).2.1 (σ w)).tendsto.comp (htime (σ w))).prodMk_nhds
          (((Y n w).2.1 (τ w)).tendsto.comp (htime (τ w))))
  have hupper (k : ℕ) :
      (∫ w, boundedDistance ((Y n w).1 (σ w + c k)) ((Y n w).1 (τ w + c k))
        ∂(P n : Measure (Ωs n))) ≤ ε / 2 := by
    have hs' : naturalStopping (Y n) (H + 1) (fun w => σ w + c k) := by
      have hh := hσ.add_pos (hc k)
      exact ⟨fun w => by linarith [hh.1 w, hcle k], hh.2⟩
    have ht' : naturalStopping (Y n) (H + 1) (fun w => τ w + c k) := by
      have hh := hτ.add_pos (hc k)
      exact ⟨fun w => by linarith [hh.1 w, hcle k], hh.2⟩
    apply (hN n hn _ _ hs' ht' (fun w => by gcongr; exact hστ w) ?_).le
    intro w
    change (τ w : ℝ) + (c k : ℝ) ≤ ((σ w : ℝ) + (c k : ℝ)) + δ
    linarith [hnear w]
  have hfinal := le_of_tendsto hlim (Eventually.of_forall hupper)
  linarith

end LatticeProb.Cadlag.HalfLine
