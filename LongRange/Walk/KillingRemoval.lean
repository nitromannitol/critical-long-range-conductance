import LongRange.Walk.InitialLaw
import LongRange.Walk.Compactness
import LatticeProb.Prob.BrownianDirichlet.LargeBallExit

/-!
# Removal of killing

Bounded observables differ from their killed versions by at most the bound times
exit probability. Vanishing limiting exit probabilities therefore remove killing.
-/

namespace LongRange

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-- Killing a bounded observable changes its expectation by at most the exit mass. -/
theorem abs_integral_sub_killed_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → ℝ} {C : ℝ}
    (hZ : Measurable Z) (hbound : ∀ x, |Z x| ≤ C)
    {A : Set Ω} (hA : MeasurableSet A) :
    |(∫ x, Z x ∂μ) - ∫ x, A.indicator Z x ∂μ| ≤ C * μ.real Aᶜ := by
  have hi : Integrable Z μ :=
    Integrable.of_bound hZ.aestronglyMeasurable C
      (ae_of_all μ (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  rw [integral_indicator hA, ← integral_add_compl hA hi, add_sub_cancel_left]
  simpa only [Real.norm_eq_abs] using
    norm_setIntegral_le_of_norm_le_const_ae (f := Z) (C := C) (measure_lt_top μ Aᶜ)
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hbound x))

/-- Convergent killed expectations and vanishing limiting exit errors imply convergence. -/
theorem limsup_product_le_of_killed {ι : Type*} {l : Filter ι}
    {f : ι → ℝ} {b : ℝ} {k p : ℕ → ι → ℝ} {q r : ℕ → ℝ}
    {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ R i, |f i - k R i| ≤ C * p R i)
    (hb : ∀ R, |b - q R| ≤ C * r R)
    (hk : ∀ R, Tendsto (k R) l (𝓝 (q R)))
    (hp : ∀ R, Tendsto (p R) l (𝓝 (r R)))
    (hr : Tendsto r atTop (𝓝 0)) : Tendsto f l (𝓝 b) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hz : Tendsto (fun R => 2 * C * r R) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr.const_mul (2 * C)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hz.eventually (gt_mem_nhds (by linarith :
    (0 : ℝ) < ε / 2)))
  have hh := ((hp R).const_mul C).add
    (((hk R).sub (tendsto_const_nhds (x := q R))).abs)
  have he : ∀ᶠ i in l, C * p R i + |k R i - q R| < C * r R + ε / 2 := by
    have hgap : C * r R + |q R - q R| < C * r R + ε / 2 := by
      simp only [sub_self, abs_zero, add_zero]
      linarith
    exact hh.eventually (gt_mem_nhds hgap)
  filter_upwards [he] with i hi
  rw [Real.dist_eq]
  have ht : |f i - b| ≤ |f i - k R i| + |k R i - q R| + |q R - b| := by
    calc
      _ = |(f i - k R i) + (k R i - q R) + (q R - b)| := by congr 1; ring
      _ ≤ |(f i - k R i) + (k R i - q R)| + |q R - b| :=
        abs_add_le _ _
      _ ≤ _ := add_le_add (abs_add_le (f i - k R i) (k R i - q R)) le_rfl
  have hb' := hb R
  rw [abs_sub_comm b] at hb'
  have hsmall := hR R le_rfl
  linarith [hf R i]

/-- Convergence of killed constant-one tests gives convergence of exit probabilities. -/
theorem tendsto_exit_probability_of_killed_one {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {l : Filter ι}
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {A : Set Ω} {B : Set Ω'} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : Tendsto (fun i => ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ i) l
      (𝓝 (∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂ν))) :
    Tendsto (fun i => (μ i).real Aᶜ) l (𝓝 (ν.real Bᶜ)) := by
  have he (i : ι) : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ i) =
      (μ i).real A := integral_indicator_one hA
  have heB : (∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂ν) =
      ν.real B := integral_indicator_one hB
  simp only [he, heB] at h
  simpa only [probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hB] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- Removal of killing for probability laws on possibly different measurable spaces. -/
theorem tendsto_integral_of_killed {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {l : Filter ι}
    (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Z : Ω → ℝ) (W : Ω' → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hZ : Measurable Z) (hW : Measurable W)
    (hZC : ∀ x, |Z x| ≤ C) (hWC : ∀ x, |W x| ≤ C)
    (A : ℕ → Set Ω) (B : ℕ → Set Ω')
    (hA : ∀ R, MeasurableSet (A R)) (hB : ∀ R, MeasurableSet (B R))
    (hk : ∀ R, Tendsto (fun i => ∫ x, (A R).indicator Z x ∂μ i) l
      (𝓝 (∫ x, (B R).indicator W x ∂ν)))
    (hp : ∀ R, Tendsto (fun i => (μ i).real (A R)ᶜ) l (𝓝 (ν.real (B R)ᶜ)))
    (hr : Tendsto (fun R => ν.real (B R)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ x, Z x ∂μ i) l (𝓝 (∫ x, W x ∂ν)) := by
  exact limsup_product_le_of_killed hC
    (fun R i => abs_integral_sub_killed_le (μ i) hZ hZC (hA R))
    (fun R => abs_integral_sub_killed_le ν hW hWC (hB R)) hk hp hr

/-- The continuous-path mixture supplies the vanishing exit error automatically. -/
theorem tendsto_integral_of_killed_largeBall {ι Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {l : Filter ι} (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)]
    (ρ : Measure (LatticeProb.Euc d)) [IsProbabilityMeasure ρ]
    (β : Measure (LatticeProb.BrownianPath d)) [IsProbabilityMeasure β]
    (s : ℝ) (T : ℝ≥0) (Z : Ω → ℝ)
    (W : LatticeProb.Euc d × LatticeProb.BrownianPath d → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hZ : Measurable Z) (hW : Measurable W)
    (hZC : ∀ x, |Z x| ≤ C) (hWC : ∀ x, |W x| ≤ C)
    (A : ℕ → Set Ω) (hA : ∀ R, MeasurableSet (A R))
    (hk : ∀ R, Tendsto (fun i => ∫ x, (A R).indicator Z x ∂μ i) l
      (𝓝 (∫ p, {p | (T : ℝ≥0∞) < LatticeProb.scaledExit
        (Metric.ball 0 (R : ℝ)) s p.1 p.2}.indicator W p ∂ρ.prod β)))
    (hp : ∀ R, Tendsto (fun i => (μ i).real (A R)ᶜ) l
      (𝓝 ((ρ.prod β).real {p | LatticeProb.scaledExit
        (Metric.ball 0 (R : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)}))) :
    Tendsto (fun i => ∫ x, Z x ∂μ i) l (𝓝 (∫ p, W p ∂ρ.prod β)) := by
  let B : ℕ → Set (LatticeProb.Euc d × LatticeProb.BrownianPath d) :=
    fun R => {p | (T : ℝ≥0∞) < LatticeProb.scaledExit
      (Metric.ball 0 (R : ℝ)) s p.1 p.2}
  have hB (R : ℕ) : MeasurableSet (B R) :=
    measurableSet_lt measurable_const
      (LatticeProb.measurable_scaledExit_joint Metric.isOpen_ball s)
  have he (R : ℕ) : (B R)ᶜ = {p | LatticeProb.scaledExit
      (Metric.ball 0 (R : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)} := by
    ext p
    simp only [B, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  apply tendsto_integral_of_killed μ (ρ.prod β) Z W hC hZ hW hZC hWC A B hA hB hk
  · simpa only [he] using hp
  · simp only [he, Measure.real]
    exact (ENNReal.continuousAt_toReal (by simp)).tendsto.comp
      (LatticeProb.tendsto_exit_largeBall ρ β s T)

open LatticeProb LatticeProb.Euclidean.Lattice LatticeProb.Cadlag.HalfLine

/-- Killed walk expectations from the cell-average initial law determine full expectations.
The survival event is evaluated on the actual jump history, including the endpoint `T`.
The continuous mixture is evaluated on the independent initial point and Brownian path. -/
theorem tendsto_walk_integral_of_killed_largeBall {d : ℕ} (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1)
    (β : Measure (BrownianPath d)) [IsProbabilityMeasure β] (s : ℝ) (T : ℝ≥0)
    (Z : D (EuclideanSpace ℝ (Fin d)) → ℝ)
    (W : Euc d × BrownianPath d → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hZ : Measurable Z) (hW : Measurable W)
    (hZC : ∀ x, |Z x| ≤ C) (hWC : ∀ x, |W x| ≤ C)
    (l : Filter (Set.Ioo (0 : ℝ) 1))
    (hk : ∀ R : ℕ, Tendsto (fun ε : Set.Ioo (0 : ℝ) 1 =>
      ∫ h, {h : JumpChain.RegularHistory (Site d) | ∀ t ≤ T,
        walkEmbed ε (h.position t) ∈ Metric.ball 0 (R : ℝ)}.indicator
          (fun h => Z (h.halfLinePath (walkEmbed ε))) h
        ∂(walkRates hd ε.2.1 hlam a ha).regularLaw
          (initialLaw ε g ε.2.1 hg hg0 hg1)) l
      (𝓝 (∫ p, {p | (T : ℝ≥0∞) < scaledExit
        (Metric.ball 0 (R : ℝ)) s p.1 p.2}.indicator W p
          ∂(initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β)))
    (hp : ∀ R : ℕ, Tendsto (fun ε : Set.Ioo (0 : ℝ) 1 =>
      ((walkRates hd ε.2.1 hlam a ha).regularLaw
        (initialLaw ε g ε.2.1 hg hg0 hg1)).real
          {h | ∀ t ≤ T, walkEmbed ε (h.position t) ∈ Metric.ball 0 (R : ℝ)}ᶜ) l
      (𝓝 (((initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β).real
        {p | scaledExit (Metric.ball 0 (R : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)}))) :
    Tendsto (fun ε : Set.Ioo (0 : ℝ) 1 =>
      ∫ x, Z x ∂(pathLaw (walkRates hd ε.2.1 hlam a ha)
        (initialLaw ε g ε.2.1 hg hg0 hg1) (walkEmbed ε) :
          Measure (D (EuclideanSpace ℝ (Fin d))))) l
      (𝓝 (∫ p, W p
        ∂(initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β)) := by
  have hA (ε : Set.Ioo (0 : ℝ) 1) (R : ℕ) : MeasurableSet
      {h : JumpChain.RegularHistory (Site d) | ∀ t ≤ T,
        walkEmbed ε (h.position t) ∈ Metric.ball 0 (R : ℝ)} :=
    JumpChain.BoundedRates.naturalSigma_le T _
      (JumpChain.BoundedRates.measurableSet_survival_naturalSigma
        ((walkEmbed ε) ⁻¹' Metric.ball 0 (R : ℝ)) T)
  -- The observable depends on the scale, so use its uniform bound at each scale.
  apply limsup_product_le_of_killed hC (k := fun R (ε : Set.Ioo (0 : ℝ) 1) =>
    ∫ h, {h : JumpChain.RegularHistory (Site d) | ∀ t ≤ T,
      walkEmbed ε (h.position t) ∈ Metric.ball 0 (R : ℝ)}.indicator
        (fun h => Z (h.halfLinePath (walkEmbed ε))) h
      ∂(walkRates hd ε.2.1 hlam a ha).regularLaw
        (initialLaw ε g ε.2.1 hg hg0 hg1))
    (p := fun R (ε : Set.Ioo (0 : ℝ) 1) => ((walkRates hd ε.2.1 hlam a ha).regularLaw
      (initialLaw ε g ε.2.1 hg hg0 hg1)).real
        {h | ∀ t ≤ T, walkEmbed ε (h.position t) ∈ Metric.ball 0 (R : ℝ)}ᶜ)
    (r := fun R => ((initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β).real
      {p | scaledExit (Metric.ball 0 (R : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)})
  · intro R ε
    rw [pathLaw, ProbabilityMeasure.toMeasure_map,
      integral_map (measurable_halfLinePath (walkEmbed ε)).aemeasurable
        hZ.aestronglyMeasurable]
    exact abs_integral_sub_killed_le _ (hZ.comp (measurable_halfLinePath _))
      (fun h => hZC _) (hA ε R)
  · intro R
    have hB : MeasurableSet {p : Euc d × BrownianPath d |
        (T : ℝ≥0∞) < scaledExit (Metric.ball 0 (R : ℝ)) s p.1 p.2} :=
      measurableSet_lt measurable_const
        (measurable_scaledExit_joint Metric.isOpen_ball s)
    simpa only [Set.compl_setOf, not_lt] using
      abs_integral_sub_killed_le
        ((initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β) hW hWC hB
  · exact hk
  · exact hp
  · exact (ENNReal.continuousAt_toReal (by simp)).tendsto.comp
      (tendsto_exit_largeBall (initialDensityEuclidean g hg hg0 hg1) β s T)

end LongRange
