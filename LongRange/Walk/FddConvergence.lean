import LongRange.Walk.SemigroupConvergence
import LongRange.Walk.KilledFddConvergence
import LongRange.Walk.KillingRemoval
import LatticeProb.Prob.Cadlag.HalfLine.FddAssembly

/-!
# Convergence of positive-time walk observations

On the full-probability homogenization event, killed product expectations converge on every
large ball. Large-ball exit removes the killing. This gives the positive-time product tests
of the walk path laws against the independent mixture of the initial density and Brownian
motion.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.ContractionSemigroup LatticeProb.Cadlag.HalfLine
open scoped NNReal ENNReal Topology BoundedContinuousFunction

noncomputable section

variable {d : ℕ}

/-- The continuous path `x + s W` started from an initial point and a Brownian path. -/
def brownianMixturePath (s : ℝ) (p : EuclideanSpace ℝ (Fin d) × BrownianPath d) :
    D (EuclideanSpace ℝ (Fin d)) :=
  D.ofContinuous ⟨fun t => p.1 + s • p.2 t,
    continuous_const.add (p.2.continuous.const_smul s)⟩

/-- The mixture path is measurable for the Skorokhod Borel structure. -/
theorem measurable_brownianMixturePath (s : ℝ) :
    Measurable (brownianMixturePath (d := d) s) := by
  apply measurable_iff_measurable_eval.mpr
  intro t
  change Measurable (fun p : EuclideanSpace ℝ (Fin d) × BrownianPath d => p.1 + s • p.2 t)
  fun_prop

/-- An embedded site lies in a Euclidean ball exactly when it lies in the lattice ball. -/
theorem walkEmbed_mem_ball_iff (ε r : ℝ) (q : Site d) :
    walkEmbed ε q ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r ↔
      q ∈ latticeSet ε (continuumDomain (d := d) r) := by
  rw [continuumDomain_eq_radius, Metric.mem_ball, dist_zero_right, walkEmbed, ← radius_norm]
  rfl

/-- A measurable nonnegative representative of an L² density, supported in its support. -/
theorem exists_density_representative {g : (Fin d → ℝ) → ℝ} (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) :
    ∃ g' : (Fin d → ℝ) → ℝ, Measurable g' ∧ (∀ x, 0 ≤ g' x) ∧ g' =ᵐ[volume] g ∧
      Function.support g' ⊆ tsupport g := by
  refine ⟨(tsupport g).indicator (fun x => max (hg.1.mk g x) 0), ?_, ?_, ?_, ?_⟩
  · exact (hg.1.stronglyMeasurable_mk.measurable.max measurable_const).indicator
      (isClosed_tsupport g).measurableSet
  · exact Set.indicator_nonneg (fun y _ => le_max_right _ _)
  · filter_upwards [hg.1.ae_eq_mk, hg0] with x hx hx0
    by_cases hxs : x ∈ tsupport g
    · rw [Set.indicator_of_mem hxs, ← hx, max_eq_left hx0]
    · rw [Set.indicator_of_notMem hxs, image_eq_zero_of_notMem_tsupport hxs]
  · exact Set.support_indicator_subset

/-- Initial lattice laws depend only on the almost-everywhere class of the density. -/
theorem initialLaw_congr_ae {ε : ℝ} (hε : 0 < ε) {g g' : (Fin d → ℝ) → ℝ}
    (h : g' =ᵐ[volume] g) (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) (hg' : Integrable g' volume) (hg0' : ∀ᵐ y ∂volume, 0 ≤ g' y)
    (hg1' : ∫ y, g' y = 1) :
    initialLaw ε g' hε hg' hg0' hg1' = initialLaw ε g hε hg hg0 hg1 := by
  apply Subtype.ext
  apply initialLaw_unique
  intro z
  have hc : cellAverage ε Set.univ g' z = cellAverage ε Set.univ g z := by
    simp only [cellAverage, Set.indicator_univ]
    congr 1
    exact integral_congr_ae (ae_restrict_of_ae h)
  rw [← hc]
  exact initialLaw_singleton ε g' hε hg' hg0' hg1' z

/-- The transported density law depends only on the almost-everywhere class of the density. -/
theorem initialDensityEuclidean_congr_ae {g g' : (Fin d → ℝ) → ℝ}
    (h : g' =ᵐ[volume] g) (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) (hg' : Integrable g' volume) (hg0' : ∀ᵐ y ∂volume, 0 ≤ g' y)
    (hg1' : ∫ y, g' y = 1) :
    initialDensityEuclidean g' hg' hg0' hg1' = initialDensityEuclidean g hg hg0 hg1 := by
  apply Subtype.ext
  change Measure.map _ (volume.withDensity _) = Measure.map _ (volume.withDensity _)
  rw [withDensity_congr_ae (h.mono fun y hy => by rw [hy])]

/-- A density vanishing off a coordinate ball transports to the restricted ball density. -/
theorem initialDensityEuclidean_eq_restrict {g : (Fin d → ℝ) → ℝ}
    (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1)
    {R : ℝ} (hzero : ∀ x, x ∉ continuumDomain (d := d) R → g x = 0) :
    (initialDensityEuclidean g hg hg0 hg1 : Measure (EuclideanSpace ℝ (Fin d))) =
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)).withDensity
        (fun x => ENNReal.ofReal (g (EuclideanSpace.equiv (Fin d) ℝ x))) := by
  have hmeas : MeasurableSet (continuumDomain (d := d) R) := by
    rw [continuumDomain_eq_radius]
    exact (isOpen_lt (radius_continuous d) continuous_const).measurableSet
  have hdom : (fun y => ENNReal.ofReal (g y)) =
      (continuumDomain (d := d) R).indicator (fun y => ENNReal.ofReal (g y)) := by
    funext y
    by_cases hy : y ∈ continuumDomain (d := d) R
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, hzero y hy, ENNReal.ofReal_zero]
  have hto : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    (PiLp.continuous_toLp (p := (2 : ENNReal)) (fun _ : Fin d => ℝ)).measurable
  ext A hA
  have hpre : (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' ((WithLp.toLp 2) ⁻¹' A) = A := rfl
  rw [initialDensityEuclidean, ProbabilityMeasure.toMeasure_map, Measure.map_apply hto hA]
  change (volume.withDensity (fun y => ENNReal.ofReal (g y))) _ = _
  rw [hdom, withDensity_indicator hmeas, withDensity_apply _ (hto hA), withDensity_apply _ hA]
  conv_rhs => rw [← hpre]
  exact ((coord_measurePreserving (d := d) R).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding _ _).symm

/-- Increments of a monotone schedule accumulate back to its observation times. -/
theorem cumulativeObservations_ofFn {k : ℕ} (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t)
    (b : Fin k → Euc d → ℝ) :
    cumulativeObservations (t 0) (List.ofFn fun i => (t i.succ - t i.castSucc, b i)) =
      List.ofFn fun i => (t i.succ, b i) := by
  induction k with
  | zero => simp only [List.ofFn_zero, cumulativeObservations]
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [cumulativeObservations, Fin.castSucc_zero]
    rw [add_tsub_cancel_of_le (ht (Fin.zero_le _))]
    have h := ih (fun i => t i.succ) (ht.comp Fin.strictMono_succ.monotone)
      (fun i => b i.succ)
    simp only [Fin.succ_castSucc] at h
    rw [h]

/-- The increments of a monotone schedule sum to its total elapsed time. -/
theorem sum_increments_ofFn {k : ℕ} (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t)
    (b : Fin k → Euc d → ℝ) :
    ((List.ofFn fun i => (t i.succ - t i.castSucc, b i)).map Prod.fst).sum =
      t (Fin.last k) - t 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.map_cons, List.sum_cons]
    have h := ih (fun i => t i.succ) (ht.comp Fin.strictMono_succ.monotone)
      (fun i => b i.succ)
    simp only [Fin.succ_castSucc, Fin.succ_last] at h
    rw [h, Fin.castSucc_zero, add_comm,
      tsub_add_tsub_cancel (ht (Fin.le_last _)) (ht (Fin.zero_le _))]

/-- A nonempty killed schedule is the survival indicator times the observation product. -/
theorem killedProduct_ofFn_eq {B : Set (Euc d)} (hB : IsOpen B) (σ : ℝ) {k : ℕ}
    (t : Fin (k + 2) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (b : Fin (k + 1) → Euc d → ℝ) (x : Euc d) (ω : BrownianPath d) :
    killedProduct B σ (List.ofFn fun i => (t i.succ - t i.castSucc, b i)) x ω =
      if (t (Fin.last (k + 1)) : ℝ≥0∞) < scaledExit B σ x ω
      then ∏ i, b i (x + σ • ω (t i.succ)) else 0 := by
  have hc := cumulativeObservations_ofFn t ht b
  rw [ht0] at hc
  rw [killedProduct_eq_final_survival hB σ _ (by simp), sum_increments_ofFn t ht, ht0,
    tsub_zero, observationProduct_eq_prod, hc, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Removal of killing along a sequence, using only balls beyond a fixed radius. -/
theorem tendsto_walk_integral_of_killed_largeBall_seq (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (g : (Fin d → ℝ) → ℝ) (hg : Integrable g volume)
    (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y) (hg1 : ∫ y, g y = 1)
    (β : Measure (BrownianPath d)) [IsProbabilityMeasure β] (s : ℝ) (T : ℝ≥0)
    (Z : D (EuclideanSpace ℝ (Fin d)) → ℝ)
    (W : Euc d × BrownianPath d → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hZ : Measurable Z) (hW : Measurable W)
    (hZC : ∀ x, |Z x| ≤ C) (hWC : ∀ x, |W x| ≤ C)
    (ε : ℕ → Eps) (N : ℕ)
    (hk : ∀ R : ℕ, Tendsto (fun n =>
      ∫ h, {h : JumpChain.RegularHistory (Site d) | ∀ t ≤ T,
        walkEmbed (ε n) (h.position t) ∈ Metric.ball 0 ((R + N : ℕ) : ℝ)}.indicator
          (fun h => Z (h.halfLinePath (walkEmbed (ε n)))) h
        ∂(walkRates hd (ε n).2.1 hlam a ha).regularLaw
          (initialLaw (ε n) g (ε n).2.1 hg hg0 hg1)) atTop
      (𝓝 (∫ p, {p | (T : ℝ≥0∞) < scaledExit
        (Metric.ball 0 ((R + N : ℕ) : ℝ)) s p.1 p.2}.indicator W p
          ∂(initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β)))
    (hp : ∀ R : ℕ, Tendsto (fun n =>
      ((walkRates hd (ε n).2.1 hlam a ha).regularLaw
        (initialLaw (ε n) g (ε n).2.1 hg hg0 hg1)).real
          {h | ∀ t ≤ T, walkEmbed (ε n) (h.position t) ∈
            Metric.ball 0 ((R + N : ℕ) : ℝ)}ᶜ) atTop
      (𝓝 (((initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β).real
        {p | scaledExit (Metric.ball 0 ((R + N : ℕ) : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)}))) :
    Tendsto (fun n =>
      ∫ x, Z x ∂(pathLaw (walkRates hd (ε n).2.1 hlam a ha)
        (initialLaw (ε n) g (ε n).2.1 hg hg0 hg1) (walkEmbed (ε n)) :
          Measure (D (EuclideanSpace ℝ (Fin d))))) atTop
      (𝓝 (∫ p, W p
        ∂(initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β)) := by
  have hA (n R : ℕ) : MeasurableSet
      {h : JumpChain.RegularHistory (Site d) | ∀ t ≤ T,
        walkEmbed (ε n) (h.position t) ∈ Metric.ball 0 ((R + N : ℕ) : ℝ)} :=
    JumpChain.BoundedRates.naturalSigma_le T _
      (JumpChain.BoundedRates.measurableSet_survival_naturalSigma
        ((walkEmbed (ε n)) ⁻¹' Metric.ball 0 ((R + N : ℕ) : ℝ)) T)
  apply limsup_product_le_of_killed hC (k := fun R n =>
    ∫ h, {h : JumpChain.RegularHistory (Site d) | ∀ t ≤ T,
      walkEmbed (ε n) (h.position t) ∈ Metric.ball 0 ((R + N : ℕ) : ℝ)}.indicator
        (fun h => Z (h.halfLinePath (walkEmbed (ε n)))) h
      ∂(walkRates hd (ε n).2.1 hlam a ha).regularLaw
        (initialLaw (ε n) g (ε n).2.1 hg hg0 hg1))
    (p := fun R n => ((walkRates hd (ε n).2.1 hlam a ha).regularLaw
      (initialLaw (ε n) g (ε n).2.1 hg hg0 hg1)).real
        {h | ∀ t ≤ T, walkEmbed (ε n) (h.position t) ∈ Metric.ball 0 ((R + N : ℕ) : ℝ)}ᶜ)
    (r := fun R => ((initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β).real
      {p | scaledExit (Metric.ball 0 ((R + N : ℕ) : ℝ)) s p.1 p.2 ≤ (T : ℝ≥0∞)})
  · intro R n
    rw [pathLaw, ProbabilityMeasure.toMeasure_map,
      integral_map (measurable_halfLinePath (walkEmbed (ε n))).aemeasurable
        hZ.aestronglyMeasurable]
    exact abs_integral_sub_killed_le _ (hZ.comp (measurable_halfLinePath _))
      (fun h => hZC _) (hA n R)
  · intro R
    have hB : MeasurableSet {p : Euc d × BrownianPath d |
        (T : ℝ≥0∞) < scaledExit (Metric.ball 0 ((R + N : ℕ) : ℝ)) s p.1 p.2} :=
      measurableSet_lt measurable_const
        (measurable_scaledExit_joint Metric.isOpen_ball s)
    simpa only [Set.compl_setOf, not_lt] using
      abs_integral_sub_killed_le
        ((initialDensityEuclidean g hg hg0 hg1 : Measure (Euc d)).prod β) hW hWC hB
  · exact hk
  · exact hp
  · exact (ENNReal.continuousAt_toReal (by simp)).tendsto.comp
      ((tendsto_exit_largeBall (initialDensityEuclidean g hg hg0 hg1) β s T).comp
        (tendsto_add_atTop_nat N))

/-- Under uniform killed-semigroup convergence on all large balls, walk product tests at
monotone times converge to the independent mixture of the density and Brownian motion. -/
theorem tendsto_walk_productTest_of_killed (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (a₀ : ℝ)
    {μB : Measure (BrownianPath d)} (hμB : IsStandardBrownianLaw μB)
    (hconv : ∀ R : ℕ, ∀ hR : 1 ≤ R,
      let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2)
        (show (0 : ℝ) < R by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
      ∀ εn : ℕ → {ε : ℝ // 0 < ε},
        Tendsto (fun n => (εn n).val) atTop (𝓝 0) →
        UniformSemigroupConvergence
          (fun n => cellAverageLp (εn n).property hU.1.measurableSet hU.2.2.1)
          (continuumSemigroup R a₀ hμB)
          (fun n => discreteKilledSemigroup hd (εn n).property hlam a ha hU.2.2.1))
    (g : (Fin d → ℝ) → ℝ) (hgm : Measurable g) (hg : MemLp g 2 volume)
    (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∫ x, g x = 1)
    (ε : ℕ → Eps) (hε : Tendsto (fun n => (ε n).val) atTop (𝓝 0))
    {m : ℕ} (ss : Fin (m + 1) → Time) (hss : Monotone ss)
    (φ : Fin (m + 1) → EuclideanSpace ℝ (Fin d) →ᵇ ℝ) :
    Tendsto (fun n => ∫ w, ∏ j, φ j (w.1 (ss j))
        ∂(pathLaw (walkRates hd (ε n).property.1 hlam a ha)
          (initialLaw (ε n).val g (ε n).property.1 (integrable_initial_density hg hgc)
            (Eventually.of_forall hg0) hg1 : Measure (Site d)) (walkEmbed (ε n).val) :
              Measure (D (EuclideanSpace ℝ (Fin d))))) atTop
      (𝓝 (∫ p, ∏ j, φ j (p.1 + Real.sqrt (2 * a₀) • p.2 (ss j))
        ∂(initialDensityEuclidean g (integrable_initial_density hg hgc)
          (Eventually.of_forall hg0) hg1 : Measure (EuclideanSpace ℝ (Fin d))).prod μB)) := by
  letI : IsProbabilityMeasure μB := hμB.1
  have hgi := integrable_initial_density hg hgc
  -- Observation times, with the initial time prepended.
  let t : Fin (m + 2) → ℝ≥0 := Fin.cons 0 ss
  have ht : Monotone t := by
    refine Fin.monotone_iff_le_succ.mpr (fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact zero_le
    · simp only [t, ← Fin.succ_castSucc, Fin.cons_succ]
      exact hss Fin.castSucc_lt_succ.le
  have ht0 : t 0 = 0 := rfl
  -- A radius beyond which every ball contains twice the density support.
  obtain ⟨R₀, hR₀⟩ := (hgc.image (PiLp.continuous_toLp (p := (2 : ENNReal))
    (fun _ : Fin d => ℝ))).isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin d))
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * R₀) 1)
  have hN1 : 1 ≤ N := by
    have h : (1 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
    exact_mod_cast h.le
  have hsupp (R : ℕ) :
      Function.support g ⊆ continuumDomain (d := d) (((R + N : ℕ) : ℝ) / 2) := by
    intro x hx
    have h := hR₀ (Set.mem_image_of_mem (WithLp.toLp 2) (subset_tsupport g hx))
    rw [Metric.mem_ball, dist_zero_right, ← radius_norm] at h
    rw [continuumDomain_eq_radius]
    have h2 : 2 * R₀ < N := lt_of_le_of_lt (le_max_left _ _) hN
    have h3 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    show radius x < ((R + N : ℕ) : ℝ) / 2
    push_cast
    linarith
  have hzero (R : ℕ) : ∀ x, x ∉ continuumDomain (d := d) ((R + N : ℕ) : ℝ) → g x = 0 := by
    intro x hx
    by_contra hne
    have hs := hsupp R (Function.mem_support.mpr hne)
    rw [continuumDomain_eq_radius] at hs hx
    have h3 : (0 : ℝ) ≤ ((R + N : ℕ) : ℝ) := Nat.cast_nonneg _
    exact hx (show radius x < ((R + N : ℕ) : ℝ) by
      dsimp only [Set.mem_setOf_eq] at hs; linarith)
  -- Coordinate versions of the Euclidean marks.
  let ι : C(Fin d → ℝ, EuclideanSpace ℝ (Fin d)) :=
    ⟨WithLp.toLp 2, PiLp.continuous_toLp (p := (2 : ENNReal)) (fun _ : Fin d => ℝ)⟩
  let φ' : Fin (m + 1) → (Fin d → ℝ) →ᵇ ℝ := fun j => (φ j).compContinuous ι
  let one' : Fin (m + 1) → (Fin d → ℝ) →ᵇ ℝ := fun _ => 1
  have hone (i : Fin (m + 1)) (x : Fin d → ℝ) : one' i x = 1 := rfl
  have hεF : Tendsto ε atTop epsFilter := tendsto_epsFilter_iff.mpr hε
  have hKF := fun (R : ℕ) (ψ : Fin (m + 1) → (Fin d → ℝ) →ᵇ ℝ) =>
    tendsto_killed_product_expectation hd hlam (R := ((R + N : ℕ) : ℝ))
      (by exact_mod_cast (show 0 < R + N by omega)) a ha a₀ hμB _ _ ε hεF
      (hconv (R + N) (by omega) (fun n => ⟨(ε n).val, (ε n).property.1⟩) hε)
      g hgm hg hgc hg0 hg1 (hsupp R) (m + 1) t ht ht0 ψ
  have hset (n R : ℕ) : {h : JumpChain.RegularHistory (Site d) | ∀ s ≤ t (Fin.last (m + 1)),
      walkEmbed (ε n).val (h.position s) ∈ Metric.ball 0 ((R + N : ℕ) : ℝ)} =
      {h | ∀ s ≤ t (Fin.last (m + 1)), h.position s ∈
        latticeSet (ε n).val (continuumDomain (d := d) ((R + N : ℕ) : ℝ))} := by
    ext h
    simp only [Set.mem_setOf_eq, walkEmbed_mem_ball_iff]
  have hB (R : ℕ) : MeasurableSet {p : Euc d × BrownianPath d | (t (Fin.last (m + 1)) : ℝ≥0∞) <
      scaledExit (Metric.ball 0 ((R + N : ℕ) : ℝ)) (Real.sqrt (2 * a₀)) p.1 p.2} :=
    measurableSet_lt measurable_const (measurable_scaledExit_joint Metric.isOpen_ball _)
  have hA (n R : ℕ) : MeasurableSet {h : JumpChain.RegularHistory (Site d) |
      ∀ s ≤ t (Fin.last (m + 1)), walkEmbed (ε n).val (h.position s) ∈
        Metric.ball 0 ((R + N : ℕ) : ℝ)} :=
    JumpChain.BoundedRates.naturalSigma_le _ _
      (JumpChain.BoundedRates.measurableSet_survival_naturalSigma
        ((walkEmbed (ε n).val) ⁻¹' Metric.ball 0 ((R + N : ℕ) : ℝ)) _)
  have hC : 0 ≤ ∏ j, ‖φ j‖ := Finset.prod_nonneg (fun j _ => norm_nonneg _)
  apply tendsto_walk_integral_of_killed_largeBall_seq hd hlam a ha g hgi
    (Eventually.of_forall hg0) hg1 μB (Real.sqrt (2 * a₀)) (t (Fin.last (m + 1)))
    (fun w => ∏ j, φ j (w.1 (ss j))) (fun p => ∏ j, φ j (p.1 + Real.sqrt (2 * a₀) • p.2 (ss j)))
    hC
    (Finset.measurable_prod _ (fun j _ =>
      (φ j).continuous.measurable.comp (measurable_eval (ss j))))
    (Finset.measurable_prod _ (fun j _ => (φ j).continuous.measurable.comp (by fun_prop)))
    (fun w => by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun j _ => abs_nonneg _)
        (fun j _ => by simpa only [Real.norm_eq_abs] using (φ j).norm_coe_le_norm _))
    (fun p => by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun j _ => abs_nonneg _)
        (fun j _ => by simpa only [Real.norm_eq_abs] using (φ j).norm_coe_le_norm _))
    ε N
  · intro R
    convert hKF R φ' using 1
    · funext n
      rw [hset n R]
      rfl
    · congr 1
      rw [initialDensityEuclidean_eq_restrict hgi (Eventually.of_forall hg0) hg1 (hzero R)]
      congr 1
      funext p
      rw [killedProduct_ofFn_eq Metric.isOpen_ball _ t ht ht0]
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> rfl
  · intro R
    have h1 : Tendsto (fun n => ((walkRates hd (ε n).property.1 hlam a ha).regularLaw
        (initialLaw (ε n).val g (ε n).property.1 hgi (Eventually.of_forall hg0) hg1 :
          Measure (Site d))).real {h | ∀ s ≤ t (Fin.last (m + 1)),
            walkEmbed (ε n).val (h.position s) ∈ Metric.ball 0 ((R + N : ℕ) : ℝ)}) atTop
        (𝓝 (((initialDensityEuclidean g hgi (Eventually.of_forall hg0) hg1 :
          Measure (Euc d)).prod μB).real {p | (t (Fin.last (m + 1)) : ℝ≥0∞) <
            scaledExit (Metric.ball 0 ((R + N : ℕ) : ℝ)) (Real.sqrt (2 * a₀)) p.1 p.2})) := by
      convert hKF R one' using 1
      · funext n
        rw [← integral_indicator_one (hA n R), hset n R]
        congr 1
        funext h
        simp only [hone, Finset.prod_const_one]
        rfl
      · congr 1
        rw [← integral_indicator_one (hB R),
          initialDensityEuclidean_eq_restrict hgi (Eventually.of_forall hg0) hg1 (hzero R)]
        congr 1
        funext p
        rw [killedProduct_ofFn_eq Metric.isOpen_ball _ t ht ht0]
        simp only [hone, Finset.prod_const_one, Set.indicator, Set.mem_setOf_eq]
        split_ifs <;> rfl
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    convert h2 using 1
    · funext n
      exact probReal_compl_eq_one_sub (hA n R)
    · congr 1
      rw [← probReal_compl_eq_one_sub (hB R), Set.compl_setOf]
      simp only [not_lt]

/-- On one full-probability event, for every null sequence of scales, the walk path laws
converge against all positive-time product tests to the independent mixture of the initial
density and Brownian motion with amplitude `sqrt (2 a₀)`. -/
theorem ae_tendsto_walk_productTests
    (hTK : External.EthierKurtzTrotterKato)
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (ha : AssumptionU P lam a)
    (g : (Fin d → ℝ) → ℝ) (hg : MemLp g 2 volume)
    (hg0 : ∀ᵐ x ∂volume, 0 ≤ g x) (hgc : HasCompactSupport g) (hg1 : ∫ x, g x = 1)
    (B : ProbabilityMeasure (BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (BrownianPath d))) :
    ∀ᵐ ξ ∂P, ∀ ε : ℕ → Eps, Tendsto (fun n => (ε n).val) atTop (𝓝 0) →
      ∀ {m : ℕ} (ss : Fin m → Time), StrictMono ss → (∀ j, 0 < ss j) →
      ∀ φ : Fin m → EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, ∏ j, φ j (x j)
        ∂(jointLaw (pathLaw (walkRates hd (ε n).property.1 ha.lam_pos (a ξ) (ha.bounds ξ))
          (initialLaw (ε n).val g (ε n).property.1 (integrable_initial_density hg hgc) hg0 hg1 :
            Measure (Site d)) (walkEmbed (ε n).val)) ss :
              Measure (Fin m → EuclideanSpace ℝ (Fin d)))) atTop
        (𝓝 (∫ x, ∏ j, φ j (x j) ∂(jointLaw (ProbabilityMeasure.map
          (⟨(initialDensityEuclidean g (integrable_initial_density hg hgc) hg0 hg1 :
            Measure (EuclideanSpace ℝ (Fin d))).prod (B : Measure (BrownianPath d)),
              inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × BrownianPath d))
          (measurable_brownianMixturePath (d := d)
            (Real.sqrt (2 * (meanConductance P hd a / (2 * (d : ℝ)))))).aemeasurable) ss :
              Measure (Fin m → EuclideanSpace ℝ (Fin d))))) := by
  filter_upwards [ae_tendsto_killedSemigroup hTK h619 h66 h37 h637 h614 hd P a ha hB]
    with ξ hξ
  intro ε hε m ss hss _ φ
  have hgi := integrable_initial_density hg hgc
  -- Replace the density by a measurable nonnegative compactly supported representative.
  obtain ⟨g', hg'm, hg'0, hae, hsupp'⟩ := exists_density_representative hg hg0
  have hg'L : MemLp g' 2 volume := hg.ae_eq hae.symm
  have hg'c : HasCompactSupport g' := hgc.mono' hsupp'
  have hg'1 : ∫ x, g' x = 1 := (integral_congr_ae hae).trans hg1
  have hg'i := integrable_initial_density hg'L hg'c
  have hlaw (n : ℕ) := (initialLaw_congr_ae (ε n).property.1 hae hgi hg0 hg1 hg'i
    (Eventually.of_forall hg'0) hg'1).symm
  have hρ := (initialDensityEuclidean_congr_ae hae hgi hg0 hg1 hg'i
    (Eventually.of_forall hg'0) hg'1).symm
  simp only [hlaw, hρ, integral_jointLaw_productTest]
  cases m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, integral_const, smul_eq_mul, mul_one,
      probReal_univ]
    exact tendsto_const_nhds
  | succ m =>
    have hZ : Measurable (fun w : D (EuclideanSpace ℝ (Fin d)) => ∏ j, φ j (w.1 (ss j))) :=
      Finset.measurable_prod _ (fun j _ =>
        (φ j).continuous.measurable.comp (measurable_eval (ss j)))
    rw [ProbabilityMeasure.toMeasure_map, integral_map
      (measurable_brownianMixturePath (d := d) _).aemeasurable hZ.aestronglyMeasurable]
    exact tendsto_walk_productTest_of_killed hd ha.lam_pos (a ξ) (ha.bounds ξ) _ hB hξ
      g' hg'm hg'L hg'c hg'0 hg'1 ε hε ss hss.monotone φ

end

end LongRange
