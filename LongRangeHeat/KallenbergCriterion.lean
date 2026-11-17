import LongRangeHeat.KallenbergAnnealedTight
import LongRangeHeat.KallenbergContinuity

/-!
# The Kallenberg–Aldous convergence criterion

Bounded optional increments and convergent finite-dimensional distributions
imply weak convergence in half-line path space.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

noncomputable section

variable {E : Type} [MetricSpace E] [ProperSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]

omit [ProperSpace E] in
/-- The optional-increment condition yields a uniform oscillation bound. -/
theorem exists_uniform_partition_of_stopping
    (μ : ℕ → ProbabilityMeasure (D E))
    (hstop : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : ℕ → D E → Time, (∀ n, naturalStopping id H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) → Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (μ n : Measure (D E))
          {w | η ≤ dist (w.1 (τ n w + u n)) (w.1 (τ n w))}) atTop (𝓝 0))
    (t : Time) (ht : 0 < t) {η : ℝ} (hη : 0 < η) {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      (μ n : Measure (D E)) {w | ¬ HasOscillationPartition w t δ η} < p := by
  apply exists_pos_uniform_oscillation_partition_of_optional_increment μ (fun _ => id)
    (fun _ => measurable_id) t ht ?_ hη hp
  exact hstop

omit [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Marginal tightness and the optional-increment condition give a common
high-probability totally bounded set. -/
theorem exists_totallyBounded_of_stopping
    (μ : ℕ → ProbabilityMeasure (D E)) (z : E)
    (hmarg : ∀ (t : Time) (p : ℝ), 0 < p → ∃ R : ℝ, ∀ n,
      (μ n : Measure (D E)) {w | R < dist (w.1 t) z} ≤ ENNReal.ofReal p)
    (hpart : ∀ (t : Time), 0 < t → ∀ (η : ℝ), 0 < η → ∀ (p : ℝ), 0 < p →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n,
        (μ n : Measure (D E)) {w | ¬ HasOscillationPartition w t δ η} ≤ ENNReal.ofReal p)
    {r : ℝ} (hr : 0 < r) :
    ∃ A : Set (D E), TotallyBounded A ∧ ∀ n,
      (μ n : Measure (D E)) Aᶜ ≤ ENNReal.ofReal r := by
  let t : ℕ → Time := fun k => (k : Time) + 1
  let η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let p : ℕ → ℝ := fun k => (r / 2) / 2 / 2 ^ k
  have ht0 : ∀ k, 0 < t k := by intro k; simp [t]
  have ht : Tendsto t atTop atTop := by
    exact tendsto_atTop_mono (fun k => by simp [t]) tendsto_natCast_atTop_atTop
  have hη : ∀ k, 0 < η k := by intro k; dsimp [η]; positivity
  have hη0 : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hp : ∀ k, 0 < p k := by intro k; dsimp [p]; positivity
  choose δ hδ hδbound using fun k => hpart (t k) (ht0 k) (η k) (hη k) (p k) (hp k)
  choose S hS hSbound using fun k => exists_compact_measure_excursion_le
    (fun n => (μ n : Measure (D E))) (fun _ => id) z (t k) hmarg
    (fun q hq => hpart (t k + 1) (by positivity) 1 (by norm_num) q hq) (hp k)
  obtain ⟨A, hA, hbound⟩ := exists_totallyBounded_measure_compl_le t δ η ht hδ hη hη0
    S hS (fun n => (μ n : Measure (D E))) (fun _ => id)
    (fun k => ENNReal.ofReal (p k)) (fun k => ENNReal.ofReal (p k))
    (fun n k => hδbound k n) (fun n k => hSbound k n)
  refine ⟨A, hA, fun n => (hbound n).trans ?_⟩
  have hsum : (∑' k, ENNReal.ofReal (p k)) = ENNReal.ofReal (r / 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hp k).le)]
    · simp only [p, tsum_geometric_two']
    · exact summable_geometric_two' (r / 2)
  rw [hsum, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have : r / 2 + r / 2 = r := by ring
  rw [this]

/-- Convergent one-time marginal laws have uniformly bounded tails. -/
theorem exists_marginal_radius_of_tendsto
    (μ : ℕ → ProbabilityMeasure (D E)) (ν : ProbabilityMeasure (D E)) (z : E)
    (h : ∀ t : Time, Tendsto (fun n => (μ n).map (fun w : D E => w.1 t)) atTop
      (𝓝 (ν.map (fun w : D E => w.1 t))))
    (t : Time) {p : ℝ} (hp : 0 < p) :
    ∃ R : ℝ, ∀ n, (μ n : Measure (D E)) {w | R < dist (w.1 t) z} ≤ ENNReal.ofReal p := by
  let m : ℕ → ProbabilityMeasure E := fun n => (μ n).map (fun w : D E => w.1 t)
  have hc : IsCompact (closure (range m)) := by
    have hcompact := (h t).isCompact_insert_range
    exact hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (subset_insert _ _) hcompact.isClosed)
  have htight := isTightMeasureSet_of_isCompact_closure hc
  obtain ⟨K, hK, hKbound⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal p) (ENNReal.ofReal_pos.mpr hp)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall z
  refine ⟨R, fun n => ?_⟩
  have hμ := hKbound (m n : Measure E) ⟨m n, ⟨n, rfl⟩, rfl⟩
  have hmap : (m n : Measure E) Kᶜ = (μ n : Measure (D E))
      ((fun w : D E => w.1 t) ⁻¹' Kᶜ) := by
    exact Measure.map_apply (measurable_eval t) hK.isClosed.measurableSet.compl
  rw [hmap] at hμ
  refine (measure_mono ?_).trans hμ
  intro w hw
  change w.1 t ∉ K
  intro hwK
  have := hR hwK
  change dist (w.1 t) z ≤ R at this
  exact (not_le_of_gt hw) this

/-- Convergence of finite-dimensional laws entails convergence of each
one-time marginal law. -/
theorem tendsto_marginal_of_tendsto_jointLaw
    (μ : ℕ → ProbabilityMeasure (D E)) (ν : ProbabilityMeasure (D E))
    (h : ∀ (k : ℕ) (ts : Fin k → Time),
      Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)))
    (t : Time) :
    Tendsto (fun n => (μ n).map (fun w : D E => w.1 t)) atTop
      (𝓝 (ν.map (fun w : D E => w.1 t))) := by
  let ts : Fin 1 → Time := fun _ => t
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => jointLaw (μ n) ts) (jointLaw ν ts) (h 1 ts)
    (continuous_apply (0 : Fin 1))
  have heq (ρ : ProbabilityMeasure (D E)) :
      (jointLaw ρ ts).map (fun x : Fin 1 → E => x 0) =
        ρ.map (fun w : D E => w.1 t) := by
    apply Subtype.ext
    change Measure.map (fun x : Fin 1 → E => x 0)
      (Measure.map (fun w : D E => fun i => w.1 (ts i)) (ρ : Measure (D E))) =
      Measure.map (fun w : D E => w.1 t) (ρ : Measure (D E))
    rw [Measure.map_map (measurable_pi_apply (0 : Fin 1)) (measurable_eval_family ts)]
    rfl
  simpa only [heq] using hmap

/-- **Kallenberg–Aldous criterion.** Convergence of finite-dimensional laws
and vanishing increments at bounded natural stopping times imply convergence
of the path laws in the half-line Skorokhod topology. -/
theorem tendsto_of_fdd_of_optional_increment
    (μ : ℕ → ProbabilityMeasure (D E)) (ν : ProbabilityMeasure (D E)) (z : E)
    (hfdd : ∀ (k : ℕ) (ts : Fin k → Time),
      Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)))
    (hstop : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : ℕ → D E → Time, (∀ n, naturalStopping id H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) → Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (μ n : Measure (D E))
          {w | η ≤ dist (w.1 (τ n w + u n)) (w.1 (τ n w))}) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 ν) := by
  have hmarg : ∀ (t : Time) (p : ℝ), 0 < p → ∃ R : ℝ, ∀ n,
      (μ n : Measure (D E)) {w | R < dist (w.1 t) z} ≤ ENNReal.ofReal p := by
    intro t p hp
    exact exists_marginal_radius_of_tendsto μ ν z
      (tendsto_marginal_of_tendsto_jointLaw μ ν hfdd) t hp
  have hpart : ∀ (t : Time), 0 < t → ∀ (η : ℝ), 0 < η → ∀ (p : ℝ), 0 < p →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n,
        (μ n : Measure (D E)) {w | ¬ HasOscillationPartition w t δ η} ≤ ENNReal.ofReal p := by
    intro t ht η hη p hp
    obtain ⟨δ, hδ, hbound⟩ := exists_uniform_partition_of_stopping μ hstop t ht hη
      (ENNReal.ofReal_pos.mpr hp)
    exact ⟨δ, hδ, fun n => (hbound n).le⟩
  have htight : IsTightMeasureSet {((μ n : ProbabilityMeasure (D E)) : Measure (D E)) | n} := by
    let : CompleteSpace (D E) := completeSpace_of_complete_state
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro δ hδ
    obtain ⟨r, hr, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ δ := by
      by_cases htop : δ = ∞
      · exact ⟨1, by norm_num, htop ▸ le_top⟩
      · exact ⟨δ.toReal, ENNReal.toReal_pos (ne_of_gt hδ) htop,
          le_of_eq (ENNReal.ofReal_toReal htop)⟩
    obtain ⟨A, hA, hmeasure⟩ := exists_totallyBounded_of_stopping μ z hmarg hpart hr
    refine ⟨closure A, hA.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
    rintro ρ ⟨n, rfl⟩
    exact ((measure_mono (compl_subset_compl.mpr subset_closure)).trans (hmeasure n)).trans hrδ
  have hcompact : IsCompact (closure (range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext ρ
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨ξ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, rfl⟩
  apply tendsto_of_compact_of_jointLaw_tendsto_positive hcompact
  intro k ts _
  exact hfdd k ts

/-- Strictly ordered finite-dimensional laws determine convergence at
arbitrary finite families of times. -/
theorem tendsto_jointLaw_of_ordered
    (μ : ℕ → ProbabilityMeasure (D E)) (ν : ProbabilityMeasure (D E))
    (h : ∀ (k : ℕ) (ts : Fin k → Time), StrictMono ts →
      Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)))
    {k : ℕ} (ts : Fin k → Time) :
    Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)) := by
  classical
  let s := Finset.univ.image ts
  let e := s.orderIsoOfFin rfl
  let ss : Fin s.card → Time := s.orderEmbOfFin rfl
  let r : Fin k → Fin s.card := fun i => e.symm ⟨ts i, Finset.mem_image.mpr ⟨i,
    Finset.mem_univ i, rfl⟩⟩
  have hts : ss ∘ r = ts := by
    funext i
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hconv := h s.card ss (s.orderEmbOfFin rfl).strictMono
  have hc : Continuous (fun x : Fin s.card → E => x ∘ r) :=
    continuous_pi fun i => continuous_apply (r i)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv hc
  have heq (ρ : ProbabilityMeasure (D E)) :
      jointLaw ρ (ss ∘ r) = (jointLaw ρ ss).map (fun x : Fin s.card → E => x ∘ r) :=
    jointLaw_reindex ρ ss r
  have hmap' : Tendsto (fun n => jointLaw (μ n) (ss ∘ r)) atTop
      (𝓝 (jointLaw ν (ss ∘ r))) := by
    simp only [heq]
    exact hmap
  simpa only [hts] using hmap'

/-- The convergence criterion with finite-dimensional laws stated at strictly
ordered times. -/
theorem tendsto_of_ordered_fdd_of_optional_increment
    (μ : ℕ → ProbabilityMeasure (D E)) (ν : ProbabilityMeasure (D E)) (z : E)
    (hfdd : ∀ (k : ℕ) (ts : Fin k → Time), StrictMono ts →
      Tendsto (fun n => jointLaw (μ n) ts) atTop (𝓝 (jointLaw ν ts)))
    (hstop : ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
      ∀ τ : ℕ → D E → Time, (∀ n, naturalStopping id H (τ n)) →
      ∀ u : ℕ → Time, (∀ n, 0 < u n) → Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (μ n : Measure (D E))
          {w | η ≤ dist (w.1 (τ n w + u n)) (w.1 (τ n w))}) atTop (𝓝 0)) :
    Tendsto μ atTop (𝓝 ν) :=
  tendsto_of_fdd_of_optional_increment μ ν z
    (fun _ ts => tendsto_jointLaw_of_ordered μ ν hfdd ts) hstop

end

end LatticeProb.Cadlag.HalfLine
