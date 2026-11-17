import LongRangeHeat.KallenbergModulus

/-!
# Compact containment from finite observations

An oscillation partition controls path values by finitely many observations
when every relevant partition interval contains an observation time.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set MeasureTheory
open scoped ENNReal

variable {E : Type} [MetricSpace E]

/-- A finite set meets every sufficiently short right interval beginning before `T`. -/
theorem exists_finite_right_observations (T : Time) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset Time, ∀ a : Time, a ≤ T →
      ∃ u ∈ G, (a : ℝ) < (u : ℝ) ∧ (u : ℝ) < (a : ℝ) + ε := by
  classical
  obtain ⟨S, hSsub, hSfin, hcover⟩ :=
    isCompact_Icc.finite_cover_balls (s := Icc (0 : ℝ) (T : ℝ)) (show 0 < ε / 4 by linarith)
  let G : Finset Time := hSfin.toFinset.image (fun c => (c + ε / 2).toNNReal)
  refine ⟨G, fun a ha => ?_⟩
  have haI : (a : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := ⟨a.2, by exact_mod_cast ha⟩
  obtain ⟨c, hcS, hac⟩ := Set.mem_iUnion₂.mp (hcover haI)
  have hc0 : 0 ≤ c := (hSsub hcS).1
  have hd : |(a : ℝ) - c| < ε / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hac
  have hminus := (abs_lt.mp hd).1
  have hplus := (abs_lt.mp hd).2
  have hshift : 0 ≤ c + ε / 2 := by linarith
  refine ⟨(c + ε / 2).toNNReal, Finset.mem_image.mpr ⟨c, ?_, rfl⟩, ?_, ?_⟩
  · exact hSfin.mem_toFinset.mpr hcS
  · rw [Real.coe_toNNReal _ hshift]
    linarith
  · rw [Real.coe_toNNReal _ hshift]
    linarith

/-- Each value before the horizon is close to an observation in its partition interval. -/
theorem HasOscillationPartition.exists_observation_near
    {x : D E} {t T : Time} {δ η : ℝ}
    (hpart : HasOscillationPartition x t δ η) (hT : T < t)
    (G : Finset Time)
    (hgrid : ∀ a b : Time, a ≤ T → a < b →
      (δ ≤ (b : ℝ) - (a : ℝ) ∨ b = t) →
      ∃ u ∈ G, a ≤ u ∧ u < b)
    {s : Time} (hs : s ≤ T) :
    ∃ u ∈ G, dist (x.1 s) (x.1 u) ≤ η := by
  obtain ⟨K, hK, cut, hzero, hlast, hstrict, hwidth, hosc⟩ := hpart
  have hex : ∃ j, s < cut j := ⟨K, by rw [hlast]; exact hs.trans_lt hT⟩
  let j := Nat.find hex
  have hj : s < cut j := Nat.find_spec hex
  have hjK : j ≤ K := Nat.find_min' hex (by rw [hlast]; exact hs.trans_lt hT)
  have hjpos : 0 < j := by
    by_contra h
    have : j = 0 := by omega
    rw [this, hzero] at hj
    exact (not_lt_of_ge (show 0 ≤ s from bot_le)) hj
  let i := j - 1
  have hi : i + 1 = j := by dsimp [i]; omega
  have hiK : i < K := by omega
  have hstart : cut i ≤ s := by
    have hmin := Nat.find_min hex (show i < j by omega)
    exact le_of_not_gt hmin
  have hlast_or_width : δ ≤ (cut (i + 1) : ℝ) - (cut i : ℝ) ∨ cut (i + 1) = t := by
    by_cases h : i + 1 < K
    · exact Or.inl (hwidth i h)
    · right
      have : i + 1 = K := by omega
      rw [this, hlast]
  obtain ⟨u, huG, hcu, hu⟩ := hgrid (cut i) (cut (i + 1))
    (hstart.trans hs) (hstrict i hiK) hlast_or_width
  exact ⟨u, huG, hosc i hiK s u hstart (by simpa only [hi] using hj) hcu hu⟩

/-- A finite observation set controls every path with the same mesh and oscillation bounds. -/
theorem exists_finite_observations_of_oscillation_partition
    (T : Time) {δ η : ℝ} (hδ : 0 < δ) :
    ∃ G : Finset Time, ∀ x : D E,
      HasOscillationPartition x (T + 1) δ η → ∀ s ≤ T,
      ∃ u ∈ G, dist (x.1 s) (x.1 u) ≤ η := by
  obtain ⟨G, hG⟩ := exists_finite_right_observations T (show 0 < min δ 1 by positivity)
  refine ⟨G, fun x hx s hs => hx.exists_observation_near (lt_add_of_pos_right T zero_lt_one)
    G ?_ hs⟩
  intro a b ha hab hwidth
  obtain ⟨u, hu, hau, huupper⟩ := hG a ha
  refine ⟨u, hu, ?_, ?_⟩
  · exact_mod_cast hau.le
  · have hb : (a : ℝ) + min δ 1 ≤ (b : ℝ) := by
      rcases hwidth with h | h
      · have hm := min_le_left δ (1 : ℝ)
        linarith
      · have hm := min_le_right δ (1 : ℝ)
        have ha' : (a : ℝ) ≤ (T : ℝ) := by exact_mod_cast ha
        rw [h]
        simp only [NNReal.coe_add, NNReal.coe_one]
        linarith
    exact_mod_cast huupper.trans_le hb

/-- A path with controlled observations remains in a larger closed ball through `T`. -/
theorem exists_finite_observations_bound_path
    (T : Time) {δ η : ℝ} (hδ : 0 < δ) (z : E) (R : ℝ) :
    ∃ G : Finset Time, ∀ x : D E,
      HasOscillationPartition x (T + 1) δ η →
      (∀ u ∈ G, dist (x.1 u) z ≤ R) →
      ∀ s ≤ T, dist (x.1 s) z ≤ R + η := by
  obtain ⟨G, hG⟩ := exists_finite_observations_of_oscillation_partition (E := E) T hδ
  refine ⟨G, fun x hx hvalues s hs => ?_⟩
  obtain ⟨u, hu, hdist⟩ := hG x hx s hs
  calc
    dist (x.1 s) z ≤ dist (x.1 s) (x.1 u) + dist (x.1 u) z := dist_triangle _ _ _
    _ ≤ η + R := add_le_add hdist (hvalues u hu)
    _ = R + η := add_comm _ _

/-- The probability of leaving a ball is bounded by the partition failure probability and
finitely many one-time marginal tails. -/
theorem exists_finite_observations_measure_le
    (T : Time) {δ η : ℝ} (hδ : 0 < δ) (z : E) :
    ∃ G : Finset Time, ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      (Y : Ω → D E) (R : ℝ),
      μ {ω | ∃ s ≤ T, R + η < dist ((Y ω).1 s) z} ≤
        μ {ω | ¬ HasOscillationPartition (Y ω) (T + 1) δ η} +
          ∑ u ∈ G, μ {ω | R < dist ((Y ω).1 u) z} := by
  classical
  obtain ⟨G, hG⟩ := exists_finite_observations_of_oscillation_partition (E := E) T hδ
  refine ⟨G, ?_⟩
  intro Ω mΩ μ Y R
  calc
    _ ≤ μ ({ω | ¬ HasOscillationPartition (Y ω) (T + 1) δ η} ∪
        ⋃ u ∈ G, {ω | R < dist ((Y ω).1 u) z}) := by
      apply measure_mono
      rintro ω ⟨s, hs, hout⟩
      by_cases hp : HasOscillationPartition (Y ω) (T + 1) δ η
      · right
        obtain ⟨u, hu, hdist⟩ := hG (Y ω) hp s hs
        have ht := dist_triangle ((Y ω).1 s) ((Y ω).1 u) z
        have huout : R < dist ((Y ω).1 u) z := by linarith
        exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, huout⟩⟩
      · exact Or.inl hp
    _ ≤ μ {ω | ¬ HasOscillationPartition (Y ω) (T + 1) δ η} +
        μ (⋃ u ∈ G, {ω | R < dist ((Y ω).1 u) z}) := measure_union_le _ _
    _ ≤ _ := add_le_add_right (measure_biUnion_finset_le G _) _

/-- Uniform one-time tail bounds extend to a finite observation set with one common radius. -/
theorem exists_radius_for_finite_observations
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → D E) (z : E)
    (G : Finset Time) (p : ℝ≥0∞)
    (h : ∀ u : Time, ∃ R : ℝ, ∀ n,
      P n {ω | R < dist ((Y n ω).1 u) z} ≤ p) :
    ∃ R : ℝ, ∀ n u, u ∈ G →
      P n {ω | R < dist ((Y n ω).1 u) z} ≤ p := by
  classical
  choose radius hradius using h
  obtain ⟨R, hR⟩ := (G.image radius).bddAbove
  refine ⟨R, fun n u hu => ?_⟩
  have huR : radius u ≤ R := hR (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  exact (measure_mono (fun ω hω => lt_of_le_of_lt huR hω)).trans (hradius u n)

/-- Uniform marginal tails and a partition estimate control excursions through a fixed horizon. -/
theorem exists_radius_measure_excursion_le
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → D E) (z : E)
    (T : Time) {δ η : ℝ} (hδ : 0 < δ) (p : ℝ≥0∞)
    (h : ∀ u : Time, ∃ R : ℝ, ∀ n,
      P n {ω | R < dist ((Y n ω).1 u) z} ≤ p) :
    ∃ (G : Finset Time) (R : ℝ), ∀ n,
      P n {ω | ∃ s ≤ T, R + η < dist ((Y n ω).1 s) z} ≤
        P n {ω | ¬ HasOscillationPartition (Y n ω) (T + 1) δ η} + ∑ _u ∈ G, p := by
  obtain ⟨G, hG⟩ := exists_finite_observations_measure_le T hδ z
  obtain ⟨R, hR⟩ := exists_radius_for_finite_observations P Y z G p h
  refine ⟨G, R, fun n => (hG (P n) (Y n) R).trans ?_⟩
  exact add_le_add_right (Finset.sum_le_sum fun u hu => hR n u hu) _

/-- Uniform marginal tightness and partition estimates imply compact containment in a proper
state space. -/
theorem exists_compact_measure_excursion_le [ProperSpace E]
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Y : ∀ n, Ω n → D E) (z : E) (T : Time)
    (hmarg : ∀ (u : Time) (p : ℝ), 0 < p → ∃ R : ℝ, ∀ n,
      P n {ω | R < dist ((Y n ω).1 u) z} ≤ ENNReal.ofReal p)
    (hpart : ∀ p : ℝ, 0 < p → ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      P n {ω | ¬ HasOscillationPartition (Y n ω) (T + 1) δ 1} ≤ ENNReal.ofReal p)
    {p : ℝ} (hp : 0 < p) :
    ∃ S : Set E, IsCompact S ∧ ∀ n,
      P n {ω | ∃ s ≤ T, (Y n ω).1 s ∉ S} ≤ ENNReal.ofReal p := by
  obtain ⟨δ, hδ, hpartδ⟩ := hpart (p / 2) (by linarith)
  obtain ⟨G, hG⟩ := exists_finite_observations_measure_le (E := E) (η := 1) T hδ z
  let q : ℝ := p / (2 * ((G.card : ℝ) + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨R, hR⟩ := exists_radius_for_finite_observations P Y z G (ENNReal.ofReal q)
    (fun u => hmarg u q hq)
  refine ⟨Metric.closedBall z (R + 1), isCompact_closedBall _ _, fun n => ?_⟩
  have hsum : (∑ _u ∈ G, ENNReal.ofReal q) ≤ ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hq.le)]
    apply ENNReal.ofReal_le_ofReal
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [q]
    have hc : 0 ≤ (G.card : ℝ) := Nat.cast_nonneg _
    have hd : 0 < 2 * ((G.card : ℝ) + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound := (hG (P n) (Y n) R).trans
    (add_le_add (hpartδ n) (Finset.sum_le_sum fun u hu => hR n u hu))
  have ht : ENNReal.ofReal (p / 2) + ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring
  have hset : {ω | ∃ s ≤ T, (Y n ω).1 s ∉ Metric.closedBall z (R + 1)} =
      {ω | ∃ s ≤ T, R + 1 < dist ((Y n ω).1 s) z} := by
    ext ω
    simp only [Metric.mem_closedBall, not_le]
  rw [hset]
  exact hbound.trans ((add_le_add le_rfl hsum).trans_eq ht)

end LatticeProb.Cadlag.HalfLine
