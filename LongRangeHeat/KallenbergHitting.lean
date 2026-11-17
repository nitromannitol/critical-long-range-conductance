import LongRangeHeat.KallenbergStoppedValue

/-!
# Weakly optional oscillation times

Right continuity reduces strict threshold exceedances to a countable set of
evaluation times.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology NNReal

variable {E : Type} [MetricSpace E]

/-- A strict pathwise threshold exceedance before a horizon is witnessed at a
positive rational time before the horizon. -/
theorem exists_rat_of_right_exceed (x : D E) (s u t : Time) (η : ℝ)
    (hsu : s < u) (hut : u < t) (he : η < dist (x.1 s) (x.1 u)) :
    ∃ q : ℚ, s < ((q : ℝ).toNNReal) ∧ ((q : ℝ).toNNReal) < t ∧
      η < dist (x.1 s) (x.1 ((q : ℝ).toNNReal)) := by
  have hc : ContinuousWithinAt (fun v => dist (x.1 s) (x.1 v)) (Ici u) u :=
    continuousWithinAt_const.dist (x.2.1 u)
  obtain ⟨d, hd, hclose⟩ := Metric.continuousWithinAt_iff.mp hc
    (dist (x.1 s) (x.1 u) - η) (by linarith)
  have hr : (u : ℝ) < min (t : ℝ) ((u : ℝ) + d / 2) := by
    apply lt_min
    · exact_mod_cast hut
    · linarith
  obtain ⟨q, hqu, hqt⟩ := exists_rat_btwn hr
  have hq0 : 0 ≤ (q : ℝ) := le_trans u.2 hqu.le
  let r : Time := (q : ℝ).toNNReal
  have hrval : (r : ℝ) = q := Real.coe_toNNReal _ hq0
  have hur : u < r := by
    apply NNReal.coe_lt_coe.mp
    simpa only [hrval] using hqu
  have hrt : r < t := by
    apply NNReal.coe_lt_coe.mp
    rw [hrval]
    exact hqt.trans_le (min_le_left _ _)
  have hru : dist r u < d := by
    change dist (r : ℝ) (u : ℝ) < d
    rw [Real.dist_eq, abs_of_pos (by rw [hrval]; linarith)]
    rw [hrval]
    linarith [hqt.trans_le (min_le_right (t : ℝ) ((u : ℝ) + d / 2))]
  have hdiff := hclose hur.le hru
  have hdiff' : |dist (x.1 s) (x.1 r) - dist (x.1 s) (x.1 u)| <
      dist (x.1 s) (x.1 u) - η := by simpa only [Real.dist_eq] using hdiff
  refine ⟨q, hsu.trans hur, hrt, ?_⟩
  linarith [(abs_lt.mp hdiff').1]


/-- The first strict oscillation time after `τ`, capped at `T`. -/
noncomputable def nextOscillationTime {Ω : Type} (Y : Ω → D E)
    (τ : Ω → Time) (T : Time) (η : ℝ) (w : Ω) : Time :=
  sInf (insert T {u | τ w < u ∧ η < dist ((Y w).1 (τ w)) ((Y w).1 u)})

/-- The capped oscillation time is no later than its cap. -/
theorem nextOscillationTime_le {Ω : Type} (Y : Ω → D E) (τ : Ω → Time)
    (T : Time) (η : ℝ) (w : Ω) : nextOscillationTime Y τ T η w ≤ T := by
  apply csInf_le ⟨0, fun _ _ => zero_le⟩
  exact mem_insert _ _

/-- The capped oscillation time is no earlier than its starting time. -/
theorem le_nextOscillationTime {Ω : Type} (Y : Ω → D E) (τ : Ω → Time)
    (T : Time) (η : ℝ) (w : Ω) (hτ : τ w ≤ T) :
    τ w ≤ nextOscillationTime Y τ T η w := by
  apply le_csInf ⟨T, mem_insert _ _⟩
  intro u hu
  rcases mem_insert_iff.mp hu with rfl | hu
  · exact hτ
  · exact hu.1.le

/-- The strict comparison event for the next oscillation time has a countable
rational description. -/
theorem nextOscillationTime_lt_iff {Ω : Type} (Y : Ω → D E) (τ : Ω → Time)
    (T : Time) (η : ℝ) (w : Ω) (t : Time) :
    nextOscillationTime Y τ T η w < t ↔ T < t ∨
      ∃ q : ℚ, τ w < ((q : ℝ).toNNReal) ∧ ((q : ℝ).toNNReal) < t ∧
        η < dist ((Y w).1 (τ w)) ((Y w).1 ((q : ℝ).toNNReal)) := by
  rw [nextOscillationTime, csInf_lt_iff ⟨0, fun _ _ => zero_le⟩ ⟨T, mem_insert _ _⟩]
  constructor
  · rintro ⟨u, hu, hut⟩
    rcases mem_insert_iff.mp hu with rfl | hu
    · exact Or.inl hut
    · exact Or.inr (exists_rat_of_right_exceed (Y w) (τ w) u t η hu.1 hut hu.2)
  · rintro (h | ⟨q, hτ, hqt, hq⟩)
    · exact ⟨T, mem_insert _ _, h⟩
    · exact ⟨(q : ℝ).toNNReal, mem_insert_of_mem T ⟨hτ, hq⟩, hqt⟩


/-- If the capped first oscillation occurs before the cap, its size reaches the
threshold. -/
theorem le_dist_nextOscillationTime {Ω : Type} (Y : Ω → D E) (τ : Ω → Time)
    (T : Time) (η : ℝ) (w : Ω) (hT : nextOscillationTime Y τ T η w < T) :
    η ≤ dist ((Y w).1 (τ w)) ((Y w).1 (nextOscillationTime Y τ T η w)) := by
  let S : Set Time := insert T {u | τ w < u ∧ η < dist ((Y w).1 (τ w)) ((Y w).1 u)}
  have hS : S.Nonempty := ⟨T, mem_insert _ _⟩
  have hSb : BddBelow S := ⟨0, fun _ _ => zero_le⟩
  obtain ⟨u, _, hu, huS⟩ := exists_seq_tendsto_sInf hS hSb
  have hwithin : Tendsto u atTop (𝓝[Ici (sInf S)] (sInf S)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hu, Eventually.of_forall fun k => csInf_le hSb (huS k)⟩
  have hdist : Tendsto (fun k => dist ((Y w).1 (τ w)) ((Y w).1 (u k))) atTop
      (𝓝 (dist ((Y w).1 (τ w)) ((Y w).1 (sInf S)))) :=
    tendsto_const_nhds.dist (((Y w).2.1 (sInf S)).tendsto.comp hwithin)
  change η ≤ dist ((Y w).1 (τ w)) ((Y w).1 (sInf S))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hdist
  have hlt : sInf S < T := hT
  filter_upwards [hu.eventually (Iio_mem_nhds hlt)] with k hk
  rcases mem_insert_iff.mp (huS k) with heq | hex
  · exact (lt_irrefl T (heq ▸ hk)).elim
  · exact hex.2.le

variable [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]

/-- A capped first oscillation after a weakly optional time is weakly optional. -/
theorem weakNaturalStopping_nextOscillationTime {Ω : Type} {Y : Ω → D E}
    {τ : Ω → Time} {T : Time} {η : ℝ}
    (hτ : weakNaturalStopping Y (T : ℝ) τ) :
    weakNaturalStopping Y (T : ℝ) (nextOscillationTime Y τ T η) := by
  constructor
  · intro w
    exact NNReal.coe_le_coe.mpr (nextOscillationTime_le Y τ T η w)
  · intro t
    by_cases hTt : T < t
    · have heq : {w | nextOscillationTime Y τ T η w < t} = univ := by
        ext w
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact (nextOscillationTime_le Y τ T η w).trans_lt hTt
      rw [heq]
      exact @MeasurableSet.univ Ω (naturalSigma Y t)
    · let s (q : ℚ) : Time := (q : ℝ).toNNReal
      have hevent : {w | nextOscillationTime Y τ T η w < t} =
          ⋃ q : ℚ, {w | s q < t ∧ τ w < s q ∧
            η < dist ((Y w).1 (τ w)) ((Y w).1 (s q))} := by
        ext w
        simp only [mem_ofPred_eq, mem_iUnion, nextOscillationTime_lt_iff,
          hTt, false_or]
        constructor
        · rintro ⟨q, h1, h2, h3⟩
          exact ⟨q, h2, h1, h3⟩
        · rintro ⟨q, h2, h1, h3⟩
          exact ⟨q, h1, h2, h3⟩
      rw [hevent]
      apply MeasurableSet.iUnion
      intro q
      by_cases hqt : s q < t
      · let : MeasurableSpace Ω := naturalSigma Y t
        have hτevent : MeasurableSet[naturalSigma Y t] {w | τ w < s q} :=
          naturalSigma_mono Y hqt.le _ (hτ.2 (s q))
        have hYq : Measurable[naturalSigma Y t] (fun w => (Y w).1 (s q)) := by
          rw [measurable_iff_comap_le]
          exact le_iSup_of_le (s q) (le_iSup_of_le hqt.le le_rfl)
        have hYτ := hτ.measurable_stopped_min t
        have hdist : MeasurableSet[naturalSigma Y t] {w |
            η < dist ((Y w).1 (min (τ w) t)) ((Y w).1 (s q))} :=
          measurableSet_lt measurable_const (hYτ.dist hYq)
        have heq : {w | s q < t ∧ τ w < s q ∧ η < dist ((Y w).1 (τ w)) ((Y w).1 (s q))} =
            {w | τ w < s q} ∩ {w | η < dist ((Y w).1 (min (τ w) t)) ((Y w).1 (s q))} := by
          ext w
          simp only [mem_ofPred_eq, hqt, true_and, mem_inter_iff]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by simpa only [min_eq_left (h1.trans hqt).le] using h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by simpa only [min_eq_left (h1.trans hqt).le] using h2⟩
        rw [heq]
        exact hτevent.inter hdist
      · have heq : {w | s q < t ∧ τ w < s q ∧ η < dist ((Y w).1 (τ w)) ((Y w).1 (s q))} = ∅ := by
          ext w
          simp only [mem_ofPred_eq, hqt, false_and, mem_empty_iff_false]
        rw [heq]
        exact @MeasurableSet.empty Ω (naturalSigma Y t)


/-- The successive capped oscillation times of a càdlàg process. -/
noncomputable def oscillationTime {Ω : Type} (Y : Ω → D E) (T : Time) (η : ℝ) : ℕ → Ω → Time
  | 0 => fun _ => 0
  | k + 1 => nextOscillationTime Y (oscillationTime Y T η k) T η

/-- Every successive oscillation time is weakly optional and bounded by the cap. -/
theorem weakNaturalStopping_oscillationTime {Ω : Type} (Y : Ω → D E)
    (T : Time) (η : ℝ) (k : ℕ) :
    weakNaturalStopping Y (T : ℝ) (oscillationTime Y T η k) := by
  induction k with
  | zero =>
    constructor
    · intro w
      exact T.2
    · intro t
      by_cases ht : 0 < t
      · have heq : {w : Ω | oscillationTime Y T η 0 w < t} = univ := by
          ext w
          simp only [oscillationTime, mem_ofPred_eq, mem_univ, iff_true, ht]
        rw [heq]
        exact @MeasurableSet.univ Ω (naturalSigma Y t)
      · have heq : {w : Ω | oscillationTime Y T η 0 w < t} = ∅ := by
          ext w
          simp only [oscillationTime, mem_ofPred_eq, ht, mem_empty_iff_false]
        rw [heq]
        exact @MeasurableSet.empty Ω (naturalSigma Y t)
  | succ k ih =>
    exact weakNaturalStopping_nextOscillationTime ih

/-- Successive oscillation times are ordered. -/
theorem oscillationTime_le_succ {Ω : Type} (Y : Ω → D E)
    (T : Time) (η : ℝ) (k : ℕ) (w : Ω) :
    oscillationTime Y T η k w ≤ oscillationTime Y T η (k + 1) w := by
  apply le_nextOscillationTime
  exact NNReal.coe_le_coe.mp ((weakNaturalStopping_oscillationTime Y T η k).1 w)

/-- An oscillation time strictly before the cap reaches the threshold. -/
theorem le_dist_oscillationTime_succ {Ω : Type} (Y : Ω → D E)
    (T : Time) (η : ℝ) (k : ℕ) (w : Ω)
    (hT : oscillationTime Y T η (k + 1) w < T) :
    η ≤ dist ((Y w).1 (oscillationTime Y T η k w))
      ((Y w).1 (oscillationTime Y T η (k + 1) w)) :=
  le_dist_nextOscillationTime Y (oscillationTime Y T η k) T η w hT

end LatticeProb.Cadlag.HalfLine
