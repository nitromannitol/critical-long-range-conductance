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


/-- Before the first oscillation time, the distance from the starting value
cannot exceed the threshold. -/
theorem dist_le_of_lt_nextOscillationTime {Ω : Type} (Y : Ω → D E) (τ : Ω → Time)
    (T : Time) {η : ℝ} (hη : 0 ≤ η) (w : Ω) {s : Time}
    (hτs : τ w ≤ s) (hs : s < nextOscillationTime Y τ T η w) :
    dist ((Y w).1 (τ w)) ((Y w).1 s) ≤ η := by
  by_cases heq : τ w = s
  · rw [← heq, dist_self]
    exact hη
  · have hlt : τ w < s := lt_of_le_of_ne hτs heq
    by_contra hbad
    have hdist : η < dist ((Y w).1 (τ w)) ((Y w).1 s) := lt_of_not_ge hbad
    have hle : nextOscillationTime Y τ T η w ≤ s := by
      apply csInf_le ⟨0, fun _ _ => zero_le⟩
      exact mem_insert_of_mem T ⟨hlt, hdist⟩
    exact (not_lt_of_ge hle) hs



/-- Before the cap, the next positive-threshold oscillation occurs strictly
later than its starting time. -/
theorem lt_nextOscillationTime {Ω : Type} (Y : Ω → D E) (τ : Ω → Time)
    (T : Time) {η : ℝ} (hη : 0 < η) (w : Ω) (hτT : τ w < T) :
    τ w < nextOscillationTime Y τ T η w := by
  obtain ⟨d, hd, hclose⟩ := Metric.continuousWithinAt_iff.mp ((Y w).2.1 (τ w)) η hη
  let r : Time := min T (τ w + (d / 2).toNNReal)
  have hd2 : 0 < d / 2 := half_pos hd
  have hτr : τ w < r := by
    apply lt_min hτT
    exact lt_add_of_pos_right _ (Real.toNNReal_pos.mpr hd2)
  have hbound : r ≤ nextOscillationTime Y τ T η w := by
    apply le_csInf ⟨T, mem_insert _ _⟩
    intro u hu
    rcases mem_insert_iff.mp hu with rfl | hu
    · exact min_le_left _ _
    · by_contra hru
      have hur : u < r := lt_of_not_ge hru
      have hud : dist u (τ w) < d := by
        have hle : u < τ w + (d / 2).toNNReal := hur.trans_le (min_le_right _ _)
        change dist (u : ℝ) (τ w : ℝ) < d
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (NNReal.coe_lt_coe.mpr hu.1))]
        have hle' : (u : ℝ) < (τ w : ℝ) + d / 2 := by
          have hh := NNReal.coe_lt_coe.mpr hle
          simpa only [NNReal.coe_add, Real.coe_toNNReal _ hd2.le] using hh
        linarith
      have hdist := hclose hu.1.le hud
      rw [dist_comm] at hdist
      exact (not_lt_of_ge hdist.le) hu.2
  exact hτr.trans_le hbound

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
          simp only [oscillationTime, mem_ofPred_eq, mem_univ, ht]
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

omit [MeasurableSpace E] [BorelSpace E] [SeparableSpace E] in
/-- An oscillation time strictly before the cap reaches the threshold. -/
theorem le_dist_oscillationTime_succ {Ω : Type} (Y : Ω → D E)
    (T : Time) (η : ℝ) (k : ℕ) (w : Ω)
    (hT : oscillationTime Y T η (k + 1) w < T) :
    η ≤ dist ((Y w).1 (oscillationTime Y T η k w))
      ((Y w).1 (oscillationTime Y T η (k + 1) w)) :=
  le_dist_nextOscillationTime Y (oscillationTime Y T η k) T η w hT

omit [MeasurableSpace E] [BorelSpace E] [SeparableSpace E] in
/-- Two values between successive oscillation times are within twice the
threshold. -/
theorem dist_le_between_oscillationTimes {Ω : Type} (Y : Ω → D E)
    (T : Time) {η : ℝ} (hη : 0 ≤ η) (k : ℕ) (w : Ω) {s u : Time}
    (hks : oscillationTime Y T η k w ≤ s)
    (hs : s < oscillationTime Y T η (k + 1) w)
    (hku : oscillationTime Y T η k w ≤ u)
    (hu : u < oscillationTime Y T η (k + 1) w) :
    dist ((Y w).1 s) ((Y w).1 u) ≤ 2 * η := by
  have hs' := dist_le_of_lt_nextOscillationTime Y (oscillationTime Y T η k) T hη w hks hs
  have hu' := dist_le_of_lt_nextOscillationTime Y (oscillationTime Y T η k) T hη w hku hu
  have htri := dist_triangle ((Y w).1 s) ((Y w).1 (oscillationTime Y T η k w)) ((Y w).1 u)
  have hs'' : dist ((Y w).1 s) ((Y w).1 (oscillationTime Y T η k w)) ≤ η := by
    simpa only [dist_comm] using hs'
  linarith


omit [MeasurableSpace E] [BorelSpace E] [SeparableSpace E] in
/-- The successive positive-threshold oscillation times cannot accumulate
strictly before their cap. -/
theorem exists_le_oscillationTime {Ω : Type} (Y : Ω → D E) (T t : Time)
    (ht : t < T) {η : ℝ} (hη : 0 < η) (w : Ω) :
    ∃ k : ℕ, t ≤ oscillationTime Y T η k w := by
  classical
  by_contra hnone
  push Not at hnone
  let α : ℕ → Time := fun k => oscillationTime Y T η k w
  have hα (k : ℕ) : α k < t := hnone k
  have hstrict : StrictMono α := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact lt_nextOscillationTime Y (oscillationTime Y T η k) T hη w ((hα k).trans ht)
  have hbdd : BddAbove (range α) := ⟨t, fun _ ⟨k, hk⟩ => hk ▸ (hα k).le⟩
  let L : Time := ⨆ k, α k
  have hlim : Tendsto α atTop (𝓝 L) := tendsto_atTop_ciSup hstrict.monotone hbdd
  have hbelow (k : ℕ) : α k < L := (hstrict (Nat.lt_succ_self k)).trans_le (le_ciSup hbdd (k + 1))
  have hLpos : 0 < L := by
    have hzero : α 0 = 0 := rfl
    simpa only [hzero] using hbelow 0
  have hwithin : Tendsto α atTop (𝓝[<] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hbelow⟩
  obtain ⟨v, hv⟩ := (Y w).2.2 L hLpos
  have hx : Tendsto (fun k => (Y w).1 (α k)) atTop (𝓝 v) := hv.comp hwithin
  have hdist : Tendsto (fun k => dist ((Y w).1 (α k)) ((Y w).1 (α (k + 1))))
      atTop (𝓝 0) := by
    simpa only [dist_self, Function.comp_def] using hx.dist (hx.comp (Filter.tendsto_add_atTop_nat 1))
  obtain ⟨k, hk⟩ := (hdist.eventually (Iio_mem_nhds hη)).exists
  have hlarge := le_dist_oscillationTime_succ Y T η k w ((hα (k + 1)).trans ht)
  exact (not_lt_of_ge hlarge) hk

end LatticeProb.Cadlag.HalfLine
