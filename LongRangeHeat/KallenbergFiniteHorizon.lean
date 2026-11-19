import LongRangeHeat.KallenbergStepConvergence

/-!
# Finite-horizon approximation

Uniform approximation on a finite time interval controls the half-line
Skorokhod distance up to an exponentially small tail.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- A uniform state-distance estimate through `T` gives a path-distance
estimate with an exponentially small tail. -/
theorem dist_le_of_finite_horizon {E : Type*} [MetricSpace E]
    (x y : D E) (T : Time) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ t ≤ T, dist (x.1 t) (y.1 t) ≤ ε) :
    dist x y ≤ ε + Real.exp (-(T : ℝ)) := by
  have hsup : (⨆ t ≤ T, q (x.1 t) (y.1 t)) ≤ ENNReal.ofReal ε := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact (min_le_left _ _).trans (by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (h t ht))
  have hext : skorohodDistanceExtended x y ≤
      ENNReal.ofReal (ε + Real.exp (-(T : ℝ))) := by
    calc
      _ ≤ _ := skorohodDistanceExtended_le_uniform x y
      _ ≤ (⨆ t ≤ T, q (x.1 t) (y.1 t)) +
          ENNReal.ofReal (Real.exp (-(T : ℝ))) := uniformIntegral_le x y T
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (Real.exp (-(T : ℝ))) :=
        add_le_add hsup le_rfl
      _ = _ := by rw [ENNReal.ofReal_add hε (Real.exp_nonneg _)]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hε (Real.exp_nonneg _)) hext


/-- Before the last threshold, dropping that threshold does not change the
selected step interval. -/
theorem stepIndex_drop_last (N : ℕ) (s : Fin (N + 1) → Time) (t : Time)
    (ht : t < s (Fin.last N)) :
    stepIndex s t = (stepIndex (fun i : Fin N => s i.castSucc) t).castSucc := by
  induction N with
  | zero =>
    have h : t < s 0 := by simpa only [Fin.last_zero] using ht
    simp only [stepIndex, h, ↓reduceIte]
    rfl
  | succ N ih =>
    change (if t < s 0 then 0 else (stepIndex (fun i => s i.succ) t).succ) =
      (if t < s 0 then 0 else
        (stepIndex (fun i => s i.succ.castSucc) t).succ).castSucc
    split_ifs with h
    · rfl
    · have htail : t < (fun i : Fin (N + 1) => s i.succ) (Fin.last N) := by
        simpa only [Fin.succ_last] using ht
      have hindex := ih (fun i : Fin (N + 1) => s i.succ) htail
      apply Fin.ext
      simpa only [Fin.val_succ, Fin.val_castSucc, Fin.castSucc_succ] using
        congrArg (fun i => i.val + 1) hindex


/-- A path with small oscillation on partition intervals is close to the
step path formed from nonterminal cuts and their left endpoint values. -/
theorem dist_stepPath_nonterminal_le_of_oscillation {E : Type*} [MetricSpace E]
    (x : D E) (N : ℕ) (cut : Fin (N + 2) → Time)
    (hmono : Monotone cut) (hzero : cut 0 = 0) (T : Time)
    (hT : T < cut (Fin.last (N + 1))) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ i : Fin (N + 1), ∀ a : Time,
      a ≤ T → cut i.castSucc ≤ a → a < cut i.succ →
      dist (x.1 a) (x.1 (cut i.castSucc)) ≤ ε) :
    dist x (stepPath (fun i : Fin N => cut i.succ.castSucc)
      (fun i : Fin (N + 1) => x.1 (cut i.castSucc))) ≤
        ε + Real.exp (-(T : ℝ)) := by
  apply dist_le_of_finite_horizon x _ T hε
  intro t ht
  have hfull := dist_stepPath_le_of_oscillation x (N + 1) cut hmono hzero T hT ε hosc t ht
  have hidx := stepIndex_drop_last N (fun i : Fin (N + 1) => cut i.succ) t (ht.trans_lt hT)
  change dist (x.1 t) (x.1 (cut (stepIndex (fun i : Fin (N + 1) => cut i.succ) t))) ≤ ε at hfull
  change dist (x.1 t) (x.1 (cut (stepIndex (fun i : Fin N => cut i.succ.castSucc) t).castSucc)) ≤ ε
  rw [hidx] at hfull
  simpa only [Fin.castSucc_succ] using hfull


/-- Oscillation partitions and compact state values yield a subsequence close
on a shorter horizon to a single limiting step path. -/
theorem exists_subseq_near_stepPath {E : Type} [MetricSpace E]
    (S : Set E) (hS : IsCompact S) (t T : Time) (hT : T < t)
    {δ η ρ : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hρ : 0 < ρ)
    (x : ℕ → D E) (hx : ∀ n, HasOscillationPartition (x n) t δ η)
    (hcompact : ∀ n s, s ≤ t → (x n).1 s ∈ S) :
    ∃ (φ : ℕ → ℕ) (y : D E), StrictMono φ ∧
      ∀ᶠ n in atTop, dist (x (φ n)) y < η + Real.exp (-(T : ℝ)) + ρ := by
  obtain ⟨φ, k, cut, limit, v, hφ, hk, hp, hlimit, hv, hzero, hlast,
    horder, hwidth, hcuts, hvalues⟩ :=
    exists_subseq_oscillation_partitions S hS t hδ x hx hcompact
  cases k with
  | zero => omega
  | succ N =>
    let c : ℕ → Fin (N + 2) → Time := fun n i => cut n i.val
    let s : Fin N → Time := fun i => limit i.succ.castSucc
    let r : ℕ → Fin N → Time := fun n i => c n i.succ.castSucc
    let w : ℕ → Fin (N + 1) → E := fun n i => (x (φ n)).1 (c n i.castSucc)
    let z : Fin (N + 1) → E := fun i => v i.castSucc
    have hstrict : StrictMono (fun i : Fin (N + 1) => limit i.castSucc) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      have hw := hwidth i.castSucc (by simp only [Fin.val_castSucc]; omega)
      have heq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
      change limit i.castSucc.castSucc < limit i.succ.castSucc
      rw [← heq]
      exact_mod_cast (show (limit i.castSucc.castSucc : ℝ) < limit i.castSucc.succ by linarith)
    have hs : StrictMono s := fun i j hij => hstrict (Fin.succ_lt_succ_iff.mpr hij)
    have hspos : ∀ i, 0 < s i := by
      intro i
      have h0 : limit (0 : Fin (N + 1)).castSucc = 0 := by simpa using hzero
      rw [← h0]
      exact hstrict (show (0 : Fin (N + 1)) < i.succ from by simp)
    have hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 (s i)) :=
      fun i => hcuts i.succ.castSucc
    have hw : Tendsto w atTop (𝓝 z) := by
      apply tendsto_pi_nhds.mpr
      intro i
      exact hvalues i.castSucc
    have hstep := tendsto_stepPath_of_positive_cuts_and_values N s r z w hs.injective hspos hr hw
    have hnear : ∀ n, dist (x (φ n)) (stepPath (r n) (w n)) ≤
        η + Real.exp (-(T : ℝ)) := by
      intro n
      have hcmono : Monotone (c n) := by
        apply (Fin.monotone_iff_le_succ).mpr
        intro i
        exact (hp n).2.2.1 i.val i.isLt |>.le
      have hcT : T < c n (Fin.last (N + 1)) := by
        simpa only [c, Fin.val_last, (hp n).2.1] using hT
      apply dist_stepPath_nonterminal_le_of_oscillation (x (φ n)) N (c n)
        hcmono (hp n).1 T hcT hη
      intro i a ha hlo hhi
      exact (hp n).2.2.2.2 i.val i.isLt a (c n i.castSucc) hlo hhi le_rfl
        ((hp n).2.2.1 i.val i.isLt)
    refine ⟨φ, stepPath s z, hφ, ?_⟩
    filter_upwards [Metric.tendsto_nhds.mp hstep ρ hρ] with n hn
    exact lt_of_le_of_lt (dist_triangle _ _ _) (by linarith [hnear n])


/-- A uniform subsequence approximation property implies total boundedness. -/
theorem totallyBounded_of_subseq_near {E : Type*} [MetricSpace E] (A : Set E)
    (h : ∀ ε > 0, ∀ x : ℕ → E, (∀ n, x n ∈ A) →
      ∃ (φ : ℕ → ℕ) (y : E), StrictMono φ ∧
        ∀ᶠ n in atTop, dist (x (φ n)) y < ε) : TotallyBounded A := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  by_contra hn
  have hgen : ∀ t : Set E, t.Finite → ∃ c, c ∈ A ∧ ∀ y ∈ t, ε ≤ dist c y := by
    intro t ht
    have hnot : ¬ A ⊆ ⋃ y ∈ t, Metric.ball y ε := fun hc => hn ⟨t, ht, hc⟩
    obtain ⟨c, hc, hct⟩ := Set.not_subset.mp hnot
    refine ⟨c, hc, fun y hy => ?_⟩
    have : c ∉ Metric.ball y ε := fun hb => hct (mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hb⟩⟩)
    exact le_of_not_gt this
  obtain ⟨x, hx⟩ := seq_of_forall_finite_exists hgen
  have hxA : ∀ n, x n ∈ A := fun n => (hx n).1
  have hsep : ∀ n m, m < n → ε ≤ dist (x n) (x m) := by
    intro n m hmn
    exact (hx n).2 (x m) ⟨m, hmn, rfl⟩
  obtain ⟨φ, y, hφ, hevent⟩ := h (ε / 3) (by positivity) x hxA
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  have h1 := hM M le_rfl
  have h2 := hM (M + 1) (by omega)
  have h3 := hsep (φ (M + 1)) (φ M) (hφ (by omega))
  have h4 := dist_triangle (x (φ (M + 1))) y (x (φ M))
  rw [dist_comm y (x (φ M))] at h4
  linarith

/-- Compact containment and arbitrarily fine oscillation partitions on every
finite horizon imply total boundedness in the half-line path metric. -/
theorem totallyBounded_of_oscillation_partitions {E : Type} [MetricSpace E]
    (A : Set (D E))
    (hcompact : ∀ t : Time, ∃ S : Set E, IsCompact S ∧
      ∀ x ∈ A, ∀ s ≤ t, x.1 s ∈ S)
    (hpartition : ∀ (t : Time) (η : ℝ), 0 < η → ∃ δ > 0,
      ∀ x ∈ A, HasOscillationPartition x t δ η) : TotallyBounded A := by
  apply totallyBounded_of_subseq_near A
  intro ε hε x hx
  have he : 0 < ε / 4 := by positivity
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he))
  let T : Time := ⟨max R 0, le_max_right _ _⟩
  have htail : Real.exp (-(T : ℝ)) < ε / 4 := hR _ (le_max_left _ _)
  let t : Time := T + 1
  have hT : T < t := by dsimp [t]; exact lt_add_of_pos_right _ zero_lt_one
  obtain ⟨S, hS, hvalue⟩ := hcompact t
  obtain ⟨δ, hδ, hpart⟩ := hpartition t (ε / 4) he
  obtain ⟨φ, y, hφ, hnear⟩ := exists_subseq_near_stepPath S hS t T hT hδ he.le he x
    (fun n => hpart (x n) (hx n)) (fun n s hs => hvalue (x n) (hx n) s hs)
  refine ⟨φ, y, hφ, ?_⟩
  filter_upwards [hnear] with n hn
  linarith


/-- A countable sequence of increasing horizons and vanishing oscillation
scales suffices for total boundedness. -/
theorem totallyBounded_of_partition_sequence {E : Type} [MetricSpace E]
    (A : Set (D E)) (t : ℕ → Time) (η δ : ℕ → ℝ)
    (ht : Tendsto t atTop atTop) (hη : Tendsto η atTop (𝓝 0))
    (hηpos : ∀ k, 0 < η k) (hδ : ∀ k, 0 < δ k)
    (hcompact : ∀ k, ∃ S : Set E, IsCompact S ∧
      ∀ x ∈ A, ∀ s ≤ t k, x.1 s ∈ S)
    (hpartition : ∀ k, ∀ x ∈ A, HasOscillationPartition x (t k) (δ k) (η k)) :
    TotallyBounded A := by
  apply totallyBounded_of_subseq_near A
  intro ε hε x hx
  have he : 0 < ε / 4 := by positivity
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he))
  let T : Time := ⟨max R 0, le_max_right _ _⟩
  have htail : Real.exp (-(T : ℝ)) < ε / 4 := hR _ (le_max_left _ _)
  have hevent : ∀ᶠ k in atTop, T + 1 ≤ t k ∧ η k < ε / 4 := by
    filter_upwards [ht (eventually_ge_atTop (T + 1)), hη (Iio_mem_nhds he)] with k hk hl
    exact ⟨hk, hl⟩
  obtain ⟨k, hk⟩ := hevent.exists
  have hT : T < t k := (lt_add_of_pos_right T zero_lt_one).trans_le hk.1
  obtain ⟨S, hS, hvalue⟩ := hcompact k
  obtain ⟨φ, y, hφ, hnear⟩ := exists_subseq_near_stepPath S hS (t k) T hT
    (hδ k) (hηpos k).le he x (fun n => hpartition k (x n) (hx n))
      (fun n s hs => hvalue (x n) (hx n) s hs)
  refine ⟨φ, y, hφ, ?_⟩
  filter_upwards [hnear] with n hn
  linarith [hk.2]

end LatticeProb.Cadlag.HalfLine
