import LongRangeHeat.KallenbergModulus

/-!
# Compactness of partition points

Finite vectors of partition points in a bounded interval admit convergent
subsequences.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter Set
open scoped Topology

/-- A sequence of finite vectors of points in a bounded time interval has a
subsequence converging at every coordinate. -/
theorem exists_subseq_partition_points (t : Time) (N : ℕ)
    (cut : ℕ → Fin N → Time) (hcut : ∀ n i, cut n i ≤ t) :
    ∃ (φ : ℕ → ℕ) (limit : Fin N → Time), StrictMono φ ∧
      (∀ i, limit i ≤ t) ∧ ∀ i, Tendsto (fun n => cut (φ n) i) atTop (𝓝 (limit i)) := by
  let S : Set (Fin N → Time) := Set.pi univ (fun _ => Icc 0 t)
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hm : ∀ n, cut n ∈ S := by
    intro n i _
    exact ⟨zero_le, hcut n i⟩
  obtain ⟨limit, hlimit, φ, hφ, hlim⟩ := hS.tendsto_subseq hm
  refine ⟨φ, limit, hφ, fun i => (hlimit i (mem_univ i)).2, ?_⟩
  exact (tendsto_pi_nhds.mp hlim)

/-- Along a subsequence the partition points converge, preserving their order
and the lower width bound for every nonterminal interval. -/
theorem exists_subseq_partition_points_with_width (t : Time) (K : ℕ) (δ : ℝ)
    (cut : ℕ → Fin (K + 1) → Time) (hcut : ∀ n i, cut n i ≤ t)
    (horder : ∀ n (i : Fin K), cut n i.castSucc ≤ cut n i.succ)
    (hwidth : ∀ n (i : Fin K), i.val + 1 < K →
      δ ≤ (cut n i.succ : ℝ) - (cut n i.castSucc : ℝ)) :
    ∃ (φ : ℕ → ℕ) (limit : Fin (K + 1) → Time), StrictMono φ ∧
      (∀ i, limit i ≤ t) ∧
      (∀ i : Fin K, limit i.castSucc ≤ limit i.succ) ∧
      (∀ i : Fin K, i.val + 1 < K →
        δ ≤ (limit i.succ : ℝ) - (limit i.castSucc : ℝ)) ∧
      ∀ i, Tendsto (fun n => cut (φ n) i) atTop (𝓝 (limit i)) := by
  obtain ⟨φ, limit, hφ, hlimit, hlim⟩ := exists_subseq_partition_points t (K + 1) cut hcut
  refine ⟨φ, limit, hφ, hlimit, ?_, ?_, hlim⟩
  · intro i
    exact le_of_tendsto_of_tendsto' (hlim i.castSucc) (hlim i.succ)
      (fun n => horder (φ n) i)
  · intro i hi
    have hs := (NNReal.continuous_coe.tendsto (limit i.succ)).comp (hlim i.succ)
    have hp := (NNReal.continuous_coe.tendsto (limit i.castSucc)).comp (hlim i.castSucc)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hs.sub hp)
      (fun n => hwidth (φ n) i hi)

end LatticeProb.Cadlag.HalfLine

namespace LatticeProb.Cadlag.HalfLine

open Filter Set
open scoped Topology

/-- A bounded sequence of partition counts has a constant subsequence. -/
theorem exists_subseq_const_of_bounded (K : ℕ → ℕ) (N : ℕ) (hK : ∀ n, K n ≤ N) :
    ∃ (φ : ℕ → ℕ) (k : ℕ), StrictMono φ ∧ ∀ n, K (φ n) = k := by
  have hc : IsCompact (Iic N : Set ℕ) := (Set.finite_Iic N).isCompact
  obtain ⟨k, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => hK n)
  have hevent : ∀ᶠ n in atTop, K (φ n) = k := by
    have hsingle : ({k} : Set ℕ) ∈ 𝓝 k := by simp only [nhds_discrete, mem_pure, mem_singleton_iff]
    have hh : ∀ᶠ n in atTop, (K ∘ φ) n ∈ ({k} : Set ℕ) := hlim hsingle
    filter_upwards [hh] with n hn
    exact Set.mem_singleton_iff.mp hn
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨fun n => φ (n + M), k, ?_, fun n => hM (n + M) (by omega)⟩
  exact hφ.comp (fun _ _ h => by omega)

/-- Bounded partition counts and cut points admit a subsequence with fixed
count and convergent cut points, retaining all nonterminal width bounds. -/
theorem exists_subseq_fixed_count_partition_points (t : Time) (δ : ℝ)
    (K : ℕ → ℕ) (cut : ℕ → ℕ → Time) (N : ℕ) (hK : ∀ n, K n ≤ N)
    (hcut : ∀ n i, i ≤ K n → cut n i ≤ t)
    (horder : ∀ n i, i < K n → cut n i ≤ cut n (i + 1))
    (hwidth : ∀ n i, i + 1 < K n →
      δ ≤ (cut n (i + 1) : ℝ) - (cut n i : ℝ)) :
    ∃ (φ : ℕ → ℕ) (k : ℕ) (limit : Fin (k + 1) → Time),
      StrictMono φ ∧ (∀ n, K (φ n) = k) ∧
      (∀ i, limit i ≤ t) ∧
      (∀ i : Fin k, limit i.castSucc ≤ limit i.succ) ∧
      (∀ i : Fin k, i.val + 1 < k →
        δ ≤ (limit i.succ : ℝ) - (limit i.castSucc : ℝ)) ∧
      ∀ i, Tendsto (fun n => cut (φ n) i.val) atTop (𝓝 (limit i)) := by
  obtain ⟨ψ, k, hψ, hk⟩ := exists_subseq_const_of_bounded K N hK
  let c : ℕ → Fin (k + 1) → Time := fun n i => cut (ψ n) i.val
  have hc : ∀ n i, c n i ≤ t := by
    intro n i
    apply hcut
    rw [hk]
    omega
  have ho : ∀ n (i : Fin k), c n i.castSucc ≤ c n i.succ := by
    intro n i
    apply horder
    rw [hk]
    exact i.isLt
  have hw : ∀ n (i : Fin k), i.val + 1 < k →
      δ ≤ (c n i.succ : ℝ) - (c n i.castSucc : ℝ) := by
    intro n i hi
    apply hwidth
    rw [hk]
    exact hi
  obtain ⟨χ, limit, hχ, hlimit, hle, hδ, hlim⟩ :=
    exists_subseq_partition_points_with_width t k δ c hc ho hw
  exact ⟨ψ ∘ χ, k, limit, hψ.comp hχ, fun n => hk (χ n), hlimit, hle, hδ, hlim⟩

/-- In addition to fixed counts and convergent cut points, finitely many
partition values in a compact set can be selected to converge simultaneously. -/
theorem exists_subseq_partition_points_and_values {E : Type} [MetricSpace E]
    (S : Set E) (hS : IsCompact S) (t : Time) (δ : ℝ)
    (K : ℕ → ℕ) (cut : ℕ → ℕ → Time) (value : ℕ → ℕ → E)
    (N : ℕ) (hK : ∀ n, K n ≤ N)
    (hcut : ∀ n i, i ≤ K n → cut n i ≤ t)
    (horder : ∀ n i, i < K n → cut n i ≤ cut n (i + 1))
    (hwidth : ∀ n i, i + 1 < K n →
      δ ≤ (cut n (i + 1) : ℝ) - (cut n i : ℝ))
    (hvalue : ∀ n i, i ≤ K n → value n i ∈ S) :
    ∃ (φ : ℕ → ℕ) (k : ℕ) (limit : Fin (k + 1) → Time)
      (v : Fin (k + 1) → E),
      StrictMono φ ∧ (∀ n, K (φ n) = k) ∧
      (∀ i, limit i ≤ t) ∧ (∀ i, v i ∈ S) ∧
      (∀ i : Fin k, limit i.castSucc ≤ limit i.succ) ∧
      (∀ i : Fin k, i.val + 1 < k →
        δ ≤ (limit i.succ : ℝ) - (limit i.castSucc : ℝ)) ∧
      (∀ i, Tendsto (fun n => cut (φ n) i.val) atTop (𝓝 (limit i))) ∧
      ∀ i, Tendsto (fun n => value (φ n) i.val) atTop (𝓝 (v i)) := by
  obtain ⟨ψ, k, limit, hψ, hk, ht, ho, hw, hlim⟩ :=
    exists_subseq_fixed_count_partition_points t δ K cut N hK hcut horder hwidth
  let V : ℕ → Fin (k + 1) → E := fun n i => value (ψ n) i.val
  have hv : ∀ n, V n ∈ Set.pi univ (fun _ => S) := by
    intro n i _
    apply hvalue
    rw [hk]
    omega
  have hc : IsCompact (Set.pi univ (fun _ : Fin (k + 1) => S)) :=
    isCompact_univ_pi (fun _ => hS)
  obtain ⟨v, hvS, χ, hχ, hvlim⟩ := hc.tendsto_subseq hv
  refine ⟨ψ ∘ χ, k, limit, v, hψ.comp hχ, fun n => hk (χ n), ht,
    fun i => hvS i (mem_univ i), ho, hw, ?_, ?_⟩
  · intro i
    exact (hlim i).comp hχ.tendsto_atTop
  · exact tendsto_pi_nhds.mp hvlim

/-- Admissible oscillation partitions with compactly confined paths admit a
subsequence whose counts, cuts and values at the cuts converge together. -/
theorem exists_subseq_oscillation_partitions {E : Type} [MetricSpace E]
    (S : Set E) (hS : IsCompact S) (t : Time) {δ η : ℝ} (hδ : 0 < δ)
    (x : ℕ → D E) (hx : ∀ n, HasOscillationPartition (x n) t δ η)
    (hcompact : ∀ n s, s ≤ t → (x n).1 s ∈ S) :
    ∃ (φ : ℕ → ℕ) (k : ℕ) (cut : ℕ → ℕ → Time)
      (limit : Fin (k + 1) → Time) (v : Fin (k + 1) → E),
      StrictMono φ ∧ 0 < k ∧
      (∀ n, cut n 0 = 0 ∧ cut n k = t ∧
        (∀ i, i < k → cut n i < cut n (i + 1)) ∧
        (∀ i, i + 1 < k → δ ≤ (cut n (i + 1) : ℝ) - (cut n i : ℝ)) ∧
        ∀ i, i < k → ∀ s u : Time,
          cut n i ≤ s → s < cut n (i + 1) →
          cut n i ≤ u → u < cut n (i + 1) →
          dist ((x (φ n)).1 s) ((x (φ n)).1 u) ≤ η) ∧
      (∀ i, limit i ≤ t) ∧ (∀ i, v i ∈ S) ∧
      limit 0 = 0 ∧ limit (Fin.last k) = t ∧
      (∀ i : Fin k, limit i.castSucc ≤ limit i.succ) ∧
      (∀ i : Fin k, i.val + 1 < k →
        δ ≤ (limit i.succ : ℝ) - (limit i.castSucc : ℝ)) ∧
      (∀ i, Tendsto (fun n => cut n i.val) atTop (𝓝 (limit i))) ∧
      ∀ i, Tendsto (fun n => (x (φ n)).1 (cut n i.val)) atTop (𝓝 (v i)) := by
  classical
  choose K hK cut hzero hend hstrict hwidth hosc using hx
  obtain ⟨N, hN⟩ := exists_partition_interval_bound t hδ
  have hbound : ∀ n, K n ≤ N := fun n =>
    hN (K n) (cut n) (hK n) (hzero n) (hend n) (hstrict n) (hwidth n)
  have hcut : ∀ n i, i ≤ K n → cut n i ≤ t := by
    intro n i hi
    have hmono : ∀ j, i ≤ j → j ≤ K n → cut n i ≤ cut n j := by
      intro j hij
      induction j, hij using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ j hj ih =>
        intro hjK
        exact (ih (by omega)).trans (hstrict n j (by omega)).le
    simpa only [hend n] using hmono (K n) hi le_rfl
  have horder : ∀ n i, i < K n → cut n i ≤ cut n (i + 1) :=
    fun n i hi => (hstrict n i hi).le
  have hval : ∀ n i, i ≤ K n → (x n).1 (cut n i) ∈ S :=
    fun n i hi => hcompact n (cut n i) (hcut n i hi)
  obtain ⟨φ, k, limit, v, hφ, hcount, hlimit, hv, ho, hw, hlim, hvlim⟩ :=
    exists_subseq_partition_points_and_values S hS t δ K cut
      (fun n i => (x n).1 (cut n i)) N hbound hcut horder hwidth hval
  have hfirst : limit 0 = 0 := by
    apply tendsto_nhds_unique (hlim 0)
    simpa only [Fin.val_zero, hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : Time)) atTop (𝓝 0))
  have hlast : limit (Fin.last k) = t := by
    apply tendsto_nhds_unique (hlim (Fin.last k))
    have hc : ∀ n, cut (φ n) k = t := by
      intro n
      simpa only [hcount n] using hend (φ n)
    simpa only [Fin.val_last, hc] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => t) atTop (𝓝 t))
  refine ⟨φ, k, fun n => cut (φ n), limit, v, hφ, ?_, ?_, hlimit, hv,
    hfirst, hlast, ho, hw, hlim, hvlim⟩
  · simpa only [hcount 0] using hK (φ 0)
  · intro n
    simpa only [hcount n] using
      And.intro (hzero (φ n)) (And.intro (hend (φ n))
        (And.intro (hstrict (φ n)) (And.intro (hwidth (φ n)) (hosc (φ n)))))

end LatticeProb.Cadlag.HalfLine
