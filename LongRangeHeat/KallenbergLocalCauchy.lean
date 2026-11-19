import LongRangeHeat.KallenbergUniformConvergence

/-!
# Locally uniform Cauchy sequences

Locally uniform Cauchy sequences into a complete metric space converge
locally uniformly. For càdlàg paths, the limit is càdlàg and convergence
holds in the half-line Skorokhod metric.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter
open scoped Topology

/-- Summable uniform bounds on successive differences imply uniform Cauchyness. -/
theorem uniformCauchySeqOn_of_summable_dist {α E : Type*} [PseudoMetricSpace E]
    {s : Set α} {f : ℕ → α → E} {a : ℕ → ℝ} (ha : Summable a)
    (h : ∀ n t, t ∈ s → dist (f n t) (f (n + 1) t) ≤ a n) :
    UniformCauchySeqOn f atTop s := by
  have hc : CauchySeq (fun n => ∑ k ∈ Finset.range n, a k) :=
    ha.hasSum.tendsto_sum_nat.cauchySeq
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  have bound : ∀ i j, N ≤ i → N ≤ j → i ≤ j → dist (f i t) (f j t) < ε := by
    intro i j hi hj hij
    calc
      dist (f i t) (f j t) ≤ ∑ k ∈ Finset.Ico i j, a k :=
        dist_le_Ico_sum_of_dist_le (f := fun k => f k t) (d := a) hij
          (fun {k} _ _ => h k t ht)
      _ = (∑ k ∈ Finset.range j, a k) - ∑ k ∈ Finset.range i, a k :=
        Finset.sum_Ico_eq_sub _ hij
      _ ≤ |(∑ k ∈ Finset.range j, a k) - ∑ k ∈ Finset.range i, a k| := le_abs_self _
      _ = dist (∑ k ∈ Finset.range j, a k) (∑ k ∈ Finset.range i, a k) :=
        (Real.dist_eq _ _).symm
      _ < ε := hN j hj i hi
  rcases le_total m n with hmn | hnm
  · exact bound m n hm hn hmn
  · rw [dist_comm]
    exact bound n m hn hm hnm

/-- A locally uniformly Cauchy sequence has a locally uniform limit. -/
theorem exists_tendstoUniformlyOn_of_uniformCauchySeqOn
    {E : Type*} [MetricSpace E] [CompleteSpace E] {f : ℕ → Time → E}
    (h : ∀ T : Time, UniformCauchySeqOn f atTop (Iic T)) :
    ∃ g : Time → E, ∀ T : Time, TendstoUniformlyOn f g atTop (Iic T) := by
  have hp : ∀ t, ∃ y, Tendsto (fun n => f n t) atTop (𝓝 y) := by
    intro t
    exact cauchySeq_tendsto_of_complete ((h t).cauchySeq (mem_Iic.mpr le_rfl))
  choose g hg using hp
  exact ⟨g, fun T => (h T).tendstoUniformlyOn_of_tendsto (fun t _ => hg t)⟩

/-- A locally uniformly Cauchy sequence of càdlàg paths converges in the
half-line path metric. -/
theorem exists_tendsto_of_uniformCauchySeqOn_paths
    {E : Type*} [MetricSpace E] [CompleteSpace E] {x : ℕ → D E}
    (h : ∀ T : Time, UniformCauchySeqOn (fun n => (x n).1) atTop (Iic T)) :
    ∃ z : D E, (∀ T : Time, TendstoUniformlyOn (fun n => (x n).1) z.1 atTop (Iic T)) ∧
      Tendsto x atTop (𝓝 z) := by
  obtain ⟨g, hg⟩ := exists_tendstoUniformlyOn_of_uniformCauchySeqOn h
  obtain ⟨z, hz, hlim⟩ := exists_tendsto_of_tendstoUniformlyOn_paths hg
  exact ⟨z, hz ▸ hg, hlim⟩

/-- Summable bounds on successive path differences on each initial interval
provide a càdlàg limit in the half-line path metric. -/
theorem exists_tendsto_of_summable_dist_paths
    {E : Type*} [MetricSpace E] [CompleteSpace E] {x : ℕ → D E}
    (h : ∀ T : Time, ∃ a : ℕ → ℝ, Summable a ∧
      ∀ n t, t ∈ Iic T → dist ((x n).1 t) ((x (n + 1)).1 t) ≤ a n) :
    ∃ z : D E, (∀ T : Time, TendstoUniformlyOn (fun n => (x n).1) z.1 atTop (Iic T)) ∧
      Tendsto x atTop (𝓝 z) := by
  apply exists_tendsto_of_uniformCauchySeqOn_paths
  intro T
  obtain ⟨a, ha, hbound⟩ := h T
  exact uniformCauchySeqOn_of_summable_dist ha hbound

end LatticeProb.Cadlag.HalfLine
