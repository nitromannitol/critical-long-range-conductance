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
