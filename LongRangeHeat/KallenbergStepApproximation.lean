import LongRangeHeat.KallenbergStoppedPartitions

/-!
# Approximation by aligned step paths

Pointwise approximation on a finite horizon controls the stopped discrepancy
outside the windows between aligned cuts.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set MeasureTheory
open scoped ENNReal NNReal

/-- On a finite horizon, two paths close to aligned step paths with common
values have small stopped discrepancy outside the cut windows. -/
theorem discrepancy_le_of_step_approximations {E : Type*} [MetricSpace E]
    (x y : D E) (N : ℕ) (s : Fin N → Time) (v : Fin (N + 1) → E)
    (l : LambdaPrime) (T u : Time) (ε η : ℝ) (huT : u ≤ T)
    (hx : ∀ t ≤ T, dist (x.1 t) (v (stepIndex s t)) ≤ ε)
    (hy : ∀ t ≤ T, dist (y.1 t) (v (stepIndex (fun i => l (s i)) t)) ≤ η)
    (hu : (u : ℝ) ∉ ⋃ c ∈ Finset.univ.image s,
      Ico (min (c : ℝ) (l c : ℝ)) (max (c : ℝ) (l c : ℝ))) :
    discrepancy x y l u ≤ ENNReal.ofReal (ε + η) := by
  apply iSup_le
  intro t
  have hside (i : Fin N) : u < s i ↔ u < l (s i) :=
    lt_cut_iff_lt_image_of_not_mem_windows (Finset.univ.image s) l u (s i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hu
  have hi := stepIndex_stopped_timeChange N s l t u hside
  have hdist : dist (x.1 (min t u)) (y.1 (min (l t) u)) ≤ ε + η := by
    calc
      _ ≤ dist (x.1 (min t u)) (v (stepIndex s (min t u))) +
          dist (v (stepIndex s (min t u))) (y.1 (min (l t) u)) := dist_triangle _ _ _
      _ ≤ ε + η := by
        apply add_le_add (hx _ ((min_le_right _ _).trans huT))
        rw [hi, dist_comm]
        exact hy _ ((min_le_right _ _).trans huT)
  exact (min_le_left _ _).trans (by simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hdist)

/-- Finite-horizon approximation by aligned step paths bounds integrated
stopped discrepancy by the approximation errors, cut windows and tail. -/
theorem integratedDiscrepancy_le_of_step_approximations {E : Type*} [MetricSpace E]
    (x y : D E) (N : ℕ) (s : Fin N → Time) (v : Fin (N + 1) → E)
    (l : LambdaPrime) (T : Time) (B : ℝ≥0) (ε η : ℝ)
    (hmove : ∀ i, dist (s i) (l (s i)) ≤ B)
    (hx : ∀ t ≤ T, dist (x.1 t) (v (stepIndex s t)) ≤ ε)
    (hy : ∀ t ≤ T, dist (y.1 t) (v (stepIndex (fun i => l (s i)) t)) ≤ η) :
    integratedDiscrepancy x y l ≤ ENNReal.ofReal (ε + η) +
      (Finset.univ.image s).card * ENNReal.ofReal B +
        ENNReal.ofReal (Real.exp (-(T : ℝ))) := by
  apply integratedDiscrepancy_le_of_cut_windows x y l T (Finset.univ.image s) B (ε + η)
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact hmove i
  · intro u hu huT hout
    apply discrepancy_le_of_step_approximations x y N s v l T u.toNNReal ε η
    · exact_mod_cast (show (u.toNNReal : ℝ) ≤ (T : ℝ) by
        simpa only [Real.coe_toNNReal _ hu.le] using huT)
    · exact hx
    · exact hy
    · simpa only [Real.coe_toNNReal _ hu.le] using hout

/-- The same approximation estimates bound the half-line Skorokhod distance
using the distortion of the chosen time change. -/
theorem skorohodDistanceExtended_le_of_step_approximations {E : Type*} [MetricSpace E]
    (x y : D E) (N : ℕ) (s : Fin N → Time) (v : Fin (N + 1) → E)
    (l : Lambda) (T : Time) (B : ℝ≥0) (ε η : ℝ)
    (hmove : ∀ i, dist (s i) (l.1 (s i)) ≤ B)
    (hx : ∀ t ≤ T, dist (x.1 t) (v (stepIndex s t)) ≤ ε)
    (hy : ∀ t ≤ T, dist (y.1 t) (v (stepIndex (fun i => l.1 (s i)) t)) ≤ η) :
    skorohodDistanceExtended x y ≤ max (gamma l.1) (ENNReal.ofReal (ε + η) +
      (Finset.univ.image s).card * ENNReal.ofReal B +
        ENNReal.ofReal (Real.exp (-(T : ℝ)))) := by
  exact (iInf_le (fun k : Lambda => max (gamma k.1) (integratedDiscrepancy x y k.1)) l).trans
    (max_le_max le_rfl (integratedDiscrepancy_le_of_step_approximations
      x y N s v l.1 T B ε η hmove hx hy))

/-- Before the terminal cut, the step index selects the unique half-open
interval containing the time. -/
theorem stepIndex_mem_partition (N : ℕ) (cut : Fin (N + 1) → Time)
    (hmono : Monotone cut) (hzero : cut 0 = 0) (t : Time)
    (ht : t < cut (Fin.last N)) :
    ∃ i : Fin N, stepIndex (fun j : Fin N => cut j.succ) t = i.castSucc ∧
      cut i.castSucc ≤ t ∧ t < cut i.succ := by
  cases N with
  | zero => simp [hzero] at ht
  | succ N =>
    let s : Fin (N + 1) → Time := fun j => cut j.succ
    have hs : Monotone s := fun i j hij => hmono (Fin.succ_le_succ_iff.mpr hij)
    let k := stepIndex s t
    have hk : k.val < N + 1 := by
      have hlast := (stepIndex_le_iff s hs t (Fin.last N)).2 (by simpa [s] using ht)
      dsimp [k] at hlast
      simpa only [Fin.val_last] using Nat.lt_succ_of_le hlast
    let i : Fin (N + 1) := ⟨k.val, hk⟩
    have hki : k = i.castSucc := by apply Fin.ext; rfl
    refine ⟨i, hki, ?_, ?_⟩
    · by_cases hi : i.val = 0
      · have : i.castSucc = 0 := by apply Fin.ext; simpa using hi
        rw [this, hzero]
        exact zero_le
      · let j : Fin (N + 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hj : ¬ k.val ≤ j.val := by
          dsimp [i] at hi
          dsimp [i, j]
          omega
        have hn : ¬ t < s j := by
          intro h
          exact hj ((stepIndex_le_iff s hs t j).2 h)
        have heq : j.succ = i.castSucc := by apply Fin.ext; dsimp [j]; omega
        simpa only [s, heq] using le_of_not_gt hn
    · have hk' : k.val ≤ i.val := by dsimp [i]; exact le_rfl
      exact (stepIndex_le_iff s hs t i).1 hk'

/-- An oscillation bound on each half-open interval bounds approximation by
the step path taking the values at the left endpoints. -/
theorem dist_stepPath_le_of_oscillation {E : Type*} [MetricSpace E]
    (x : D E) (N : ℕ) (cut : Fin (N + 1) → Time)
    (hmono : Monotone cut) (hzero : cut 0 = 0) (T : Time)
    (hT : T < cut (Fin.last N)) (ε : ℝ)
    (hosc : ∀ i : Fin N, ∀ a : Time,
      a ≤ T → cut i.castSucc ≤ a → a < cut i.succ →
      dist (x.1 a) (x.1 (cut i.castSucc)) ≤ ε) :
    ∀ t ≤ T, dist (x.1 t)
      ((stepPath (fun j : Fin N => cut j.succ) (fun i => x.1 (cut i))).1 t) ≤ ε := by
  intro t ht
  obtain ⟨i, hi, hlo, hhi⟩ := stepIndex_mem_partition N cut hmono hzero t (ht.trans_lt hT)
  change dist (x.1 t) (x.1 (cut (stepIndex (fun j : Fin N => cut j.succ) t))) ≤ ε
  rw [hi]
  exact hosc i t ht hlo hhi

/-- Approximating the values at the cuts adds their maximal error to the
oscillation error of the step approximation. -/
theorem dist_stepPath_le_of_oscillation_and_cut_values {E : Type*} [MetricSpace E]
    (x : D E) (N : ℕ) (cut : Fin (N + 1) → Time) (v : Fin (N + 1) → E)
    (hmono : Monotone cut) (hzero : cut 0 = 0) (T : Time)
    (hT : T < cut (Fin.last N)) (ε η : ℝ)
    (hosc : ∀ i : Fin N, ∀ a : Time,
      a ≤ T → cut i.castSucc ≤ a → a < cut i.succ →
      dist (x.1 a) (x.1 (cut i.castSucc)) ≤ ε)
    (hv : ∀ i, dist (x.1 (cut i)) (v i) ≤ η) :
    ∀ t ≤ T, dist (x.1 t)
      ((stepPath (fun j : Fin N => cut j.succ) v).1 t) ≤ ε + η := by
  intro t ht
  calc
    _ ≤ dist (x.1 t) (x.1 (cut (stepIndex (fun j : Fin N => cut j.succ) t))) +
        dist (x.1 (cut (stepIndex (fun j : Fin N => cut j.succ) t)))
          (v (stepIndex (fun j : Fin N => cut j.succ) t)) := dist_triangle _ _ _
    _ ≤ ε + η := add_le_add
      (dist_stepPath_le_of_oscillation x N cut hmono hzero T hT ε hosc t ht) (hv _)

/-- Oscillation bounds transfer to a partition with the same nonterminal
cuts on horizons shorter than the original terminal cut. -/
theorem oscillation_le_of_nonterminal_cuts {E : Type*} [MetricSpace E]
    (x : D E) (N : ℕ) (cut r : Fin (N + 1) → Time) (T : Time) (ε : ℝ)
    (hleft : ∀ i : Fin N, r i.castSucc = cut i.castSucc)
    (hright : ∀ i : Fin N, i.val + 1 < N → r i.succ = cut i.succ)
    (hT : T < cut (Fin.last N))
    (hstrict : ∀ i : Fin N, cut i.castSucc < cut i.succ)
    (hosc : ∀ i : Fin N, ∀ a b : Time,
      cut i.castSucc ≤ a → a < cut i.succ →
      cut i.castSucc ≤ b → b < cut i.succ → dist (x.1 a) (x.1 b) ≤ ε) :
    ∀ i : Fin N, ∀ a : Time, a ≤ T → r i.castSucc ≤ a → a < r i.succ →
      dist (x.1 a) (x.1 (r i.castSucc)) ≤ ε := by
  intro i a haT ha hnext
  have halo : cut i.castSucc ≤ a := by simpa only [hleft i] using ha
  have hahi : a < cut i.succ := by
    by_cases hi : i.val + 1 < N
    · simpa only [hright i hi] using hnext
    · have heq : i.succ = Fin.last N := by apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; have := i.isLt; omega
      rw [heq]
      exact haT.trans_lt hT
  simpa only [hleft i] using hosc i a (cut i.castSucc) halo hahi le_rfl (hstrict i)

end LatticeProb.Cadlag.HalfLine
