import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Minimal scale from block events

The eventual good block index defines an extended nonnegative random variable.
Exponential bounds for the bad blocks give an exponential tail for this scale.
-/

namespace LongRange

open MeasureTheory

/-- The first block index after which every block event holds, scaled by `K`; `⊤` if none. -/
noncomputable def minimalScale {Ω : Type*} (G : ℕ → Set Ω) (K : ℝ) (ω : Ω) : ENNReal :=
  ⨅ (m₀ : ℕ) (_ : 1 ≤ m₀) (_ : ∀ m, m₀ ≤ m → ω ∈ G m),
    ENNReal.ofReal (K * m₀)

/-- Measurable block events give a measurable minimal scale. -/
theorem measurable_minimalScale {Ω : Type*} [MeasurableSpace Ω] {G : ℕ → Set Ω}
    (hG : ∀ m, MeasurableSet (G m)) (K : ℝ) : Measurable (minimalScale G K) := by
  classical
  apply Measurable.iInf
  intro m₀
  apply Measurable.iInf
  intro _
  have hset : MeasurableSet {ω | ∀ m, m₀ ≤ m → ω ∈ G m} := by
    simpa only [Set.setOf_forall, Set.setOf_mem_eq] using
      MeasurableSet.iInter fun m => MeasurableSet.iInter fun (_ : m₀ ≤ m) => hG m
  have heq : (fun ω => ⨅ (_ : ∀ m, m₀ ≤ m → ω ∈ G m),
      ENNReal.ofReal (K * m₀)) =
      (fun ω => if ∀ m, m₀ ≤ m → ω ∈ G m then ENNReal.ofReal (K * m₀) else ⊤) := by
    funext ω
    by_cases h : ∀ m, m₀ ≤ m → ω ∈ G m
    · rw [if_pos h]
      exact le_antisymm (iInf_le _ h) (le_iInf fun _ => le_rfl)
    · rw [if_neg h]
      exact top_unique (le_iInf fun hh => False.elim (h hh))
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

/-- An admissible block index bounds the minimal scale from above. -/
theorem minimalScale_le_of_good {Ω : Type*} {G : ℕ → Set Ω} {K : ℝ} {ω : Ω}
    {m : ℕ} (hm : 1 ≤ m) (hgood : ∀ n, m ≤ n → ω ∈ G n) :
    minimalScale G K ω ≤ ENNReal.ofReal (K * m) := by
  exact iInf_le_of_le m (iInf_le_of_le hm (iInf_le_of_le hgood le_rfl))

/-- Every block at or above a finite minimal scale is good. -/
theorem mem_of_minimalScale_le {Ω : Type*} {G : ℕ → Set Ω} {K : ℝ} (hK : 0 < K)
    {ω : Ω} {m : ℕ} (hm : 1 ≤ m)
    (h : minimalScale G K ω ≤ ENNReal.ofReal (K * m)) : ω ∈ G m := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  by_contra hbad
  have hlower : ENNReal.ofReal (K * (m + 1)) ≤ minimalScale G K ω := by
    refine le_iInf fun n => le_iInf fun _hn => le_iInf fun hgood => ?_
    have hmn : m + 1 ≤ n := by
      by_contra hnot
      exact hbad (hgood m (by omega))
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) hK.le)
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hK.le hmpos.le)).mp (hlower.trans h)
  have : (m : ℝ) + 1 ≤ m := (mul_le_mul_iff_right₀ hK).mp hreal
  linarith

/-- A union bound and a geometric series control failure after a fixed block index. -/
theorem measure_minimalScale_tail_block {Ω : Type*} [MeasurableSpace Ω]
    {G : ℕ → Set Ω} {P : Measure Ω} {C c K : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hP : ∀ m : ℕ, P (G m)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * m))))
    {N : ℕ} (hN : 1 ≤ N) :
    P {ω | ENNReal.ofReal (K * N) < minimalScale G K ω} ≤
      ENNReal.ofReal (C * Real.exp (-(c * N)) / (1 - Real.exp (-c))) := by
  have hsub : {ω | ENNReal.ofReal (K * N) < minimalScale G K ω} ⊆
      ⋃ j : ℕ, (G (N + j))ᶜ := by
    intro ω hω
    by_contra hnot
    have hgood : ∀ n, N ≤ n → ω ∈ G n := by
      intro n hn
      have : ω ∉ (G (N + (n - N)))ᶜ := by
        exact fun hmem => hnot (Set.mem_iUnion.mpr ⟨n - N, hmem⟩)
      simpa only [Nat.add_sub_of_le hn, Set.mem_compl_iff, not_not] using this
    exact (not_lt_of_ge (minimalScale_le_of_good hN hgood)) hω
  have hr : Real.exp (-c) < 1 := by simpa using Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  have heq (j : ℕ) : C * Real.exp (-(c * (N + j))) =
      (C * Real.exp (-(c * N))) * Real.exp (-c) ^ j := by
    have halg : -(c * ((N : ℝ) + j)) = -(c * N) + (j : ℝ) * (-c) := by ring
    rw [halg, Real.exp_add, Real.exp_nat_mul, mul_assoc]
  have hsum : Summable (fun j : ℕ => C * Real.exp (-(c * (N + j)))) := by
    simp_rw [heq]
    exact (summable_geometric_of_lt_one (Real.exp_nonneg _) hr).mul_left _
  calc
    _ ≤ P (⋃ j : ℕ, (G (N + j))ᶜ) := measure_mono hsub
    _ ≤ ∑' j : ℕ, P (G (N + j))ᶜ := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (C * Real.exp (-(c * (N + j)))) :=
      ENNReal.tsum_le_tsum fun j => by simpa only [Nat.cast_add] using hP (N + j)
    _ = ENNReal.ofReal (∑' j : ℕ, C * Real.exp (-(c * (N + j)))) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum).symm
    _ = _ := by
      simp_rw [heq]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _) hr, div_eq_mul_inv]

/-- Exponentially unlikely bad blocks give an exponential tail, with explicit constants. -/
theorem measure_minimalScale_tail {Ω : Type*} [MeasurableSpace Ω]
    {G : ℕ → Set Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {C c K : ℝ} (hC : 0 < C) (hc : 0 < c) (hK : 0 < K)
    (hP : ∀ m : ℕ, P (G m)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * m)))) :
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ s : ℝ, 1 ≤ s →
      P {ω | ENNReal.ofReal s < minimalScale G K ω} ≤
        ENNReal.ofReal (C' * Real.exp (-(c' * s))) := by
  have hden : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
    linarith
  let A : ℝ := C / (1 - Real.exp (-c))
  have hA : 0 < A := div_pos hC hden
  refine ⟨(A + 1) * Real.exp c, c / K, by positivity, div_pos hc hK, ?_⟩
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hexp : Real.exp c * Real.exp (-(c / K * s)) =
      Real.exp (c - c * (s / K)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_cases hlarge : K ≤ s
  · let N : ℕ := ⌊s / K⌋₊
    have hN : 1 ≤ N := Nat.le_floor ((le_div_iff₀ hK).mpr (by simpa using hlarge))
    have hNs : K * N ≤ s := by
      have hf := (le_div_iff₀ hK).mp (Nat.floor_le (div_nonneg hspos.le hK.le))
      simpa only [mul_comm] using hf
    have hsubset : {ω | ENNReal.ofReal s < minimalScale G K ω} ⊆
        {ω | ENNReal.ofReal (K * N) < minimalScale G K ω} := by
      intro ω hω
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hNs) hω
    have hfloor : s / K < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hexple : Real.exp (-(c * N)) ≤ Real.exp (c - c * (s / K)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_lt_mul_of_pos_left hfloor hc]
    calc
      _ ≤ P {ω | ENNReal.ofReal (K * N) < minimalScale G K ω} := measure_mono hsubset
      _ ≤ ENNReal.ofReal (C * Real.exp (-(c * N)) / (1 - Real.exp (-c))) :=
        measure_minimalScale_tail_block hC hc hP hN
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc, hexp]
        have halg : C * Real.exp (-(c * N)) / (1 - Real.exp (-c)) =
            A * Real.exp (-(c * N)) := by dsimp [A]; ring
        rw [halg]
        exact (mul_le_mul_of_nonneg_left hexple hA.le).trans
          (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
  · have hratio : s / K < 1 := (div_lt_one hK).mpr (lt_of_not_ge hlarge)
    have hexpone : 1 ≤ Real.exp (c - c * (s / K)) := by
      apply Real.one_le_exp
      nlinarith [mul_lt_mul_of_pos_left hratio hc]
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc, hexp]
        exact one_le_mul_of_one_le_of_one_le (by linarith) hexpone

end LongRange
