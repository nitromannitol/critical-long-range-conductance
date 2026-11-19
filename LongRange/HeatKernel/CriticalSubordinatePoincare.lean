import LongRange.HeatKernel.CriticalLatticePseudoPoincare
import LongRange.HeatKernel.CriticalEnergyReal

/-!
# Pseudo-Poincaré bounds for subordinated kernels

Finite sums of the quadratic-time estimates control the energy of a mixture.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- A weighted family of energy bounds passes to its summable mixture. -/
theorem weighted_energy_sum_lower (N : ℕ) (D B : ℝ) (w e a : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (he : ∀ n, 0 ≤ e n)
    (hs : Summable (fun n => w n * e n))
    (hB : 0 ≤ B) (hbound : ∀ n ∈ Finset.range N, D * a n ≤ B * e n) :
    D * (∑ n ∈ Finset.range N, w n * a n) ≤ B * ∑' n, w n * e n := by
  calc
    _ = ∑ n ∈ Finset.range N, w n * (D * a n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ∑ n ∈ Finset.range N, w n * (B * e n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (hbound n hn) (hw n)
    _ = B * ∑ n ∈ Finset.range N, w n * e n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ B * ∑' n, w n * e n := by
      exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun n _ => mul_nonneg (hw n) (he n))) hB

/-- Finite quadratic-time estimates bound the energy of the subordinated lattice walk. -/
theorem weightedLattice_subordinate_energy_lower {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ f : lp (fun _ : LatticeProb.Site d => ℝ) 2,
      Summable (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
      (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) *
          (∑ n ∈ Finset.range ⌊R⌋₊, (criticalSubordinationWeight n).toReal *
            ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        C * R ^ 2 * realKernelEnergy
          (criticalSubordinateDensity (weightedLattice d hd).mass
            (averagedDensity (weightedLattice d hd).mass
              (weightedLattice d hd).referenceDensity)) f := by
  obtain ⟨C, hC, hpoincare⟩ := weightedLattice_pseudoPoincare hd
  refine ⟨C, hC, ?_⟩
  intro R hR f
  let q := averagedDensity (weightedLattice d hd).mass (weightedLattice d hd).referenceDensity
  have hm : ∀ y, (weightedLattice d hd).mass y ≠ 0 := by
    intro y
    simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true]
  have hq : ∀ x, ∑' y, q x y = 1 := by
    intro x
    simpa only [q, weightedLattice_mass, ENNReal.coe_one, mul_one] using
      averagedDensity_isMarkov (weightedLattice d hd).mass hm _
        (weightedLattice_isMarkovDensity hd) x
  have hsym : ∀ x y, q x y = q y x :=
    averagedDensity_symmetric (weightedLattice d hd).mass hm _
      (weightedLattice d hd).referenceDensity_symmetric
  have hmass : (weightedLattice d hd).mass = fun _ => 1 := by
    funext x
    exact weightedLattice_mass hd x
  have hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞ := by
    have h : Summable (fun x => f x ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact h.tsum_ofReal_lt_top
  let e : ℕ → ℝ := fun n => realKernelEnergy (densityPower (fun _ => 1) q
    (2 * (n + 1) ^ 2)) f
  have hs := criticalSubordinateDensity_real_energy q hq hsym f hf
  change Summable (fun n => (criticalSubordinationWeight n).toReal * e n) ∧
    realKernelEnergy (criticalSubordinateDensity (fun _ => 1) q) f =
      ∑' n, (criticalSubordinationWeight n).toReal * e n at hs
  have he (n : ℕ) : 0 ≤ e n := by
    dsimp [e, realKernelEnergy]
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun x => tsum_nonneg (fun y =>
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
  have hbound (n : ℕ) (hn : n ∈ Finset.range ⌊R⌋₊) :
      (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) *
          ((n + 1 : ℕ) : ℝ) ^ 2 ≤ C * R ^ 2 * e n := by
    have hk : n + 1 ≤ ⌊R⌋₊ := by have := Finset.mem_range.mp hn; omega
    have hkR : ((n + 1 : ℕ) : ℝ) ≤ R := by
      exact (Nat.cast_le.mpr hk).trans (Nat.floor_le (by linarith))
    have hp := (hpoincare R hR (n + 1) (by omega) hkR f).2
    have heq : e n = realKernelEnergy (densityPower (weightedLattice d hd).mass q
        (2 * (n + 1) ^ 2)) f := by
      dsimp only [e]
      rw [hmass]
    change (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
      C * (R / ((n + 1 : ℕ) : ℝ)) ^ 2 *
        realKernelEnergy (densityPower (weightedLattice d hd).mass q (2 * (n + 1) ^ 2)) f at hp
    rw [← heq] at hp
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right hp hpos.le
    calc
      _ ≤ (C * (R / ((n + 1 : ℕ) : ℝ)) ^ 2 * e n) *
          ((n + 1 : ℕ) : ℝ) ^ 2 := h
      _ = C * R ^ 2 * e n := by
        rw [div_pow]
        field_simp
  have hsum := weighted_energy_sum_lower ⌊R⌋₊
    (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2)
    (C * R ^ 2) (fun n => (criticalSubordinationWeight n).toReal) e
    (fun n => ((n + 1 : ℕ) : ℝ) ^ 2) (fun _ => ENNReal.toReal_nonneg) he hs.1
    (by positivity) hbound
  rw [← hs.2, ← hmass] at hsum
  exact ⟨(hpoincare R hR 1 (by omega) (by simpa using hR) f).1, hsum⟩

end LatticeProb.Graph.LongRangeKernel
