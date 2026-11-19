import LongRange.HeatKernel.CriticalSubordination
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic mass of the quadratic subordination

The weighted quadratic-time coefficients contain a harmonic sum.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The quadratic moment of each subordination weight dominates a reciprocal. -/
theorem criticalSubordinationWeight_quadratic_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c / ((n + 1 : ℕ) : ℝ) ≤
        (criticalSubordinationWeight n).toReal * ((n + 1 : ℕ) : ℝ) ^ 2 := by
  let S : ℝ≥0∞ := ∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j)
  have hSfin : S ≠ ∞ := summable_criticalSubordinationCoefficient.tsum_ofReal_lt_top.ne
  have hSpos : 0 < S := by
    have h := ENNReal.le_tsum (f := fun n => ENNReal.ofReal (criticalSubordinationCoefficient n)) 0
    have h0 : (0 : ℝ≥0∞) < ENNReal.ofReal (criticalSubordinationCoefficient 0) := by
      simp [criticalSubordinationCoefficient, quadraticScale]
    exact lt_of_lt_of_le h0 h
  have ha : 0 < (S⁻¹).toReal := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr hSfin) (ENNReal.inv_ne_top.mpr hSpos.ne')
  refine ⟨(S⁻¹).toReal / 4, by positivity, ?_⟩
  intro n
  let k : ℝ := (n + 1 : ℕ)
  have hk : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hcoef : criticalSubordinationCoefficient n = 1 / (k * (1 + k) ^ 2) := by
    simp only [criticalSubordinationCoefficient, quadraticScale, k, Nat.cast_add, Nat.cast_one]
  have hc : 0 ≤ criticalSubordinationCoefficient n := by rw [hcoef]; positivity
  have hweight : (criticalSubordinationWeight n).toReal =
      (S⁻¹).toReal * criticalSubordinationCoefficient n := by
    simp only [criticalSubordinationWeight, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, S]
  rw [hweight, hcoef]
  change (S⁻¹).toReal / 4 / k ≤ (S⁻¹).toReal * (1 / (k * (1 + k) ^ 2)) * k ^ 2
  have hbase : 1 / (4 * k) ≤ (1 / (k * (1 + k) ^ 2)) * k ^ 2 := by
    have hpow : (1 + k) ^ 2 ≤ 4 * k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
    have hprod := mul_le_mul_of_nonneg_left hpow (show 0 ≤ k by linarith)
    have hdiv : 1 / (4 * k) ≤ k ^ 2 / (k * (1 + k) ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith
    convert hdiv using 1
    ring
  have h := mul_le_mul_of_nonneg_left hbase ha.le
  convert h using 1 <;> ring

/-- The quadratic moment accumulated up to a real radius grows at least logarithmically. -/
theorem criticalSubordinationWeight_log_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, 1 ≤ R →
      c * Real.log (1 + R) ≤
        ∑ n ∈ Finset.range ⌊R⌋₊, (criticalSubordinationWeight n).toReal *
          ((n + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨a, ha, hlower⟩ := criticalSubordinationWeight_quadratic_lower
  refine ⟨a / 2, by positivity, ?_⟩
  intro R hR
  let m := ⌊R⌋₊
  have hm : 1 ≤ m := by
    dsimp [m]
    exact (Nat.le_floor_iff (by linarith : 0 ≤ R)).mpr (by simpa using hR)
  have hmR : R < (m : ℝ) + 1 := Nat.lt_floor_add_one R
  have hmR' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : Real.log (1 + R) ≤ 2 * Real.log ((m : ℝ) + 1) := by
    have harg : 1 + R ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
    calc
      _ ≤ Real.log (((m : ℝ) + 1) ^ 2) := Real.log_le_log (by linarith) harg
      _ = _ := by rw [Real.log_pow]; norm_num
  have hh := log_add_one_le_harmonic m
  have hsum : (harmonic m : ℝ) =
      ∑ n ∈ Finset.range m, (((n + 1 : ℕ) : ℝ))⁻¹ := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hweighted : a * (harmonic m : ℝ) ≤
      ∑ n ∈ Finset.range m, (criticalSubordinationWeight n).toReal *
        ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [div_eq_mul_inv] using hlower n
  have hh' : Real.log ((m : ℝ) + 1) ≤ (harmonic m : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have h := mul_le_mul_of_nonneg_left hh' ha.le
  nlinarith

end LatticeProb.Graph.LongRangeKernel
