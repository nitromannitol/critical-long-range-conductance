import LongRange.Support.Graph.LongRangeKernel.WeightedGraph
import LongRange.Support.Graph.LongRangeKernel.CriticalScale
import Mathlib.Analysis.PSeries

/-!
# Mixtures of Markov densities

Countable mixtures preserve Markov normalization and decompose the associated
nonnegative energy. These identities underlie the subordinated kernel in
Murugan and Saloff-Coste, Proposition 2.5.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

variable {X ι : Type*}

/-- A normalized mixture of Markov densities is a Markov density. -/
theorem isMarkovDensity_tsum (m : X → ℝ≥0) (w : ι → ℝ≥0∞)
    (k : ι → X → X → ℝ≥0∞) (hw : ∑' i, w i = 1)
    (hk : ∀ i, IsMarkovDensity m (k i)) :
    IsMarkovDensity m (fun x y => ∑' i, w i * k i x y) := by
  intro x
  calc
    (∑' y, (∑' i, w i * k i x y) * (m y : ℝ≥0∞)) =
        ∑' y, ∑' i, w i * (k i x y * (m y : ℝ≥0∞)) := by
      apply tsum_congr
      intro y
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro i
      rw [mul_assoc]
    _ = ∑' i, w i * ∑' y, k i x y * (m y : ℝ≥0∞) := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro i
      exact ENNReal.tsum_mul_left
    _ = 1 := by
      simp_rw [fun i => hk i x, mul_one]
      exact hw

/-- The counting-measure energy of a mixture is the corresponding mixture of energies. -/
theorem tsum_kernel_energy (w : ι → ℝ≥0∞) (k : ι → X → X → ℝ≥0∞)
    (f : X → ℝ) :
    (∑' x, ∑' y, (∑' i, w i * k i x y) *
      ENNReal.ofReal ((f x - f y) ^ 2)) =
      ∑' i, w i * ∑' x, ∑' y, k i x y *
        ENNReal.ofReal ((f x - f y) ^ 2) := by
  calc
    _ = ∑' x, ∑' y, ∑' i, w i * (k i x y *
        ENNReal.ofReal ((f x - f y) ^ 2)) := by
      apply tsum_congr
      intro x
      apply tsum_congr
      intro y
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro i
      rw [mul_assoc]
    _ = ∑' i, ∑' x, ∑' y, w i * (k i x y *
        ENNReal.ofReal ((f x - f y) ^ 2)) := by
      simp_rw [ENNReal.tsum_comm (f := fun y i => w i * (k i _ y *
        ENNReal.ofReal ((f _ - f y) ^ 2)))]
      rw [ENNReal.tsum_comm]
    _ = _ := by
      apply tsum_congr
      intro i
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      rw [← ENNReal.tsum_mul_left]

/-- The coefficients in the quadratic-scale subordination, indexed from one. -/
noncomputable def criticalSubordinationCoefficient (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℝ) * quadraticScale (n + 1))

/-- The quadratic-scale coefficients are summable. -/
theorem summable_criticalSubordinationCoefficient :
    Summable criticalSubordinationCoefficient := by
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ 2)) := by
    have h : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 h
  apply hs.of_nonneg_of_le
  · intro n
    unfold criticalSubordinationCoefficient quadraticScale
    positivity
  · intro n
    unfold criticalSubordinationCoefficient quadraticScale
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n + 1) ^ 2)
    calc
      ((n : ℝ) + 1) ^ 2 ≤ (1 + ((n : ℝ) + 1)) ^ 2 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [sq_nonneg (n : ℝ)]
      _ ≤ ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)) ^ 2 := by
        nlinarith [sq_nonneg (1 + ((n : ℝ) + 1))]

/-- The normalizing series is strictly positive. -/
theorem criticalSubordinationCoefficient_tsum_pos :
    0 < ∑' n, criticalSubordinationCoefficient n := by
  refine summable_criticalSubordinationCoefficient.tsum_pos ?_ 0 ?_
  · intro n
    unfold criticalSubordinationCoefficient quadraticScale
    positivity
  · norm_num [criticalSubordinationCoefficient, quadraticScale]

/-- The normalized coefficients of the quadratic-scale subordinated kernel. -/
noncomputable def criticalSubordinationWeight (n : ℕ) : ℝ≥0∞ :=
  (∑' j, ENNReal.ofReal (criticalSubordinationCoefficient j))⁻¹ *
    ENNReal.ofReal (criticalSubordinationCoefficient n)

/-- The normalized coefficients have total mass one. -/
theorem tsum_criticalSubordinationWeight :
    (∑' n, criticalSubordinationWeight n) = 1 := by
  have hfin : (∑' n, ENNReal.ofReal (criticalSubordinationCoefficient n)) ≠ ⊤ :=
    ne_of_lt summable_criticalSubordinationCoefficient.tsum_ofReal_lt_top
  have hpos : (0 : ℝ≥0∞) < ∑' n, ENNReal.ofReal (criticalSubordinationCoefficient n) := by
    have h := ENNReal.le_tsum (f := fun n =>
      ENNReal.ofReal (criticalSubordinationCoefficient n)) 0
    have h0 : (0 : ℝ≥0∞) < ENNReal.ofReal (criticalSubordinationCoefficient 0) := by
      simp [criticalSubordinationCoefficient, quadraticScale]
    exact lt_of_lt_of_le h0 h
  simp only [criticalSubordinationWeight, ENNReal.tsum_mul_left]
  exact ENNReal.inv_mul_cancel (ne_of_gt hpos) hfin

/-- Mixtures preserve symmetry of the component densities. -/
theorem symmetric_tsum_density (w : ι → ℝ≥0∞) (k : ι → X → X → ℝ≥0∞)
    (hk : ∀ i x y, k i x y = k i y x) (x y : X) :
    (∑' i, w i * k i x y) = ∑' i, w i * k i y x := by
  apply tsum_congr
  intro i
  rw [hk]

/-- The quadratic-scale subordination of a density, as in equation (29). -/
noncomputable def criticalSubordinateDensity (m : X → ℝ≥0) (q : X → X → ℝ≥0∞)
    (x y : X) : ℝ≥0∞ :=
  ∑' n, criticalSubordinationWeight n * densityPower m q (2 * (n + 1) ^ 2) x y

/-- The quadratic-scale subordinated density is Markov. -/
theorem criticalSubordinateDensity_isMarkov (m : X → ℝ≥0)
    (hm : ∀ x, m x ≠ 0) (q : X → X → ℝ≥0∞) (hq : IsMarkovDensity m q) :
    IsMarkovDensity m (criticalSubordinateDensity m q) := by
  exact isMarkovDensity_tsum m criticalSubordinationWeight
    (fun n => densityPower m q (2 * (n + 1) ^ 2))
    tsum_criticalSubordinationWeight (fun n => densityPower_isMarkov m hm q hq _)

/-- The counting-measure energy of the subordinated density is the mixture of its power energies. -/
theorem criticalSubordinateDensity_energy (m : X → ℝ≥0) (q : X → X → ℝ≥0∞)
    (f : X → ℝ) :
    (∑' x, ∑' y, criticalSubordinateDensity m q x y *
      ENNReal.ofReal ((f x - f y) ^ 2)) =
      ∑' n, criticalSubordinationWeight n * ∑' x, ∑' y,
        densityPower m q (2 * (n + 1) ^ 2) x y *
          ENNReal.ofReal ((f x - f y) ^ 2) := by
  exact tsum_kernel_energy criticalSubordinationWeight
    (fun n => densityPower m q (2 * (n + 1) ^ 2)) f

/-- The average of a density and its two-step power, as in equation (21). -/
noncomputable def averagedDensity (m : X → ℝ≥0) (p : X → X → ℝ≥0∞)
    (x y : X) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * (p x y + densityPower m p 2 x y)

/-- Averaging a Markov density with its two-step power preserves normalization. -/
theorem averagedDensity_isMarkov (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (p : X → X → ℝ≥0∞) (hp : IsMarkovDensity m p) :
    IsMarkovDensity m (averagedDensity m p) := by
  intro x
  have hp2 := densityPower_isMarkov m hm p hp 2 x
  calc
    (∑' y, averagedDensity m p x y * (m y : ℝ≥0∞)) =
        (2 : ℝ≥0∞)⁻¹ * ((∑' y, p x y * (m y : ℝ≥0∞)) +
          ∑' y, densityPower m p 2 x y * (m y : ℝ≥0∞)) := by
      simp_rw [averagedDensity, mul_assoc, add_mul, ENNReal.tsum_mul_left,
        ENNReal.tsum_add]
    _ = 1 := by
      rw [hp x, hp2, show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

end LatticeProb.Graph.LongRangeKernel
