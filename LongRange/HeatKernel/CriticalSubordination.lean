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

/-- Convolution of densities with respect to the vertex masses. -/
noncomputable def densityComp (m : X → ℝ≥0) (a b : X → X → ℝ≥0∞)
    (x y : X) : ℝ≥0∞ := ∑' z, a x z * b z y * (m z : ℝ≥0∞)

/-- Weighted density convolution is associative. -/
theorem densityComp_assoc (m : X → ℝ≥0) (a b c : X → X → ℝ≥0∞)
    (x y : X) : densityComp m (densityComp m a b) c x y =
      densityComp m a (densityComp m b c) x y := by
  simp only [densityComp, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  calc
    _ = ∑' z, ∑' w, a x w * (b w z * c z y * (m z : ℝ≥0∞)) *
        (m w : ℝ≥0∞) := by
      apply tsum_congr; intro z
      apply tsum_congr; intro w
      ac_rfl
    _ = ∑' w, ∑' z, a x w * (b w z * c z y * (m z : ℝ≥0∞)) *
        (m w : ℝ≥0∞) := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr; intro w
      apply tsum_congr; intro z
      ac_rfl

/-- The identity density is a left unit when the masses are positive. -/
theorem densityComp_identity_left (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (k : X → X → ℝ≥0∞) (x y : X) : densityComp m (identityDensity m) k x y = k x y := by
  classical
  simp only [densityComp, identityDensity, ite_mul, zero_mul, tsum_ite_eq']
  have h : (m x : ℝ≥0∞)⁻¹ * (m x : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hm x) ENNReal.coe_ne_top
  calc
    (m x : ℝ≥0∞)⁻¹ * k x y * (m x : ℝ≥0∞) =
      ((m x : ℝ≥0∞)⁻¹ * (m x : ℝ≥0∞)) * k x y := by ac_rfl
    _ = k x y := by rw [h, one_mul]

/-- The identity density is a right unit when the masses are positive. -/
theorem densityComp_identity_right (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (k : X → X → ℝ≥0∞) (x y : X) : densityComp m k (identityDensity m) x y = k x y := by
  classical
  simp only [densityComp, identityDensity, mul_ite, mul_zero, ite_mul, zero_mul, tsum_ite_eq]
  rw [mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hm y) ENNReal.coe_ne_top, mul_one]

/-- Density powers form a semigroup under weighted convolution. -/
theorem densityPower_add (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (k : X → X → ℝ≥0∞) (a b : ℕ) (x y : X) :
    densityPower m k (a + b) x y = densityComp m (densityPower m k a) (densityPower m k b) x y := by
  induction a generalizing x y with
  | zero =>
    simpa [densityPower] using (densityComp_identity_left m hm (densityPower m k b) x y).symm
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    change densityComp m k (densityPower m k (a + b)) x y = _
    have heq : densityPower m k (a + b) =
        densityComp m (densityPower m k a) (densityPower m k b) := by
      funext x y; exact ih x y
    rw [heq, ← densityComp_assoc]
    rfl

/-- Density powers preserve symmetry. -/
theorem densityPower_symmetric (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (k : X → X → ℝ≥0∞) (hk : ∀ x y, k x y = k y x) (n : ℕ) (x y : X) :
    densityPower m k n x y = densityPower m k n y x := by
  classical
  induction n generalizing x y with
  | zero =>
    by_cases h : x = y
    · subst y; rfl
    · simp [densityPower, identityDensity, h, Ne.symm h]
  | succ n ih =>
    have hone : densityPower m k 1 = k := by
      funext x y
      exact densityComp_identity_right m hm k x y
    calc
      densityPower m k (n + 1) x y = densityComp m (densityPower m k n) k x y := by
        rw [densityPower_add m hm k, hone]
      _ = densityPower m k (n + 1) y x := by
        change (∑' z, densityPower m k n x z * k z y * (m z : ℝ≥0∞)) =
          ∑' z, k y z * densityPower m k n z x * (m z : ℝ≥0∞)
        apply tsum_congr; intro z
        rw [ih x z, hk z y, mul_comm (densityPower m k n z x) (k y z)]

/-- The quadratic-scale subordination of a density, as in equation (29). -/
noncomputable def criticalSubordinateDensity (m : X → ℝ≥0) (q : X → X → ℝ≥0∞)
    (x y : X) : ℝ≥0∞ :=
  ∑' n, criticalSubordinationWeight n * densityPower m q (2 * (n + 1) ^ 2) x y

/-- The quadratic-scale subordinate of a symmetric density is symmetric. -/
theorem criticalSubordinateDensity_symmetric (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (q : X → X → ℝ≥0∞) (hq : ∀ x y, q x y = q y x) (x y : X) :
    criticalSubordinateDensity m q x y = criticalSubordinateDensity m q y x := by
  exact symmetric_tsum_density criticalSubordinationWeight
    (fun n => densityPower m q (2 * (n + 1) ^ 2))
    (fun n => densityPower_symmetric m hm q hq _) x y

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

/-- Averaging a symmetric density with its two-step power preserves symmetry. -/
theorem averagedDensity_symmetric (m : X → ℝ≥0) (hm : ∀ x, m x ≠ 0)
    (p : X → X → ℝ≥0∞) (hp : ∀ x y, p x y = p y x) (x y : X) :
    averagedDensity m p x y = averagedDensity m p y x := by
  simp only [averagedDensity, hp x y, densityPower_symmetric m hm p hp 2 x y]

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
