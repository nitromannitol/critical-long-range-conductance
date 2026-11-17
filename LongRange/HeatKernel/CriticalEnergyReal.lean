import LongRange.HeatKernel.CriticalEnergyBound

/-!
# Real energy of a symmetric Markov kernel

Finite nonnegative energy agrees with the real double sum in the Dirichlet
form of a symmetric Markov kernel on counting measure.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The real Dirichlet energy associated with a kernel. -/
noncomputable def realKernelEnergy {X : Type*} (k : X → X → ℝ≥0∞) (f : X → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' x, ∑' y, (k x y).toReal * (f x - f y) ^ 2

/-- Square-summability gives summability of every real energy row. -/
theorem summable_real_kernel_energy_row {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) (x : X) :
    Summable (fun y => (k x y).toReal * (f x - f y) ^ 2) := by
  have h := symmetric_markov_energy_lt_top k hk hsym f hf
  have hx : (∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) ≠ ∞ :=
    ENNReal.ne_top_of_tsum_ne_top h.ne x
  have hs := ENNReal.summable_toReal hx
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] using hs

/-- Finite nonnegative energy converts to the real Dirichlet double sum. -/
theorem realKernelEnergy_eq_toReal_of_lt_top {X : Type*} (k : X → X → ℝ≥0∞)
    (f : X → ℝ)
    (h : (∑' x, ∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) < ∞) :
    realKernelEnergy k f = (1 / 2 : ℝ) *
      (∑' x, ∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)).toReal := by
  have hx (x : X) : (∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) ≠ ∞ :=
    ENNReal.ne_top_of_tsum_ne_top h.ne x
  unfold realKernelEnergy
  rw [ENNReal.tsum_toReal_eq hx]
  congr 1
  apply tsum_congr
  intro x
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top (hx x))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Square-summability gives the real form of the finite-energy identity. -/
theorem realKernelEnergy_eq_toReal {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    realKernelEnergy k f = (1 / 2 : ℝ) *
      (∑' x, ∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)).toReal :=
  realKernelEnergy_eq_toReal_of_lt_top k f (symmetric_markov_energy_lt_top k hk hsym f hf)

/-- The real energy rows are summable for a square-summable function. -/
theorem summable_real_kernel_energy {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    Summable (fun x => ∑' y, (k x y).toReal * (f x - f y) ^ 2) := by
  have h := symmetric_markov_energy_lt_top k hk hsym f hf
  have hx (x : X) : (∑' y, k x y * ENNReal.ofReal ((f x - f y) ^ 2)) ≠ ∞ :=
    ENNReal.ne_top_of_tsum_ne_top h.ne x
  have hs := ENNReal.summable_toReal h.ne
  apply hs.congr
  intro x
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top (hx x))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Finite kernel energies commute with a nonnegative mixture. -/
theorem realKernelEnergy_tsum {X ι : Type*} (w : ι → ℝ≥0∞)
    (k : ι → X → X → ℝ≥0∞) (f : X → ℝ)
    (hk : ∀ i, (∑' x, ∑' y, k i x y * ENNReal.ofReal ((f x - f y) ^ 2)) < ∞)
    (hmix : (∑' x, ∑' y, (∑' i, w i * k i x y) *
      ENNReal.ofReal ((f x - f y) ^ 2)) < ∞) :
    Summable (fun i => (w i).toReal * realKernelEnergy (k i) f) ∧
      realKernelEnergy (fun x y => ∑' i, w i * k i x y) f =
        ∑' i, (w i).toReal * realKernelEnergy (k i) f := by
  have heq := tsum_kernel_energy w k f
  have hsum : (∑' i, w i * ∑' x, ∑' y, k i x y *
      ENNReal.ofReal ((f x - f y) ^ 2)) ≠ ∞ := by rw [← heq]; exact hmix.ne
  have hs := ENNReal.summable_toReal hsum
  have hterm (i : ι) : (w i * ∑' x, ∑' y, k i x y *
      ENNReal.ofReal ((f x - f y) ^ 2)).toReal =
      (w i).toReal * (∑' x, ∑' y, k i x y *
        ENNReal.ofReal ((f x - f y) ^ 2)).toReal := ENNReal.toReal_mul
  have hs' : Summable (fun i => (w i).toReal *
      (∑' x, ∑' y, k i x y * ENNReal.ofReal ((f x - f y) ^ 2)).toReal) := by
    simpa only [hterm] using hs
  constructor
  · convert hs'.mul_left (1 / 2 : ℝ) using 1
    ext i
    rw [realKernelEnergy_eq_toReal_of_lt_top (k i) f (hk i)]
    ring
  · rw [realKernelEnergy_eq_toReal_of_lt_top _ f hmix, heq,
      ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hsum)]
    simp_rw [hterm, realKernelEnergy_eq_toReal_of_lt_top _ f (hk _)]
    rw [← tsum_mul_left]
    congr 1
    funext i
    ring

/-- The real energy of the quadratic-scale subordinate kernel is the weighted
sum of the energies of its even powers. -/
theorem criticalSubordinateDensity_real_energy {X : Type*} (q : X → X → ℝ≥0∞)
    (hq : ∀ x, ∑' y, q x y = 1) (hsym : ∀ x y, q x y = q y x) (f : X → ℝ)
    (hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞) :
    Summable (fun n => (criticalSubordinationWeight n).toReal *
      realKernelEnergy (densityPower (fun _ => 1) q (2 * (n + 1) ^ 2)) f) ∧
    realKernelEnergy (criticalSubordinateDensity (fun _ => 1) q) f =
      ∑' n, (criticalSubordinationWeight n).toReal *
        realKernelEnergy (densityPower (fun _ => 1) q (2 * (n + 1) ^ 2)) f := by
  have hq' : IsMarkovDensity (fun _ => 1) q := by
    intro x
    simpa only [ENNReal.coe_one, mul_one] using hq x
  have hm : ∀ x : X, (1 : ℝ≥0) ≠ 0 := fun _ => one_ne_zero
  have hp (n : ℕ) : ∀ x, ∑' y, densityPower (fun _ => 1) q n x y = 1 := by
    intro x
    simpa only [ENNReal.coe_one, mul_one] using densityPower_isMarkov (fun _ => 1) hm q hq' n x
  have hs (n : ℕ) : ∀ x y, densityPower (fun _ => 1) q n x y =
      densityPower (fun _ => 1) q n y x := densityPower_symmetric (fun _ => 1) hm q hsym n
  have hsub : ∀ x, ∑' y, criticalSubordinateDensity (fun _ => 1) q x y = 1 := by
    intro x
    simpa only [ENNReal.coe_one, mul_one] using
      criticalSubordinateDensity_isMarkov (fun _ => 1) hm q hq' x
  have hsubsym : ∀ x y, criticalSubordinateDensity (fun _ => 1) q x y =
      criticalSubordinateDensity (fun _ => 1) q y x :=
    criticalSubordinateDensity_symmetric (fun _ => 1) hm q hsym
  exact realKernelEnergy_tsum criticalSubordinationWeight
    (fun n => densityPower (fun _ => 1) q (2 * (n + 1) ^ 2)) f
    (fun n => symmetric_markov_energy_lt_top _ (hp _) (hs _) f hf)
    (symmetric_markov_energy_lt_top _ hsub hsubsym f hf)

end LatticeProb.Graph.LongRangeKernel
