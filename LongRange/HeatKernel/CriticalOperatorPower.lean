import LongRange.HeatKernel.CriticalOperatorSpectral
import LongRange.HeatKernel.CriticalSubordination

/-!
# Kernel powers and Markov operators

Counting-measure kernel powers act as powers of their Markov operator.
-/

open scoped NNReal ENNReal InnerProductSpace

namespace LatticeProb.Graph.LongRangeKernel

private theorem summable_kernel_comp_mul {X : Type*} (a b : X → X → ℝ≥0∞)
    (ha : ∀ x, ∑' y, a x y = 1) (hb : ∀ x, ∑' y, b x y = 1)
    (f : lp (fun _ : X => ℝ) 2) (x : X) :
    Summable (fun p : X × X => (a x p.1).toReal * (b p.1 p.2).toReal * f p.2) := by
  have hmass : (∑' p : X × X, a x p.1 * b p.1 p.2) = 1 := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, hb, mul_one, ha]
  have hs := ENNReal.summable_toReal (by rw [hmass]; exact ENNReal.one_ne_top)
  have hs' : Summable (fun p : X × X => (a x p.1).toReal * (b p.1 p.2).toReal) := by
    simpa only [ENNReal.toReal_mul] using hs
  apply Summable.of_norm_bounded (hs'.mul_right ‖f‖)
  intro ⟨z, y⟩
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg ENNReal.toReal_nonneg]
  have hf : |f y| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num) f y
  exact mul_le_mul_of_nonneg_left hf
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

private theorem densityComp_apply {X : Type*} (a b : X → X → ℝ≥0∞)
    (ha : ∀ x, ∑' y, a x y = 1) (hb : ∀ x, ∑' y, b x y = 1)
    (f : lp (fun _ : X => ℝ) 2) (x : X) :
    (∑' y, (densityComp (fun _ => 1) a b x y).toReal * f y) =
      ∑' z, (a x z).toReal * ∑' y, (b z y).toReal * f y := by
  have hs := summable_kernel_comp_mul a b ha hb f x
  have hfin (y : X) : (∑' z, a x z * b z y) ≠ ⊤ := by
    have hle : (∑' z, a x z * b z y) ≤ 1 := by
      calc
        _ ≤ ∑' z, a x z := by
          apply ENNReal.tsum_le_tsum
          intro z
          exact mul_le_of_le_one_right' ((ENNReal.le_tsum y).trans_eq (hb z))
        _ = 1 := ha x
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  calc
    _ = ∑' y, ∑' z, (a x z).toReal * (b z y).toReal * f y := by
      apply tsum_congr
      intro y
      simp only [densityComp, ENNReal.coe_one, mul_one]
      rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top (hfin y)), ← tsum_mul_right]
      apply tsum_congr
      intro z
      rw [ENNReal.toReal_mul]
    _ = ∑' p : X × X, (a x p.1).toReal * (b p.1 p.2).toReal * f p.2 := by
      rw [hs.tsum_comm, ← hs.tsum_prod]
    _ = _ := by
      rw [hs.tsum_prod]
      apply tsum_congr
      intro z
      rw [← tsum_mul_left]
      apply tsum_congr
      intro y
      ring

/-- A counting-measure kernel power acts as the corresponding operator power. -/
theorem densityPower_apply_eq_operator_pow {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (n : ℕ) (f : lp (fun _ : X => ℝ) 2) (x : X) :
    (∑' y, (densityPower (fun _ => 1) k n x y).toReal * f y) =
      ((markovOperatorCLM k hk hsym ^ n) f) x := by
  classical
  induction n generalizing x with
  | zero =>
      simp [densityPower, identityDensity, apply_ite, ite_mul]
  | succ n ih =>
      have hp : ∀ z, ∑' y, densityPower (fun _ => 1) k n z y = 1 := by
        have h := densityPower_isMarkov (fun _ : X => 1) (by simp) k
          (by simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using hk) n
        simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using h
      change (∑' y, (densityComp (fun _ => 1) k
        (densityPower (fun _ => 1) k n) x y).toReal * f y) = _
      rw [densityComp_apply k _ hk hp f x]
      simp_rw [ih]
      rw [pow_succ', mul_apply_eq_comp]
      rfl

/-- The energy of a symmetric Markov kernel power is at most its time times the original energy. -/
theorem realKernelEnergy_densityPower_le {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (n : ℕ) (f : lp (fun _ : X => ℝ) 2) :
    realKernelEnergy (densityPower (fun _ => 1) k n) f ≤
      (n : ℝ) * realKernelEnergy k f := by
  have hp : ∀ x, ∑' y, densityPower (fun _ => 1) k n x y = 1 := by
    have h := densityPower_isMarkov (fun _ : X => 1) (by simp) k
      (by simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using hk) n
    simpa only [IsMarkovDensity, ENNReal.coe_one, mul_one] using h
  have hs := densityPower_symmetric (fun _ : X => 1) (by simp) k hsym n
  rw [realKernelEnergy_eq_inner _ hp hs f]
  have heq : markovOperatorCLM (densityPower (fun _ => 1) k n) hp hs f =
      (markovOperatorCLM k hk hsym ^ n) f := by
    apply lp.ext
    funext x
    exact densityPower_apply_eq_operator_pow k hk hsym n f x
  rw [heq]
  exact markovOperatorCLM_pow_energy_le k hk hsym n f

end LatticeProb.Graph.LongRangeKernel
