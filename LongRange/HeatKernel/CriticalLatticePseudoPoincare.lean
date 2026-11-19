import LongRange.HeatKernel.CriticalLatticeBall
import LongRange.HeatKernel.CriticalPowerRatio

/-!
# Lattice ball pseudo-Poincaré inequality

Quadratic-time lower bounds and contraction compare averages on lattice balls
with losses of powers of the averaged walk.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The averaged nearest-neighbour Markov operator on the lattice. -/
noncomputable def latticeAveragedMarkovOperator {d : ℕ} (hd : 0 < d) :
    lp (fun _ : Site d => ℝ) 2 →L[ℝ] lp (fun _ : Site d => ℝ) 2 :=
  markovOperatorCLM (averagedDensity (weightedLattice d hd).mass
    (weightedLattice d hd).referenceDensity)
    (by
      intro x
      simpa only [weightedLattice_mass, ENNReal.coe_one, mul_one] using
        averagedDensity_isMarkov (weightedLattice d hd).mass
          (by intro y; simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true])
          _ (weightedLattice_isMarkovDensity hd) x)
    (averagedDensity_symmetric (weightedLattice d hd).mass
      (by intro y; simp only [weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true])
      _ (weightedLattice d hd).referenceDensity_symmetric)

/-- The lattice graph ball of a real radius, centered at zero. -/
noncomputable def latticeRealGraphBall (d : ℕ) (R : ℝ) : Finset (Site d) :=
  latticeGraphBall d ⌊R⌋₊

/-- A site belongs to a lattice graph ball exactly when its distance is within the radius. -/
theorem mem_latticeRealGraphBall {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (z : Site d) :
    z ∈ latticeRealGraphBall d R ↔ (graphNorm z : ℝ) ≤ R := by
  rw [latticeRealGraphBall, mem_latticeGraphBall, Nat.le_floor_iff hR]

/-- Averaging over a real-radius lattice ball is controlled by a quadratic-time loss. -/
theorem weightedLattice_pseudoPoincare_norm {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ R →
      ∀ f : lp (fun _ : Site d => ℝ) 2,
      Summable (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
      (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
        C * (R / k) ^ 2 *
          (‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (k ^ 2)) f‖ ^ 2) := by
  obtain ⟨A, hA, hball⟩ := weightedLattice_ball_average_le_power_loss hd
  refine ⟨2 * A, by positivity, ?_⟩
  intro R hR k hk hkR f
  let r := ⌊R⌋₊
  have hkr : k ≤ r := (Nat.le_floor_iff (by linarith : 0 ≤ R)).2 hkR
  have hr : 1 ≤ r := hk.trans hkr
  have hrR : (r : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hpow : k ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hkr _
  have hkp : 0 < k ^ 2 := pow_pos (by omega) _
  have hfirst := hball r hr f
  change (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
    A * (‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (r ^ 2)) f‖ ^ 2) at hfirst
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
  have hratio := markovOperatorCLM_norm_sq_loss_le_ratio q hq hsym (k ^ 2) (r ^ 2) hkp hpow f
  change ‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (r ^ 2)) f‖ ^ 2 ≤
    (2 * ((r ^ 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ)) *
      (‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (k ^ 2)) f‖ ^ 2) at hratio
  have hloss : 0 ≤ ‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (k ^ 2)) f‖ ^ 2 := by
    have h := markovOperatorCLM_pow_norm_sq_loss_le q hq hsym f (Nat.zero_le (k ^ 2))
    simpa only [pow_zero, one_apply_eq_self, sub_self, latticeAveragedMarkovOperator, q] using h
  have hsquare : (r : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr0 hrR 2
  have hfactor : 2 * ((r ^ 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ) ≤ 2 * (R / k) ^ 2 := by
    push_cast
    rw [div_pow, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  have hf : Summable (fun x => f x ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine ⟨(finsetTranslateAverage_sq_tsum_le (latticeGraphBall d r)
    (latticeGraphBall_nonempty d r) f hf).1, ?_⟩
  calc
    _ ≤ A * (‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (r ^ 2)) f‖ ^ 2) := hfirst
    _ ≤ A * ((2 * ((r ^ 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ)) *
        (‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (k ^ 2)) f‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hratio hA.le
    _ ≤ (2 * A) * (R / k) ^ 2 *
        (‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (k ^ 2)) f‖ ^ 2) := by
          have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfactor hloss) hA.le
          nlinarith

/-- The lattice pseudo-Poincaré inequality in terms of the even-power energy. -/
theorem weightedLattice_pseudoPoincare {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ R →
      ∀ f : lp (fun _ : Site d => ℝ) 2,
      Summable (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
      (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
        C * (R / k) ^ 2 * realKernelEnergy
          (densityPower (weightedLattice d hd).mass
            (averagedDensity (weightedLattice d hd).mass
              (weightedLattice d hd).referenceDensity) (2 * k ^ 2)) f := by
  obtain ⟨C, hC, hbound⟩ := weightedLattice_pseudoPoincare_norm hd
  refine ⟨C, hC, ?_⟩
  intro R hR k hk hkR f
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
  have he := realKernelEnergy_densityPower_two_mul q hq hsym (k ^ 2) f
  change realKernelEnergy (densityPower (fun _ => 1) q (2 * k ^ 2)) f =
    ‖f‖ ^ 2 - ‖(latticeAveragedMarkovOperator hd ^ (k ^ 2)) f‖ ^ 2 at he
  rw [← hmass] at he
  exact ⟨(hbound R hR k hk hkR f).1, by rw [he]; exact (hbound R hR k hk hkR f).2⟩

end LatticeProb.Graph.LongRangeKernel
