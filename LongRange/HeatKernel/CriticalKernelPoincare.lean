import LongRange.HeatKernel.CriticalKernelComparison
import LongRange.HeatKernel.CriticalSubordinateLogPoincare

/-!
# Critical pseudo-Poincaré inequality

Comparison with the subordinated walk gives a logarithmic bound for symmetric
Markov kernels satisfying the critical lower jump estimate.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- Critical lower jump bounds imply a uniform pseudo-Poincaré inequality for large radii. -/
theorem weightedLattice_critical_pseudoPoincare {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (R : ℝ), 1 ≤ R → ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
        Real.log (1 + R) *
            (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
          A * R ^ 2 * realKernelEnergy k f := by
  obtain ⟨B, hB, hsub⟩ := weightedLattice_subordinate_pseudoPoincare hd
  obtain ⟨D, hD, hdom⟩ := weightedLattice_subordinate_le_of_lower hd C hC
  refine ⟨B * D, by positivity, ?_⟩
  intro k hk hsym hlower R hR f
  let m := (weightedLattice d hd).mass
  let q := averagedDensity m (weightedLattice d hd).referenceDensity
  let p := criticalSubordinateDensity m q
  have hm : ∀ x, m x ≠ 0 := by
    intro x; simp only [m, weightedLattice_mass, ne_eq, one_ne_zero, not_false_eq_true]
  have hq : IsMarkovDensity m q :=
    averagedDensity_isMarkov m hm _ (weightedLattice_isMarkovDensity hd)
  have hqs : ∀ x y, q x y = q y x :=
    averagedDensity_symmetric m hm _ (weightedLattice d hd).referenceDensity_symmetric
  have hp : ∀ x, ∑' y, p x y = 1 := by
    intro x
    simpa only [p, m, weightedLattice_mass, ENNReal.coe_one, mul_one] using
      criticalSubordinateDensity_isMarkov m hm q hq x
  have hps : ∀ x y, p x y = p y x := criticalSubordinateDensity_symmetric m hm q hqs
  have hf : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞ := by
    have h : Summable (fun x => f x ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact h.tsum_ofReal_lt_top
  have henergy := realKernelEnergy_le_of_offDiag p k hp hk hps hsym D
    (fun x y _ => hdom k hk hlower x y) f hf
  have h := hsub R hR f
  refine ⟨h.1, h.2.trans ?_⟩
  have hmult := mul_le_mul_of_nonneg_left henergy (show 0 ≤ B * R ^ 2 by positivity)
  convert hmult using 1
  ring

/-- Critical lower jump bounds give a pseudo-Poincaré inequality for every positive radius. -/
theorem weightedLattice_critical_pseudoPoincare_all_radii {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (R : ℝ), 0 < R → ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ∧
        Real.log (1 + R) *
            (∑' x, (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) ≤
          A * R ^ 2 * realKernelEnergy k f := by
  obtain ⟨A, hA, hlarge⟩ := weightedLattice_critical_pseudoPoincare hd C hC
  refine ⟨A, hA, ?_⟩
  intro k hk hsym hlower R hR f
  by_cases hR1 : 1 ≤ R
  · exact hlarge k hk hsym hlower R hR1 f
  · have hball : latticeRealGraphBall d R = {0} := by
      ext z
      simp only [latticeRealGraphBall, Nat.floor_eq_zero.mpr (lt_of_not_ge hR1),
        mem_latticeGraphBall, Nat.le_zero, graphNorm_eq_zero_iff, Finset.mem_singleton]
    have hzero : (fun x => (f x - finsetTranslateAverage (latticeRealGraphBall d R) f x) ^ 2) =
        fun _ => 0 := by
      funext x
      simp only [hball, finsetTranslateAverage, Finset.sum_singleton, Finset.card_singleton,
        Nat.cast_one, div_one, add_zero, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have he : 0 ≤ realKernelEnergy k f := by
      unfold realKernelEnergy
      exact mul_nonneg (by norm_num) (tsum_nonneg (fun x => tsum_nonneg (fun y =>
        mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))))
    rw [hzero]
    simp only [summable_zero, tsum_zero, mul_zero, true_and]
    positivity

end LatticeProb.Graph.LongRangeKernel
