import LongRange.HeatKernel.CriticalNashIteration
import LongRange.HeatKernel.CriticalPowerLoss

/-!
# Decreasing losses in the critical Nash recurrence

The Nash inequality at the next iterate is controlled by the preceding loss.
-/

open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The next norm is controlled by the preceding squared-norm loss. -/
theorem weightedLattice_critical_nash_next {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      ∀ (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x),
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (f : lp (fun _ : Site d => ℝ) 2), Summable (fun x => |f x|) →
        (∑' x, |f x|) ≤ 1 → ∀ n : ℕ,
          0 < ‖(markovOperatorCLM k hk hsym ^ (n + 1)) f‖ ^ 2 →
          ‖(markovOperatorCLM k hk hsym ^ (n + 1)) f‖ ^ 2 ≤
            N * (‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 -
              ‖(markovOperatorCLM k hk hsym ^ (n + 1)) f‖ ^ 2) *
            nashScale ((D / ‖(markovOperatorCLM k hk hsym ^ (n + 1)) f‖ ^ 2) ^
              (2 / (d : ℝ))) := by
  obtain ⟨D, N, hD, hN, hn⟩ := weightedLattice_critical_nash_iteration hd C hC
  refine ⟨D, N, hD, hN, ?_⟩
  intro k hk hsym hlower f hf hf1 n hq
  have hrec := hn k hk hsym hlower f hf hf1 (n + 1) hq
  have hloss := markovOperatorCLM_block_loss_succ_le k hk hsym 1 n f
  simp only [mul_one] at hloss
  have hscale : 0 ≤ nashScale ((D / ‖(markovOperatorCLM k hk hsym ^ (n + 1)) f‖ ^ 2) ^
      (2 / (d : ℝ))) := by
    exact (nashScale_pos (Real.rpow_pos_of_pos (div_pos hD hq) _)).le
  exact hrec.trans (by gcongr)

end LatticeProb.Graph.LongRangeKernel
