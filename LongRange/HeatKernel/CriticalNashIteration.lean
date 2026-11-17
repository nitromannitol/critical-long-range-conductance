import LongRange.HeatKernel.CriticalNashScale
import LongRange.HeatKernel.CriticalOperatorL1
import LongRange.HeatKernel.CriticalPowerEnergy

/-!
# Nash inequality along Markov iterates

The logarithmic Nash inequality controls the loss of squared norm at every
iterate with positive norm.
-/

open LatticeProb Set
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

private theorem lp_norm_sq_eq_tsum {X : Type*} (f : lp (fun _ : X => ℝ) 2) :
    ‖f‖ ^ 2 = ∑' x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, lp.inner_eq_tsum]
  simp only [Real.inner_apply, sq]

/-- The logarithmic Nash inequality yields the norm-loss recurrence. -/
theorem weightedLattice_critical_nash_iteration {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      ∀ (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x),
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (f : lp (fun _ : Site d => ℝ) 2), Summable (fun x => |f x|) →
        (∑' x, |f x|) ≤ 1 → ∀ n : ℕ,
          0 < ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 →
          ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 ≤
            N * (‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 -
              ‖(markovOperatorCLM k hk hsym ^ (n + 1)) f‖ ^ 2) *
            nashScale ((D / ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2) ^
              (2 / (d : ℝ))) := by
  obtain ⟨D, N, hD, hN, hn⟩ := weightedLattice_critical_nash_two_step hd C hC
  refine ⟨D, N, hD, hN, ?_⟩
  intro k hk hsym hlower f hf hf1 n hq
  let T := markovOperatorCLM k hk hsym
  let g := (T ^ n) f
  have ha := markovOperatorCLM_pow_summable_abs k hk hsym f hf n
  have hq' : 0 < ∑' x, g x ^ 2 := by rw [← lp_norm_sq_eq_tsum]; exact hq
  have hL0 : 0 ≤ ∑' x, |g x| := tsum_nonneg (fun _ => abs_nonneg _)
  have hL1 : (∑' x, |g x|) ≤ 1 := ha.2.trans hf1
  have hL2 : (∑' x, |g x|) ^ 2 ≤ 1 := by nlinarith
  have hsquares := tsum_sq_le_tsum_abs_sq g ha.1
  have hT1 : 0 < D * (∑' x, |g x|) ^ 2 / (∑' x, g x ^ 2) :=
    div_pos (mul_pos hD (lt_of_lt_of_le hq' hsquares)) hq'
  have hT2 : 0 < D / (∑' x, g x ^ 2) := div_pos hD hq'
  have hT : D * (∑' x, |g x|) ^ 2 / (∑' x, g x ^ 2) ≤
      D / (∑' x, g x ^ 2) := by
    apply div_le_div_of_nonneg_right _ hq'.le
    nlinarith
  have hpow := Real.rpow_le_rpow hT1.le hT (by positivity : 0 ≤ 2 / (d : ℝ))
  have hscale := nashScale_strictMonoOn.monotoneOn
    (show _ ∈ Ioi 0 from Real.rpow_pos_of_pos hT1 _)
    (show _ ∈ Ioi 0 from Real.rpow_pos_of_pos hT2 _) hpow
  have heq : realKernelEnergy (densityPower (weightedLattice d hd).mass k 2) g =
      ‖g‖ ^ 2 - ‖T g‖ ^ 2 := by
    have hm : (weightedLattice d hd).mass = fun _ => 1 := by
      funext x
      exact weightedLattice_mass hd x
    rw [hm]
    simpa [T] using realKernelEnergy_densityPower_two_mul k hk hsym 1 g
  have hloss : 0 ≤ ‖g‖ ^ 2 - ‖T g‖ ^ 2 := by
    have ht := norm_markovOperator_le k hk hsym g
    change ‖T g‖ ≤ ‖g‖ at ht
    exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 ht)
  have hb := hn k hk hsym hlower g ha.1 hq'
  rw [← lp_norm_sq_eq_tsum, heq] at hb
  have hstep : (T ^ (n + 1)) f = T g := by simp [pow_succ', g]
  change ‖g‖ ^ 2 ≤ N * (‖g‖ ^ 2 - ‖(T ^ (n + 1)) f‖ ^ 2) *
      nashScale ((D / ‖g‖ ^ 2) ^ (2 / (d : ℝ)))
  rw [hstep]
  rw [← lp_norm_sq_eq_tsum] at hscale
  exact hb.trans (mul_le_mul_of_nonneg_left hscale (mul_nonneg hN.le hloss))

end LatticeProb.Graph.LongRangeKernel
