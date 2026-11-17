import LongRange.HeatKernel.CriticalNashLoss
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral comparison for Nash recurrences

A decreasing sequence satisfying a Nash recurrence is bounded by the
integral of its reciprocal profile.
-/

open LatticeProb MeasureTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- Integrating the reciprocal Nash profile over each norm loss bounds time. -/
theorem nash_integral_comparison (u : ℕ → ℝ) (p : ℝ → ℝ)
    (hmono : Antitone u)
    (hp : AntitoneOn p (Ioi 0))
    (hint : ∀ a b, 0 < a → 0 < b → IntervalIntegrable p volume a b)
    (hrec : ∀ n, 0 < u (n + 1) → 1 ≤ (u n - u (n + 1)) * p (u n)) :
    ∀ n : ℕ, 0 < u n → (n : ℝ) ≤ ∫ s in u n..u 0, p s := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hpos
    have hle : u (n + 1) ≤ u n := hmono (Nat.le_succ n)
    have hprev : 0 < u n := hpos.trans_le hle
    have hzero : 0 < u 0 := hprev.trans_le (hmono (Nat.zero_le n))
    have ih := ih hprev
    have hstep : 1 ≤ ∫ s in u (n + 1)..u n, p s := by
      calc
        1 ≤ (u n - u (n + 1)) * p (u n) := hrec n hpos
        _ = ∫ _ in u (n + 1)..u n, p (u n) := by simp
        _ ≤ ∫ s in u (n + 1)..u n, p s := by
          apply intervalIntegral.integral_mono_on hle intervalIntegrable_const
            (hint _ _ hpos hprev)
          intro s hs
          exact hp (hpos.trans_le hs.1) hprev hs.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hint (u (n + 1)) (u n) hpos hprev)
      (hint (u n) (u 0) hprev hzero)
    rw [Nat.cast_succ]
    linarith

/-- The critical reciprocal Nash profile decreases on the positive axis. -/
theorem criticalNash_integrand_antitone (D q : ℝ) (hD : 0 < D) (hq : 0 ≤ q) :
    AntitoneOn (fun s : ℝ => nashScale ((D / s) ^ q) / s) (Ioi 0) := by
  intro x hx y hy hxy
  have hdiv : D / y ≤ D / x := div_le_div_of_nonneg_left hD.le hx hxy
  have hpow := Real.rpow_le_rpow (div_pos hD hy).le hdiv hq
  have hscale := nashScale_strictMonoOn.monotoneOn
    (show (D / y) ^ q ∈ Ioi 0 from Real.rpow_pos_of_pos (div_pos hD hy) _)
    (show (D / x) ^ q ∈ Ioi 0 from Real.rpow_pos_of_pos (div_pos hD hx) _) hpow
  exact (div_le_div_of_nonneg_right hscale hy.le).trans
    (div_le_div_of_nonneg_left (nashScale_pos
      (Real.rpow_pos_of_pos (div_pos hD hx) _)).le hx hxy)

/-- The critical reciprocal Nash profile is integrable on positive intervals. -/
theorem criticalNash_integrand_intervalIntegrable (D q : ℝ) (hD : 0 < D) (hq : 0 ≤ q)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s : ℝ => nashScale ((D / s) ^ q) / s) volume a b := by
  apply AntitoneOn.intervalIntegrable
  apply (criticalNash_integrand_antitone D q hD hq).mono
  intro s hs
  change min a b ≤ s ∧ s ≤ max a b at hs
  exact (lt_min ha hb).trans_le hs.1

/-- Integral comparison for the logarithmic Nash profile. -/
theorem criticalNash_integral_comparison (u : ℕ → ℝ) (D N q : ℝ)
    (hD : 0 < D) (hN : 0 < N) (hq : 0 ≤ q) (hmono : Antitone u)
    (hrec : ∀ n, 0 < u n → u n ≤
      N * (u n - u (n + 1)) * nashScale ((D / u n) ^ q)) :
    ∀ n : ℕ, 0 < u n → (n : ℝ) ≤
      ∫ s in u n..u 0, N * (nashScale ((D / s) ^ q) / s) := by
  apply nash_integral_comparison u _ hmono
  · intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left
      (criticalNash_integrand_antitone D q hD hq hx hy hxy) hN.le
  · intro a b ha hb
    exact (criticalNash_integrand_intervalIntegrable D q hD hq ha hb).const_mul N
  · intro n hn
    have hn' : 0 < u n := hn.trans_le (hmono (Nat.le_succ n))
    have h := hrec n hn'
    have hnorm : 1 ≤ (N * (u n - u (n + 1)) *
        nashScale ((D / u n) ^ q)) / u n := by
      apply (le_div_iff₀ hn').2
      simpa using h
    convert hnorm using 1; ring

/-- The squared norms of critical-kernel iterates satisfy the integral comparison. -/
theorem weightedLattice_critical_nash_integral {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      ∀ (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x),
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ (f : lp (fun _ : Site d => ℝ) 2), Summable (fun x => |f x|) →
        (∑' x, |f x|) ≤ 1 → ∀ n : ℕ,
          0 < ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 →
          (n : ℝ) ≤ ∫ s in ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2..‖f‖ ^ 2,
            N * (nashScale ((D / s) ^ (2 / (d : ℝ))) / s) := by
  obtain ⟨D, N, hD, hN, hn⟩ := weightedLattice_critical_nash_iteration hd C hC
  refine ⟨D, N, hD, hN, ?_⟩
  intro k hk hsym hlower f hf hf1 n hpos
  let u : ℕ → ℝ := fun n => ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2
  have hmono : Antitone u := by
    intro i j hij
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (antitone_norm_markovOperatorCLM_pow k hk hsym f hij)
  have hq : 0 ≤ 2 / (d : ℝ) := by positivity
  have h := criticalNash_integral_comparison u D N (2 / (d : ℝ))
    hD hN hq hmono (hn k hk hsym hlower f hf hf1) n hpos
  simpa [u] using h

end LatticeProb.Graph.LongRangeKernel
