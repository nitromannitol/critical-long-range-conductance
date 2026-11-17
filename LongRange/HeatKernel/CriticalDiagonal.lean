import LongRange.HeatKernel.CriticalNashTime
import LongRange.HeatKernel.CriticalOperatorPower
import LongRange.Support.Analysis.CriticalProfile

/-!
# Diagonal bounds for critical Markov kernels

Even-time diagonal kernel values are squared norms of point-mass iterates.
-/

open LatticeProb
open scoped NNReal ENNReal InnerProductSpace

namespace LatticeProb.Graph.LongRangeKernel

/-- An even diagonal kernel value equals the squared norm of an iterated point mass. -/
theorem densityPower_diagonal_eq_norm_sq {X : Type*} [DecidableEq X] (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (n : ℕ) (x : X) :
    (densityPower (fun _ => 1) k (2 * n) x x).toReal =
      ‖(markovOperatorCLM k hk hsym ^ n) (lp.single 2 x (1 : ℝ))‖ ^ 2 := by
  classical
  let δ : lp (fun _ : X => ℝ) 2 := lp.single 2 x (1 : ℝ)
  let T := markovOperatorCLM k hk hsym
  have heval : (densityPower (fun _ => 1) k (2 * n) x x).toReal =
      ((T ^ (2 * n)) δ) x := by
    rw [← densityPower_apply_eq_operator_pow k hk hsym (2 * n) δ x]
    symm
    rw [tsum_eq_single x]
    · simp [δ]
    · intro y hy
      simp [δ, hy]
  have hsympow : IsSelfAdjoint (T ^ n) := (markovOperatorCLM_isSelfAdjoint k hk hsym).pow n
  have hi := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsympow) ((T ^ n) δ) δ
  change ⟪(T ^ n) ((T ^ n) δ), δ⟫_ℝ = ⟪(T ^ n) δ, (T ^ n) δ⟫_ℝ at hi
  have hcomp : (T ^ (2 * n)) δ = (T ^ n) ((T ^ n) δ) := by
    rw [show 2 * n = n + n by omega, pow_add, mul_apply_eq_comp]
  calc
    _ = ((T ^ n) ((T ^ n) δ)) x := by rw [heval, hcomp]
    _ = ⟪(T ^ n) ((T ^ n) δ), δ⟫_ℝ := by simp [δ, lp.inner_single_right]
    _ = _ := hi.trans (real_inner_self_eq_norm_sq _)

/-- A critical lattice kernel has an inverse-profile even diagonal bound. -/
theorem weightedLattice_critical_diagonal_profile {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      ∀ (_hk : ∀ x, ∑' y, k x y = 1) (_hsym : ∀ x y, k x y = k y x),
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ n : ℕ, 0 < n → ∀ x,
        (densityPower (fun _ => 1) k (2 * n) x x).toReal ≤
          D * nashProfile d ((n : ℝ) / (N * (d : ℝ))) := by
  obtain ⟨D, N, hD, hN, hp⟩ := weightedLattice_critical_nash_profile hd C hC
  refine ⟨D, N, hD, hN, ?_⟩
  intro k hk hsym hlower n hn x
  let δ : lp (fun _ : Site d => ℝ) 2 := lp.single 2 x (1 : ℝ)
  have hs : Summable (fun y => |δ y|) := by
    apply summable_of_ne_finset_zero (s := {x})
    intro y hy
    have hyx : y ≠ x := by simpa using hy
    simp [δ, hyx]
  have hsum : (∑' y, |δ y|) ≤ 1 := by
    rw [tsum_eq_single x]
    · simp [δ]
    · intro y hy
      simp [δ, hy]
  rw [densityPower_diagonal_eq_norm_sq k hk hsym n x]
  exact hp k hk hsym hlower δ hs hsum n hn

/-- At integer times, the inverse Nash profile has the usual logarithmic decay. -/
theorem nashProfile_nat_le {d : ℕ} (hd : 1 ≤ d) {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      nashProfile d ((n : ℝ) / A) ≤
        B * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
  obtain ⟨B, hB, hscale⟩ := criticalProfile_scale d (inv_pos.mpr hA)
  refine ⟨B * (2 : ℝ) ^ ((d : ℝ) / 2),
    mul_pos hB (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hl0 : 0 ≤ Real.log (1 + (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 + (n : ℝ)) ≤ 2 * Real.log (1 + (n : ℝ)) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log
      (by positivity : 0 < 2 + (n : ℝ))
      (show 2 + (n : ℝ) ≤ (1 + (n : ℝ)) ^ 2 by nlinarith)
  have hbase : 1 + (n : ℝ) * Real.log (2 + n) ≤
      2 * ((n : ℝ) * (1 + Real.log (1 + n))) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hn0.le]
  have hpos : 0 < (n : ℝ) * (1 + Real.log (1 + n)) :=
    mul_pos hn0 (by linarith)
  have hlog2 : 0 ≤ Real.log (2 + (n : ℝ)) := Real.log_nonneg (by linarith)
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity :
    0 < 1 + (n : ℝ) * Real.log (2 + n)) hbase
    (neg_nonpos.mpr (by positivity : 0 ≤ (d : ℝ) / 2))
  have hprofile : criticalProfile d (n : ℝ) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
    have h := mul_le_mul_of_nonneg_left hpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((d : ℝ) / 2))
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hpos.le,
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      add_neg_cancel, Real.rpow_zero, one_mul] at h
    exact h
  calc
    nashProfile d ((n : ℝ) / A) ≤ criticalProfile d ((n : ℝ) / A) :=
      (nashProfile_comparison hd (div_pos hn0 hA)).2
    _ ≤ B * criticalProfile d (n : ℝ) := by
      simpa only [div_eq_mul_inv, mul_comm] using hscale n hn0
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hprofile hB.le
      nlinarith

/-- The even diagonal has uniform critical logarithmic decay. -/
theorem weightedLattice_critical_diagonal {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      ∀ (_hk : ∀ x, ∑' y, k x y = 1) (_hsym : ∀ x y, k x y = k y x),
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ n : ℕ, ∀ x,
        (densityPower (fun _ => 1) k (2 * n) x x).toReal ≤
          K * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
  obtain ⟨D, N, hD, hN, hb⟩ := weightedLattice_critical_diagonal_profile hd C hC
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨B, hB, hp⟩ := nashProfile_nat_le hd (mul_pos hN hdpos)
  let K := max 1 (D * B)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro k hk hsym hlower n x
  by_cases hn : n = 0
  · subst n
    simp only [densityPower, identityDensity, ite_true, ENNReal.coe_one,
      inv_one, ENNReal.toReal_one, Nat.cast_zero, zero_mul, add_zero, Real.one_rpow, mul_one]
    exact le_max_left _ _
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hlog : 0 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hbase : 0 ≤ (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) :=
      Real.rpow_nonneg (by positivity) _
    calc
      _ ≤ D * nashProfile d ((n : ℝ) / (N * (d : ℝ))) := hb k hk hsym hlower n hn' x
      _ ≤ (D * B) * (1 + (n : ℝ) * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) := by
        have h := mul_le_mul_of_nonneg_left (hp n hn') hD.le
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hbase

end LatticeProb.Graph.LongRangeKernel
