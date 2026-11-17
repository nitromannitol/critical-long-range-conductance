import LongRange.HeatKernel.CriticalNashTime
import LongRange.HeatKernel.CriticalOperatorPower

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

end LatticeProb.Graph.LongRangeKernel
