import LongRange.HeatKernel.CriticalPowerContraction
import LongRange.HeatKernel.CriticalOperatorSpectral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Decreasing losses of symmetric contractions

Successive blocks of iterates lose decreasing amounts of squared norm.
-/

open scoped InnerProductSpace NNReal ENNReal ComplexOrder

namespace LatticeProb.Graph.LongRangeKernel

private theorem square_defect_positive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) : 0 ≤ 1 - T ^ 2 := by
  rw [ContinuousLinearMap.le_def, sub_zero, ContinuousLinearMap.isPositive_iff']
  constructor
  · exact (show IsSelfAdjoint (1 : H →L[ℂ] H) by simp [IsSelfAdjoint]).sub (hT.pow 2)
  · intro f
    change 0 ≤ ⟪f - (T ^ 2) f, f⟫_ℂ
    have hi := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) (T f) f
    change ⟪T (T f), f⟫_ℂ = ⟪T f, T f⟫_ℂ at hi
    have hc : ‖T f‖ ≤ ‖f‖ := by
      calc
        ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
        _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg f)
        _ = ‖f‖ := one_mul _
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hc
    simp only [pow_two, mul_apply_eq_comp, inner_sub_left, hi, inner_self_eq_norm_sq_to_K]
    rw [RCLike.nonneg_iff]
    constructor
    · simpa [Complex.mul_re, pow_two] using sub_nonneg.mpr hs
    · simp

/-- The square root of the defect represents the loss of squared norm. -/
theorem norm_sqrt_square_defect {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) (f : H) :
    ‖(CFC.sqrt (1 - T ^ 2) : H →L[ℂ] H) f‖ ^ 2 = ‖f‖ ^ 2 - ‖T f‖ ^ 2 := by
  let R := CFC.sqrt (1 - T ^ 2)
  have hp : 0 ≤ 1 - T ^ 2 := square_defect_positive T hT hn
  have hr : IsSelfAdjoint R := (CFC.sqrt_nonneg (1 - T ^ 2)).isSelfAdjoint
  have hrsq : R * R = 1 - T ^ 2 := CFC.sqrt_mul_sqrt_self _ hp
  have hi := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hr) (R f) f
  change ⟪R (R f), f⟫_ℂ = ⟪R f, R f⟫_ℂ at hi
  have ht := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) (T f) f
  change ⟪T (T f), f⟫_ℂ = ⟪T f, T f⟫_ℂ at ht
  have he : R (R f) = f - T (T f) := by
    have h := congrArg (fun A : H →L[ℂ] H => A f) hrsq
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, pow_two] using h
  rw [he, inner_sub_left, ht] at hi
  have hre := congrArg Complex.re hi
  change RCLike.re (⟪f, f⟫_ℂ - ⟪T f, T f⟫_ℂ) = RCLike.re ⟪R f, R f⟫_ℂ at hre
  simpa only [map_sub, inner_self_eq_norm_sq, R] using hre.symm

/-- Successive blocks of a self-adjoint contraction lose decreasing squared norm. -/
theorem norm_sq_block_loss_succ_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) (n : ℕ) (f : H) :
    ‖(T ^ (n + 1)) f‖ ^ 2 - ‖(T ^ (n + 2)) f‖ ^ 2 ≤
      ‖(T ^ n) f‖ ^ 2 - ‖(T ^ (n + 1)) f‖ ^ 2 := by
  let R := CFC.sqrt (1 - T ^ 2)
  have hc : Commute R T := by
    have h : Commute (1 - T ^ 2) T := (Commute.one_left T).sub_left (Commute.pow_left (Commute.refl T) 2)
    exact h.cfcₙ_nnreal NNReal.sqrt
  have hswap (g : H) : R (T g) = T (R g) := by
    have h := congrArg (fun A : H →L[ℂ] H => A g) hc.eq
    simpa only [mul_apply_eq_comp] using h
  have hcon (g : H) : ‖T g‖ ≤ ‖g‖ := by
    calc
      ‖T g‖ ≤ ‖T‖ * ‖g‖ := T.le_opNorm g
      _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg g)
      _ = ‖g‖ := one_mul _
  have hloss (g : H) : ‖R g‖ ^ 2 = ‖g‖ ^ 2 - ‖T g‖ ^ 2 :=
    norm_sqrt_square_defect T hT hn g
  have hs := (sq_le_sq₀ (norm_nonneg (T (R ((T ^ n) f))))
    (norm_nonneg (R ((T ^ n) f)))).2 (hcon _)
  rw [← hswap, hloss, hloss] at hs
  simpa only [pow_succ', mul_apply_eq_comp, show n + 2 = (n + 1) + 1 by omega] using hs

/-- Successive blocks of a symmetric Markov operator lose decreasing squared norm. -/
theorem markovOperatorCLM_block_loss_succ_le {V : Type*} (k : V → V → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (b m : ℕ) (f : lp (fun _ : V => ℝ) 2) :
    ‖(markovOperatorCLM k hk hsym ^ ((m + 1) * b)) f‖ ^ 2 -
        ‖(markovOperatorCLM k hk hsym ^ ((m + 2) * b)) f‖ ^ 2 ≤
      ‖(markovOperatorCLM k hk hsym ^ (m * b)) f‖ ^ 2 -
        ‖(markovOperatorCLM k hk hsym ^ ((m + 1) * b)) f‖ ^ 2 := by
  let Q := markovOperatorCLM k hk hsym
  let T := ComplexSequenceSpace.complexify (Q ^ b)
  have hT : IsSelfAdjoint T := ComplexSequenceSpace.complexify_isSelfAdjoint _
    ((markovOperatorCLM_isSelfAdjoint k hk hsym).pow b)
  have hn : ‖T‖ ≤ 1 := by
    rw [show T = ComplexSequenceSpace.complexify (Q ^ b) by rfl,
      ComplexSequenceSpace.complexify_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    have h := antitone_norm_markovOperatorCLM_pow k hk hsym g (Nat.zero_le b)
    simpa only [pow_zero, one_apply_eq_self, one_mul, Q] using h
  have h := norm_sq_block_loss_succ_le T hT hn m (ComplexSequenceSpace.ofReal V f)
  have hpow (n : ℕ) : (T ^ n) (ComplexSequenceSpace.ofReal V f) =
      ComplexSequenceSpace.ofReal V ((Q ^ (n * b)) f) := by
    rw [show T = ComplexSequenceSpace.complexify (Q ^ b) by rfl,
      ComplexSequenceSpace.complexify_pow_ofReal, ← pow_mul, Nat.mul_comm]
  rw [hpow, hpow, hpow] at h
  simpa only [ComplexSequenceSpace.ofReal_norm, Q] using h

/-- The loss over several blocks is bounded by the number of blocks times the first loss. -/
theorem markovOperatorCLM_multiple_norm_sq_loss_le {V : Type*} (k : V → V → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (b m : ℕ) (f : lp (fun _ : V => ℝ) 2) :
    ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ (m * b)) f‖ ^ 2 ≤
      (m : ℝ) * (‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ b) f‖ ^ 2) := by
  let Q := markovOperatorCLM k hk hsym
  have ha : Antitone (fun n : ℕ => ‖(Q ^ (n * b)) f‖ ^ 2 -
      ‖(Q ^ ((n + 1) * b)) f‖ ^ 2) := by
    apply antitone_nat_of_succ_le
    intro n
    simpa only [Nat.succ_eq_add_one, show n + 1 + 1 = n + 2 by omega, Q] using
      markovOperatorCLM_block_loss_succ_le k hk hsym b n f
  induction m with
  | zero => simp
  | succ m ih =>
      have h := ha (Nat.zero_le m)
      simp only [zero_mul, pow_zero, one_apply_eq_self, zero_add, one_mul] at h
      simp only [Nat.cast_succ]
      nlinarith

/-- A time bounded by a number of blocks has at most that multiple of the block loss. -/
theorem markovOperatorCLM_norm_sq_loss_le_blocks {V : Type*} (k : V → V → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (b m n : ℕ) (hn : n ≤ m * b) (f : lp (fun _ : V => ℝ) 2) :
    ‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ n) f‖ ^ 2 ≤
      (m : ℝ) * (‖f‖ ^ 2 - ‖(markovOperatorCLM k hk hsym ^ b) f‖ ^ 2) :=
  (markovOperatorCLM_pow_norm_sq_loss_le k hk hsym f hn).trans
    (markovOperatorCLM_multiple_norm_sq_loss_le k hk hsym b m f)

end LatticeProb.Graph.LongRangeKernel
