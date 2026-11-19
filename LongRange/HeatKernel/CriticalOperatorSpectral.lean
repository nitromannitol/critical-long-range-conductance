/- `inner_decomposition` is copied from Leonardo Bonanno's lean-formalizations
(https://github.com/leobon12/lean-formalizations), commit fdb5cad, module
ReflectedGMS.Forms.ComplexResolvent, with the namespace renamed as in
`CriticalComplexification` and its final tactic combinator written as `all_goals`.
`complexify_isSelfAdjoint` follows the proof of `complexOneResolvent_isSelfAdjoint` in
the same module, for a general self-adjoint operator. -/
import LongRange.HeatKernel.CriticalComplexification
import LongRange.HeatKernel.CriticalSpectralComparison
import LongRange.HeatKernel.CriticalOperatorPositive
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Spectral comparison of Markov operator powers

Complexification and continuous functional calculus compare the Dirichlet
pairings of a symmetric Markov operator and its powers.
-/

open scoped InnerProductSpace NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel.ComplexSequenceSpace

/-- Complex inner products decompose into four real pairings. -/
theorem inner_decomposition {V : Type*} (z w : ComplexL2 V) :
    ⟪z, w⟫_ℂ =
      (⟪realPart V z, realPart V w⟫_ℝ + ⟪imagPart V z, imagPart V w⟫_ℝ : ℂ) +
        Complex.I * (⟪realPart V z, imagPart V w⟫_ℝ -
          ⟪imagPart V z, realPart V w⟫_ℝ : ℂ) := by
  nth_rw 1 [← reconstruction V z]
  nth_rw 1 [← reconstruction V w]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    ofReal_inner]
  apply Complex.ext <;> (simp [Complex.mul_re, Complex.mul_im]; all_goals ring)

/-- Complexification preserves self-adjointness. -/
theorem complexify_isSelfAdjoint {V : Type*} (T : ValueSpace V →L[ℝ] ValueSpace V)
    (hT : IsSelfAdjoint T) : IsSelfAdjoint (complexify T) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro z w
  change ⟪complexify T z, w⟫_ℂ = ⟪z, complexify T w⟫_ℂ
  rw [inner_decomposition, inner_decomposition]
  simp only [realPart_complexify, imagPart_complexify]
  have hs (f g : ValueSpace V) : ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) f g
  rw [hs (realPart V z) (realPart V w), hs (imagPart V z) (imagPart V w),
    hs (realPart V z) (imagPart V w), hs (imagPart V z) (realPart V w)]

/-- Powers of the complexification agree with powers on embedded real vectors. -/
theorem complexify_pow_ofReal {V : Type*} (T : ValueSpace V →L[ℝ] ValueSpace V)
    (n : ℕ) (f : ValueSpace V) :
    (complexify T ^ n) (ofReal V f) = ofReal V ((T ^ n) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp,
        mul_apply_eq_comp, ih, complexify_ofReal]

end LatticeProb.Graph.LongRangeKernel.ComplexSequenceSpace

namespace LatticeProb.Graph.LongRangeKernel

open ComplexSequenceSpace

/-- The spectral defect inequality for a self-adjoint contraction on real sequences. -/
theorem inner_one_sub_pow_le {V : Type*} (T : ValueSpace V →L[ℝ] ValueSpace V)
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) (n : ℕ) (f : ValueSpace V) :
    ⟪f - (T ^ n) f, f⟫_ℝ ≤ (n : ℝ) * ⟪f - T f, f⟫_ℝ := by
  let S := complexify T
  have hs : IsSelfAdjoint S := complexify_isSelfAdjoint T hT
  have hsnorm : ‖S‖ ≤ 1 := by simpa only [S, complexify_norm] using hnorm
  have hc := one_sub_pow_le_nat_smul_one_sub S hs hsnorm n
  have hp := (ContinuousLinearMap.le_def.mp hc).re_inner_nonneg_left (ofReal V f)
  have hpow : (S ^ n) (ofReal V f) = ofReal V ((T ^ n) f) :=
    complexify_pow_ofReal T n f
  have happly : S (ofReal V f) = ofReal V (T f) := complexify_ofReal T f
  change 0 ≤ (⟪(n : ℝ) • (ofReal V f - S (ofReal V f)) -
    (ofReal V f - (S ^ n) (ofReal V f)), ofReal V f⟫_ℂ).re at hp
  rw [hpow, happly] at hp
  have hemb : (n : ℝ) • (ofReal V f - ofReal V (T f)) =
      ofReal V ((n : ℝ) • (f - T f)) := by
    rw [map_smul, map_sub]
  rw [hemb] at hp
  simp only [inner_sub_left, ofReal_inner, Complex.sub_re, Complex.ofReal_re,
    inner_smul_left, RCLike.conj_to_real] at hp ⊢
  linarith

/-- The Dirichlet pairing of a symmetric Markov power is bounded by its time. -/
theorem markovOperatorCLM_pow_energy_le {V : Type*} (k : V → V → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (n : ℕ) (f : lp (fun _ : V => ℝ) 2) :
    ⟪f - (markovOperatorCLM k hk hsym ^ n) f, f⟫_ℝ ≤
      (n : ℝ) * realKernelEnergy k f := by
  rw [realKernelEnergy_eq_inner k hk hsym f]
  apply inner_one_sub_pow_le _ (markovOperatorCLM_isSelfAdjoint k hk hsym) _ n f
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  change ‖markovOperator k hk hsym g‖ ≤ 1 * ‖g‖
  simpa only [one_mul] using norm_markovOperator_le k hk hsym g

end LatticeProb.Graph.LongRangeKernel
