import LongRange.HeatKernel.CriticalOperatorL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Markov operators on counting-space Hilbert space

A symmetric Markov kernel defines a contraction on real square-summable functions.
-/

open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

private theorem lp_square_summable {X : Type*} (f : lp (fun _ : X => ℝ) 2) :
    (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞ := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp f)
  have hs : Summable (fun x => f x ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h
  exact hs.tsum_ofReal_lt_top

/-- The Markov operator on real counting-space square-summable functions. -/
noncomputable def markovOperator {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) :
    lp (fun _ : X => ℝ) 2 →ₗ[ℝ] lp (fun _ : X => ℝ) 2 where
  toFun f := ⟨fun x => ∑' y, (k x y).toReal * f y, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have h := ENNReal.summable_toReal (kernel_apply_square_summable k hk hsym f
      (lp_square_summable f)).ne
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using h⟩
  map_add' f g := by
    apply lp.ext
    funext x
    change (∑' y, (k x y).toReal * (f y + g y)) =
      (∑' y, (k x y).toReal * f y) + ∑' y, (k x y).toReal * g y
    simp_rw [mul_add]
    exact Summable.tsum_add (summable_kernel_apply_row k hk hsym f (lp_square_summable f) x)
      (summable_kernel_apply_row k hk hsym g (lp_square_summable g) x)
  map_smul' c f := by
    apply lp.ext
    funext x
    change (∑' y, (k x y).toReal * (c * f y)) = c * ∑' y, (k x y).toReal * f y
    simp_rw [show ∀ y, (k x y).toReal * (c * f y) = c * ((k x y).toReal * f y) by
      intro y; ring]
    exact tsum_mul_left

private theorem lp_norm_sq {X : Type*} (f : lp (fun _ : X => ℝ) 2) :
    ‖f‖ ^ 2 = ∑' x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq f, lp.inner_eq_tsum]
  simp only [Real.inner_apply, sq]

/-- The Markov operator is a contraction in the Hilbert norm. -/
theorem norm_markovOperator_le {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : lp (fun _ : X => ℝ) 2) : ‖markovOperator k hk hsym f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [lp_norm_sq, lp_norm_sq]
  exact kernel_apply_sq_tsum_le k hk hsym f (lp_square_summable f)

/-- The continuous Markov operator on real counting-space square-summable functions. -/
noncomputable def markovOperatorCLM {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) :
    lp (fun _ : X => ℝ) 2 →L[ℝ] lp (fun _ : X => ℝ) 2 :=
  (markovOperator k hk hsym).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using norm_markovOperator_le k hk hsym f)

private theorem summable_kernel_mixed {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f g : lp (fun _ : X => ℝ) 2) :
    Summable (fun p : X × X => (k p.1 p.2).toReal * (g p.1 * f p.2)) := by
  have hs := (summable_kernel_square_left k hk g (lp_square_summable g)).add
    (summable_kernel_square_right k hk hsym f (lp_square_summable f))
  apply Summable.of_norm_bounded hs
  intro ⟨x, y⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_mul]
  have h : 2 * (|g x| * |f y|) ≤ g x ^ 2 + f y ^ 2 := by
    nlinarith [sq_nonneg (|g x| - |f y|), sq_abs (g x), sq_abs (f y)]
  have hk0 : 0 ≤ (k x y).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr h)]

/-- A symmetric kernel defines a symmetric Hilbert-space operator. -/
theorem markovOperatorCLM_inner_symm {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f g : lp (fun _ : X => ℝ) 2) :
    inner ℝ (markovOperatorCLM k hk hsym f) g = inner ℝ f (markovOperatorCLM k hk hsym g) := by
  have hfg := summable_kernel_mixed k hk hsym f g
  have hgf := summable_kernel_mixed k hk hsym g f
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [Real.inner_apply]
  calc
    _ = ∑' x, ∑' y, (k x y).toReal * (g x * f y) := by
      apply tsum_congr
      intro x
      change (∑' y, (k x y).toReal * f y) * g x = _
      rw [← tsum_mul_right]
      apply tsum_congr
      intro y
      ring
    _ = ∑' p : X × X, (k p.1 p.2).toReal * (g p.1 * f p.2) := hfg.tsum_prod.symm
    _ = ∑' p : X × X, (k p.1 p.2).toReal * (f p.1 * g p.2) := by
      rw [← (Equiv.prodComm X X).tsum_eq (fun p : X × X =>
        (k p.1 p.2).toReal * (f p.1 * g p.2))]
      apply tsum_congr
      intro ⟨x, y⟩
      simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
      rw [hsym]
      ring
    _ = ∑' x, ∑' y, (k x y).toReal * (f x * g y) := hgf.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro x
      change _ = f x * ∑' y, (k x y).toReal * g y
      rw [← tsum_mul_left]
      apply tsum_congr
      intro y
      ring

/-- The Dirichlet energy is the Hilbert pairing with the Markov defect. -/
theorem realKernelEnergy_eq_inner {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x)
    (f : lp (fun _ : X => ℝ) 2) :
    realKernelEnergy k f = inner ℝ (f - markovOperatorCLM k hk hsym f) f := by
  rw [(realKernelEnergy_eq_operator_pairing k hk hsym f (lp_square_summable f)).2,
    lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  change f x * (f x - ∑' y, (k x y).toReal * f y) =
    inner ℝ (f x - ∑' y, (k x y).toReal * f y) (f x)
  rw [Real.inner_apply, mul_comm]

/-- A symmetric Markov kernel gives a self-adjoint operator. -/
theorem markovOperatorCLM_isSelfAdjoint {X : Type*} (k : X → X → ℝ≥0∞)
    (hk : ∀ x, ∑' y, k x y = 1) (hsym : ∀ x y, k x y = k y x) :
    IsSelfAdjoint (markovOperatorCLM k hk hsym) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  exact markovOperatorCLM_inner_symm k hk hsym f g

end LatticeProb.Graph.LongRangeKernel
