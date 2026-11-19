import Mathlib

/-!
# Finite symmetric jump forms

Finite jump forms with killing, their semigroups, and the quantities used in Davies' method.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies

noncomputable section

/-- A symmetric nonnegative jump kernel and a nonnegative killing rate on a finite set. -/
structure FiniteJumpForm (ι : Type*) [Fintype ι] where
  q : ι → ι → ℝ
  κ : ι → ℝ
  q_nonneg : ∀ i j, 0 ≤ q i j
  q_symm : ∀ i j, q i j = q j i
  κ_nonneg : ∀ i, 0 ≤ κ i

namespace FiniteJumpForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The generator of the killed chain. -/
def gen : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ F.q i j - if i = j then (∑ k, F.q i k) + F.κ i else 0

/-- The bilinear form associated with the killed generator. -/
def form (u v : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, F.q i j * (u j - u i) * (v j - v i)) / 2 +
    ∑ i, F.κ i * u i * v i

/-- The matrix exponential semigroup of the killed generator. -/
def semigroup (t : ℝ) : Matrix ι ι ℝ := NormedSpace.exp (t • F.gen)

/-- The semigroup conjugated by the exponential of a real-valued weight. -/
def twist (ψ f : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  Real.exp (ψ i) * (F.semigroup t *ᵥ fun j ↦ Real.exp (-ψ j) * f j) i

/-- A common upper bound for the two jump carré du champ expressions. -/
def LambdaBound (ψ : ι → ℝ) (Λsq : ℝ) : Prop :=
  0 ≤ Λsq ∧
    (∀ i, ∑ j, F.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2 ≤ Λsq) ∧
    (∀ i, ∑ j, F.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2 / 2 ≤ Λsq)

/-- The finite-set Nash inequality for the form. -/
def Nash (θ : ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ g : ι → ℝ, (∑ i, |g i|) ≤ 1 → 0 < ∑ i, (g i) ^ 2 →
    θ (∑ i, (g i) ^ 2) ≤ F.form g g + δ * ∑ i, (g i) ^ 2

/-- The finite sum of a natural power of a real-valued function. -/
def powSum (f : ι → ℝ) (p : ℕ) : ℝ := ∑ i, (f i) ^ p

/-- The generator is the negative of the bilinear jump form under counting measure. -/
theorem sum_mul_gen_mulVec (u v : ι → ℝ) :
    (∑ i, u i * (F.gen *ᵥ v) i) = -F.form u v := by
  have hswap₁ : (∑ i, ∑ j, F.q i j * u j * v j) =
      ∑ i, ∑ j, F.q i j * u i * v i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [F.q_symm]
  have hswap₂ : (∑ i, ∑ j, F.q i j * u j * v i) =
      ∑ i, ∑ j, F.q i j * u i * v j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [F.q_symm]
  have hrow (i : ι) : (F.gen *ᵥ v) i =
      (∑ j, F.q i j * v j) - ((∑ j, F.q i j) + F.κ i) * v i := by
    simp only [Matrix.mulVec, dotProduct, gen, Matrix.of_apply, sub_mul,
      Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  simp_rw [hrow]
  unfold form
  simp_rw [show ∀ i j, F.q i j * (u j - u i) * (v j - v i) =
    F.q i j * u j * v j - F.q i j * u j * v i -
      F.q i j * u i * v j + F.q i j * u i * v i by intros; ring]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hswap₁, hswap₂]
  have hx : (∑ i, u i * (((∑ j, F.q i j) + F.κ i) * v i)) =
      (∑ i, ∑ j, F.q i j * u i * v i) + ∑ i, F.κ i * u i * v i := by
    simp only [add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have hy : (∑ i, u i * ∑ j, F.q i j * v j) =
      ∑ i, ∑ j, F.q i j * u i * v j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hx, hy]
  ring

omit [DecidableEq ι] in
/-- A symmetric jump form with nonnegative killing is nonnegative on the diagonal. -/
theorem form_self_nonneg (u : ι → ℝ) : 0 ≤ F.form u u := by
  unfold form
  apply add_nonneg
  · apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (F.q_nonneg i j) (sq_nonneg (u j - u i)) |>.trans_eq (by ring)
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (F.κ_nonneg i) (sq_nonneg (u i)) |>.trans_eq (by ring)

omit [DecidableEq ι] in
/-- Simultaneously scaling both arguments scales the form quadratically. -/
theorem form_smul_smul (c : ℝ) (u v : ι → ℝ) :
    F.form (c • u) (c • v) = c ^ 2 * F.form u v := by
  unfold form
  simp only [Pi.smul_apply, smul_eq_mul]
  have h₁ : (∑ i, ∑ j, F.q i j * (c * u j - c * u i) * (c * v j - c * v i)) =
      c ^ 2 * ∑ i, ∑ j, F.q i j * (u j - u i) * (v j - v i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : (∑ i, F.κ i * (c * u i) * (c * v i)) =
      c ^ 2 * ∑ i, F.κ i * u i * v i := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h₁, h₂]
  ring

omit [DecidableEq ι] in
/-- Reversing both arguments leaves the form unchanged. -/
theorem form_neg (u v : ι → ℝ) : F.form (-u) (-v) = F.form u v := by
  simpa using F.form_smul_smul (-1) u v

/-- The finite matrix semigroup differentiates by its generator. -/
theorem hasDerivAt_semigroup_mulVec (w : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ F.semigroup u *ᵥ w)
      (F.gen *ᵥ (F.semigroup t *ᵥ w)) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) F.gen t
  have hl : HasDerivAt (fun u : ℝ ↦ (Matrix.mulVecLin (NormedSpace.exp (u • F.gen))) w)
      ((Matrix.mulVecLin (F.gen * NormedSpace.exp (t • F.gen))) w) t := by
    let ev : Matrix ι ι ℝ →L[ℝ] (ι → ℝ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun B ↦ B *ᵥ w
          map_add' := fun _ _ ↦ Matrix.add_mulVec _ _ _
          map_smul' := fun _ _ ↦ Matrix.smul_mulVec _ _ _ }
    exact ev.hasFDerivAt.comp_hasDerivAt t h
  simpa [semigroup, Matrix.mulVec_mulVec] using hl

/-- The finite semigroup obeys the addition law at all real times. -/
theorem semigroup_add (s t : ℝ) : F.semigroup (s + t) = F.semigroup s * F.semigroup t := by
  unfold semigroup
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl F.gen).smul_left s).smul_right t)

/-- The generator of a symmetric jump form is symmetric. -/
theorem gen_transpose : F.genᵀ = F.gen := by
  ext i j
  simp only [Matrix.transpose_apply, gen, Matrix.of_apply]
  rw [F.q_symm j i]
  by_cases h : i = j
  · subst j
    rfl
  · simp [h, Ne.symm h]

/-- The finite semigroup of a symmetric jump form is symmetric. -/
theorem semigroup_transpose (t : ℝ) : (F.semigroup t)ᵀ = F.semigroup t := by
  unfold semigroup
  rw [← Matrix.exp_transpose, Matrix.transpose_smul, F.gen_transpose]

/-- The matrix semigroup at negative time is the inverse at positive time. -/
theorem semigroup_mul_neg (t : ℝ) : F.semigroup t * F.semigroup (-t) = 1 := by
  rw [← F.semigroup_add, add_neg_cancel]
  simp [semigroup, NormedSpace.exp_zero]

end FiniteJumpForm
end
end LatticeProb.Davies
