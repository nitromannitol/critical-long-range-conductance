import LongRange.Support.Analysis.Davies.Killed
import LongRange.Support.Analysis.Semigroup.DirichletForm
import LongRange.Support.Prob.JumpChain.KilledGenerator

/-!
# Energy of a killed jump form

The zero extension of a function on a finite set has the same energy as the
finite killed form, transferring the full-space Nash inequality to that form.
-/

namespace LatticeProb.Davies

open External

noncomputable section

attribute [local instance] Classical.propDecidable

variable {S : Type*} (rates : JumpChain.BoundedRates S)

/-- Extend a function on a finite set by zero. -/
def extend (U : Finset S) (g : U → ℝ) (x : S) : ℝ :=
  if h : x ∈ U then g ⟨x, h⟩ else 0

@[simp] theorem extend_apply (U : Finset S) (g : U → ℝ) (x : U) :
    extend U g x = g x := by
  simp [extend, x.property]

@[simp] theorem extend_apply_of_not_mem (U : Finset S) (g : U → ℝ) {x : S}
    (hx : x ∉ U) : extend U g x = 0 := by
  simp [extend, hx]

private theorem extend_sq_summable (U : Finset S) (g : U → ℝ) :
    Summable (fun x ↦ (extend U g x) ^ 2) := by
  apply summable_of_ne_finset_zero (s := U)
  intro x hx
  simp [extend_apply_of_not_mem U g hx]

private theorem extend_abs_summable (U : Finset S) (g : U → ℝ) :
    Summable (fun x ↦ |extend U g x|) := by
  apply summable_of_ne_finset_zero (s := U)
  intro x hx
  simp [extend_apply_of_not_mem U g hx]

private theorem extend_sum (U : Finset S) (g : U → ℝ) (F : ℝ → ℝ) (hF : F 0 = 0) :
    (∑' x, F (extend U g x)) = ∑ x : U, F (g x) := by
  calc
    (∑' x, F (extend U g x)) = ∑ x ∈ U, F (extend U g x) := by
      apply tsum_eq_sum
      intro x hx
      simp [extend_apply_of_not_mem U g hx, hF]
    _ = ∑ x : U, F (extend U g x) := (Finset.sum_coe_sort U _).symm
    _ = ∑ x : U, F (g x) := by simp only [extend_apply]

/-- The full-space energy of the zero extension equals the finite killed energy. -/
theorem ckkwEnergy_extend (hs : ∀ i j, rates.q i j = rates.q j i)
    (U : Finset S) (g : U → ℝ) :
    ckkwEnergy rates (extend U g) = (killedForm rates hs U).form g g := by
  classical
  let f := extend U g
  have hf : Summable (fun x ↦ f x ^ 2) := extend_sq_summable U g
  have hgen (x : S) : rates.generator f x = rates.killedGen (U : Set S) f x := by
    have hqf := rates.summable_q_mul x f (LatticeProb.abs_le_sqrt_tsum_sq hf)
    rw [JumpChain.BoundedRates.generator, JumpChain.BoundedRates.killedGen]
    simp only [mul_sub]
    rw [hqf.tsum_sub ((rates.summable x).mul_right (f x)), tsum_mul_right]
    congr 1
    apply tsum_congr
    intro y
    by_cases hy : y ∈ U
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, show f y = 0 from extend_apply_of_not_mem U g hy]
  have hgreen := rates.tsum_mul_generator_self hs hf
  have hfinite : (∑' x, f x * rates.generator f x) =
      ∑ x ∈ U, f x * rates.killedGen (U : Set S) f x := by
    rw [tsum_eq_sum (s := U)]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [hgen]
    · intro x hx
      simp [show f x = 0 from extend_apply_of_not_mem U g hx]
  rw [hfinite] at hgreen
  have hedge : (∑ x ∈ U, ∑ y ∈ U, rates.q x y * (f y - f x) ^ 2) =
      ∑ x : U, ∑ y : U, rates.q x y * (g y - g x) * (g y - g x) := by
    rw [← Finset.sum_coe_sort U (fun x ↦ ∑ y ∈ U, rates.q x y * (f y - f x) ^ 2)]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_coe_sort U (fun y ↦ rates.q x y * (f y - f x) ^ 2)]
    apply Finset.sum_congr rfl
    intro y _
    change rates.q x y * (extend U g y - extend U g x) ^ 2 = _
    rw [extend_apply, extend_apply]
    ring
  have hkill : (∑ x ∈ U, ((∑' y, rates.q x y) - ∑ y ∈ U, rates.q x y) * f x ^ 2) =
      ∑ x : U, ((∑' y, rates.q x y) - ∑ y : U, rates.q x y) * g x * g x := by
    rw [← Finset.sum_coe_sort U (fun x ↦
      ((∑' y, rates.q x y) - ∑ y ∈ U, rates.q x y) * f x ^ 2)]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_coe_sort U (fun y ↦ rates.q x y)]
    change _ * (extend U g x) ^ 2 = _
    rw [extend_apply]
    ring
  have hform' : (∑ x ∈ U, (-rates.killedGen (U : Set S) f x) * f x) =
      (killedForm rates hs U).form g g := by
    have h := rates.sum_neg_killedGen_mul hs (U : Set S) U.finite_toSet f
    rw [Finset.finite_toSet_toFinset] at h
    rw [h]
    change (∑ x ∈ U, ∑ y ∈ U, rates.q x y * (f y - f x) ^ 2) / 2 +
      (∑ x ∈ U, ((∑' y, rates.q x y) - ∑ y ∈ U, rates.q x y) * f x ^ 2) = _
    rw [hedge, hkill]
    rfl
  have hneg : (∑ x ∈ U, (-rates.killedGen (U : Set S) f x) * f x) =
      -(∑ x ∈ U, f x * rates.killedGen (U : Set S) f x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hneg, hgreen, neg_neg] at hform'
  exact hform'

/-- A full-space Nash inequality transfers to each finite killed form. -/
theorem killedForm_nash (hs : ∀ i j, rates.q i j = rates.q j i)
    (U : Finset S) (θ : ℝ → ℝ) (δ : ℝ) (h : ckkwNashInequality rates θ δ) :
    (killedForm rates hs U).Nash θ δ := by
  intro g h₁ h₂
  have hsum₁ := extend_sum U g (fun x ↦ |x|) (by simp)
  have hsum₂ := extend_sum U g (fun x ↦ x ^ 2) (by simp)
  have h' := h (extend U g) (extend_sq_summable U g) (extend_abs_summable U g)
    (by simpa only [hsum₁] using h₁)
    (by simpa only [ckkwNormSq, hsum₂] using h₂)
  simpa only [ckkwNormSq, hsum₂, ckkwEnergy_extend rates hs U g] using h'

end
end LatticeProb.Davies
