import LongRange.Calculus.Summability
import LongRange.Model.Corrector
import LongRange.Corrector.Support

/-!
# Linearity of the rescaled generator

Summable increment series give additivity and finite superposition. Scalar multiplication
commutes with the generator without a summability assumption, and the corrector equation
therefore identifies the generator of the corrector with the negative linear forcing.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The generator preserves addition when both increment series are summable. -/
theorem generator_add (ε : ℝ) (a : Edge d → ℝ) {g h : Site d → ℝ} (q : Site d)
    (hg : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (g (q + w) - g q) * jumpKernel (physical ε w)))
    (hh : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w))) :
    generator ε a (fun x => g x + h x) q = generator ε a g q + generator ε a h q := by
  unfold generator
  rw [← mul_add, ← hg.tsum_add hh]
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte, add_zero]
  · simp only [hw, ↓reduceDIte]
    ring

/-- The generator preserves subtraction when both increment series are summable. -/
theorem generator_sub (ε : ℝ) (a : Edge d → ℝ) {g h : Site d → ℝ} (q : Site d)
    (hg : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (g (q + w) - g q) * jumpKernel (physical ε w)))
    (hh : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w))) :
    generator ε a (fun x => g x - h x) q = generator ε a g q - generator ε a h q := by
  unfold generator
  rw [← mul_sub, ← hg.tsum_sub hh]
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte, sub_zero]
  · simp only [hw, ↓reduceDIte]
    ring

/-- Scalar multiplication commutes with the generator, even for nonsummable data. -/
theorem generator_const_mul (ε : ℝ) (a : Edge d → ℝ) (c : ℝ)
    (h : Site d → ℝ) (q : Site d) :
    generator ε a (fun x => c * h x) q = c * generator ε a h q := by
  unfold generator
  have heq : (∑' w : Site d, if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (c * h (q + w) - c * h q) * jumpKernel (physical ε w)) =
      c * ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hw : w = 0
    · simp only [hw, ↓reduceDIte, mul_zero]
    · simp only [hw, ↓reduceDIte]
      ring
  rw [heq]
  ring

/-- The generator preserves a finite sum of functions with summable increment series. -/
theorem generator_finset_sum (ε : ℝ) (a : Edge d → ℝ) {ι : Type*}
    (s : Finset ι) (h : ι → Site d → ℝ) (q : Site d)
    (hs : ∀ i ∈ s, Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h i (q + w) - h i q) * jumpKernel (physical ε w))) :
    generator ε a (fun x => ∑ i ∈ s, h i x) q = ∑ i ∈ s, generator ε a (h i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [generator]
  | @insert i s hi ih =>
    have htail := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hsum : Summable (fun w : Site d => if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * ((∑ j ∈ s, h j (q + w)) - ∑ j ∈ s, h j q) *
          jumpKernel (physical ε w)) := by
      refine (summable_sum htail).congr (fun w => ?_)
      by_cases hw : w = 0
      · simp only [hw, ↓reduceDIte, Finset.sum_const_zero]
      · simp only [hw, ↓reduceDIte]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    have hadd := generator_add ε a (g := h i) (h := fun x => ∑ j ∈ s, h j x) q
      (hs i (Finset.mem_insert_self i s)) hsum
    simp only [Finset.sum_insert hi]
    exact hadd.trans (congrArg (fun t => generator ε a (h i) q + t) (ih htail))

/-- A coordinate slope has physical increment `ε * w i` in the generator series. -/
theorem generator_linearFn_single (ε : ℝ) (a : Edge d → ℝ) (i : Fin d) (q : Site d) :
    generator ε a (linearFn ε (Pi.single i 1)) q =
      ε ^ d / kappa d ε * ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (ε * (w i : ℝ)) * jumpKernel (physical ε w) := by
  unfold generator
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte]
  · simp only [hw, ↓reduceDIte, linearFn_add, add_sub_cancel_left]
    have hcoord : linearFn ε (Pi.single i 1) w = ε * (w i : ℝ) := by
      simp [linearFn, Pi.single_apply, physical, ite_mul]
    rw [hcoord]

/-- In a bounded domain the corrector generator equals the negative linear forcing. -/
theorem IsCorrectorSolution.generator_eq_neg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {p : Fin d → ℝ} {φ : Site d → ℝ} (h : IsCorrectorSolution ε U a p φ)
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    generator ε a φ q = -generator ε a (linearFn ε p) q := by
  have hlin := summable_generator_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, by intro q; simp only [abs_zero, le_refl]⟩ q
  simp only [add_zero] at hlin
  have hφ := summable_generator_bounded hd hε hlam ha
    (exists_bound_of_finite_support (h.1.hasFiniteSupport hε hU)) q
  have heq := h.2 q hq
  rw [generator_add ε a q hlin hφ] at heq
  exact eq_neg_of_add_eq_zero_right heq

end

end LongRange
