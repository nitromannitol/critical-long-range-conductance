import LongRange.Calculus.BilinForm
import LongRange.Model.CorrectorEnergy
import LongRange.Corrector.Support

/-!
# Convergence of the diagonal corrector energy

The stage bilinear summability theorem gives absolute convergence of the diagonal energy.
The critical seminorm series is supplied by the same stage module.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

variable {d : ℕ}

/-- The diagonal conductance-weighted energy series converges on finite supports. -/
theorem summable_bilinForm_self {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {φ : Site d → ℝ}
    (hφ : φ.HasFiniteSupport) :
    Summable (fun q : Site d × Site d => if hw : q.2 = 0 then 0 else
      a (edgeAdd q.1 q.2 hw) * jumpKernel (physical ε q.2) *
        (φ (q.1 + q.2) - φ q.1) * (φ (q.1 + q.2) - φ q.1)) :=
  summable_bilinForm hd hε hlam ha hφ hφ

/-- Adding a bounded finite variation to the affine argument splits the bilinear form. -/
theorem bilinForm_affine_add (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {u v : Site d → ℝ} (hu : u.HasFiniteSupport) (hv : v.HasFiniteSupport) :
    bilinForm ε a (fun q => linearFn ε p q + u q) v =
      bilinForm ε a (linearFn ε p) v + bilinForm ε a u v := by
  have hs := summable_bilinForm_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ hv
  simp only [add_zero] at hs
  have ht := summable_bilinForm hd hε hlam ha hu hv
  unfold bilinForm
  rw [← mul_add, ← Summable.tsum_add hs ht]
  congr 1
  apply tsum_congr
  intro q
  by_cases hz : q.2 = 0 <;> simp only [hz, ↓reduceDIte] <;> ring

/-- The affine cross term is additive on finite variations. -/
theorem bilinForm_linear_add_right (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {u v : Site d → ℝ} (hu : u.HasFiniteSupport) (hv : v.HasFiniteSupport) :
    bilinForm ε a (linearFn ε p) (u + v) =
      bilinForm ε a (linearFn ε p) u + bilinForm ε a (linearFn ε p) v := by
  have hs := summable_bilinForm_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ hu
  have ht := summable_bilinForm_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ hv
  simp only [add_zero] at hs ht
  unfold bilinForm
  rw [← mul_add, ← Summable.tsum_add hs ht]
  congr 1
  apply tsum_congr
  intro q
  by_cases hz : q.2 = 0 <;> simp only [hz, ↓reduceDIte, Pi.add_apply] <;> ring

open Classical in
/-- The subtracted-square series in the corrector functional is absolutely summable on
admissible functions, by the quadratic and affine cross-term majorants. -/
theorem summable_correctorFunctional (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {u : Site d → ℝ} (hu : SupportedIn ε U u) :
    Summable (fun q : Site d × Site d => if hz : q.2 = 0 then 0 else
      if q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U then
        a (edgeAdd q.1 q.2 hz) * jumpKernel (physical ε q.2) *
          ((linearFn ε p q.2 + u (q.1 + q.2) - u q.1) ^ 2 - linearFn ε p q.2 ^ 2)
      else 0) := by
  classical
  have hf := hu.hasFiniteSupport hε hU
  have hs := summable_bilinForm hd hε hlam ha hf hf
  have ht := summable_bilinForm_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ hf
  simp only [add_zero] at ht
  apply (hs.add (ht.mul_left 2)).congr
  intro q
  by_cases hz : q.2 = 0
  · simp only [hz, ↓reduceDIte, mul_zero, add_zero]
  · simp only [hz, ↓reduceDIte, linearFn_add]
    by_cases hq : q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U
    · rw [if_pos hq]
      ring
    · rw [if_neg hq, hu q.1 (not_or.mp hq).1,
        hu (q.1 + q.2) (not_or.mp hq).2]
      ring

/-- On admissible functions the subtracted-square functional is its convergent quadratic
energy plus twice the affine cross term. No separate affine-square sum is taken. -/
theorem correctorFunctional_eq_quadratic (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {u : Site d → ℝ} (hu : SupportedIn ε U u) :
    correctorFunctional ε U a p u =
      bilinForm ε a u u + 2 * bilinForm ε a (linearFn ε p) u := by
  classical
  have huf := hu.hasFiniteSupport hε hU
  have hs := summable_bilinForm hd hε hlam ha huf huf
  have ht := summable_bilinForm_affine hd hε hlam ha p
    (φ := fun _ => 0) ⟨0, le_rfl, fun _ => by simp⟩ huf
  simp only [add_zero] at ht
  unfold correctorFunctional bilinForm
  rw [show (ε ^ (2 * d) / (2 * kappa d ε) * ∑' q : Site d × Site d,
      (if hw : q.2 = 0 then 0 else a (edgeAdd q.1 q.2 hw) *
        jumpKernel (physical ε q.2) * (u (q.1 + q.2) - u q.1) *
          (u (q.1 + q.2) - u q.1))) +
      2 * (ε ^ (2 * d) / (2 * kappa d ε) * ∑' q : Site d × Site d,
      (if hw : q.2 = 0 then 0 else a (edgeAdd q.1 q.2 hw) *
        jumpKernel (physical ε q.2) *
          (linearFn ε p (q.1 + q.2) - linearFn ε p q.1) *
            (u (q.1 + q.2) - u q.1))) =
      ε ^ (2 * d) / (2 * kappa d ε) *
        ((∑' q : Site d × Site d, if hw : q.2 = 0 then 0 else
          a (edgeAdd q.1 q.2 hw) * jumpKernel (physical ε q.2) *
            (u (q.1 + q.2) - u q.1) * (u (q.1 + q.2) - u q.1)) +
        2 * (∑' q : Site d × Site d, if hw : q.2 = 0 then 0 else
          a (edgeAdd q.1 q.2 hw) * jumpKernel (physical ε q.2) *
            (linearFn ε p (q.1 + q.2) - linearFn ε p q.1) *
              (u (q.1 + q.2) - u q.1))) by ring]
  rw [← ht.tsum_mul_left 2, ← Summable.tsum_add hs (ht.mul_left 2)]
  congr 1
  apply tsum_congr
  intro q
  by_cases hz : q.2 = 0
  · simp only [hz, ↓reduceDIte, mul_zero, add_zero]
  · simp only [hz, ↓reduceDIte, linearFn_add]
    by_cases hq : q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U
    · rw [if_pos hq]
      ring
    · rw [if_neg hq, hu q.1 (not_or.mp hq).1,
        hu (q.1 + q.2) (not_or.mp hq).2]
      ring

end LongRange
