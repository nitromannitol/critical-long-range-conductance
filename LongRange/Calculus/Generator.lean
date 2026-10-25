import LongRange.Calculus.Summability

/-!
# The discrete product rule

Finite support of the second factor makes the coefficient-variation series finitely supported.
Absolute convergence of the generator then permits splitting its series term by term.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The coefficient-variation series is summable because its translated second factor has
finite support. No regularity of the first factor is needed for this assertion. -/
theorem summable_generator_product_correction (ε : ℝ) (a : Edge d → ℝ)
    (b : Site d → ℝ) {φ : Site d → ℝ} (hφ : Function.HasFiniteSupport φ) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * jumpKernel (physical ε w) * (b (q + w) - b q) * φ (q + w)) := by
  have hs : Function.HasFiniteSupport (fun w => φ (q + w)) :=
    hφ.fun_comp_of_injective (add_right_injective q)
  apply summable_of_hasFiniteSupport
  apply hs.subset
  intro w hw
  change φ (q + w) ≠ 0
  intro hz
  apply hw
  by_cases hw : w = 0 <;> simp only [hw, ↓reduceDIte, hz, mul_zero]

/-- The exact discrete product rule for a finitely supported second factor. -/
theorem generator_mul (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (b : Site d → ℝ) {φ : Site d → ℝ} (hφ : Function.HasFiniteSupport φ) (q : Site d) :
    generator ε a (fun x => b x * φ x) q = b q * generator ε a φ q +
      ε ^ d / kappa d ε * ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * jumpKernel (physical ε w) *
          (b (q + w) - b q) * φ (q + w) := by
  have hs := summable_generator_bounded hd hε hlam ha
    (exists_bound_of_finite_support hφ) q
  have hc := summable_generator_product_correction ε a b hφ q
  unfold generator
  rw [show (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (b (q + w) * φ (q + w) - b q * φ q) *
        jumpKernel (physical ε w)) =
      (fun w : Site d => b q * (if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (φ (q + w) - φ q) * jumpKernel (physical ε w)) +
        (if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * jumpKernel (physical ε w) *
          (b (q + w) - b q) * φ (q + w))) by
    funext w
    by_cases hw : w = 0 <;> simp only [hw, ↓reduceDIte] <;> ring]
  rw [Summable.tsum_add (hs.mul_left (b q)) hc, tsum_mul_left]
  ring

end

end LongRange
