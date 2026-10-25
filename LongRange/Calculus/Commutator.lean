import LongRange.Calculus.BilinForm

/-!
# The coefficient-variation identity

Green's identity and the discrete product rule identify the commutator of multiplication
with the bilinear energy. The sign agrees with the definition of the source's error term.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The coefficient-variation identity has a positive right-hand side and no extra factor.
Finite supports of `φ` and `ψ` suffice, without bounds on `b` or its increments. -/
theorem bilinForm_mul_sub_mul (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (b : Site d → ℝ)
    {φ ψ : Site d → ℝ} (hφ : Function.HasFiniteSupport φ)
    (hψ : Function.HasFiniteSupport ψ) :
    bilinForm ε a φ (fun q => b q * ψ q) -
      bilinForm ε a (fun q => b q * φ q) ψ =
      ε ^ d * ∑' q : Site d, ψ q * (ε ^ d / kappa d ε *
        ∑' w : Site d, if hw : w = 0 then 0 else
          a (edgeAdd q w hw) * jumpKernel (physical ε w) *
            (b (q + w) - b q) * φ (q + w)) := by
  have hbφ : Function.HasFiniteSupport (fun q => b q * φ q) :=
    Function.HasFiniteSupport.mul_right b hφ
  have hbψ : Function.HasFiniteSupport (fun q => b q * ψ q) :=
    Function.HasFiniteSupport.mul_right b hψ
  rw [bilinForm_eq_neg_generator_bounded hd hε hlam ha
      (exists_bound_of_finite_support hφ) hbψ,
    bilinForm_eq_neg_generator_bounded hd hε hlam ha
      (exists_bound_of_finite_support hbφ) hψ]
  let correction : Site d → ℝ := fun q => ε ^ d / kappa d ε *
    ∑' w : Site d, if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * jumpKernel (physical ε w) *
        (b (q + w) - b q) * φ (q + w)
  have hs : Summable (fun q => b q * ψ q * generator ε a φ q) :=
    summable_of_hasFiniteSupport (hbψ.mul_left (generator ε a φ))
  have hc : Summable (fun q => ψ q * correction q) :=
    summable_of_hasFiniteSupport (hψ.mul_left correction)
  have hsum : (∑' q : Site d, ψ q * generator ε a (fun x => b x * φ x) q) =
      (∑' q : Site d, b q * ψ q * generator ε a φ q) +
        ∑' q : Site d, ψ q * correction q := by
    rw [← Summable.tsum_add hs hc]
    apply tsum_congr
    intro q
    rw [generator_mul hd hε hlam ha b hφ q]
    change ψ q * (b q * generator ε a φ q + correction q) = _
    ring
  rw [hsum]
  change _ = ε ^ d * ∑' q : Site d, ψ q * correction q
  ring

end

end LongRange
