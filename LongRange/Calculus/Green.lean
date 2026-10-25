import LongRange.Calculus.Generator
import LongRange.Model.Energy

/-!
# Summation by parts for the nonlocal operator

The endpoint reversal `(q,w) ↦ (q+w,-w)` preserves the unordered conductance and the even
Euclidean kernel. Absolute convergence with one finitely supported factor permits this
reindexing and identifies the bilinear form with the negative generator pairing.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The Euclidean kernel is even. -/
theorem jumpKernel_neg (z : Fin d → ℝ) : jumpKernel (-z) = jumpKernel z := by
  simp only [jumpKernel, neg_eq_zero, radius, Pi.neg_apply, neg_sq]

/-- Physical scaling commutes with reversing the lattice increment. -/
theorem physical_neg (ε : ℝ) (w : Site d) : physical ε (-w) = -physical ε w := by
  ext i
  simp only [physical, Pi.neg_apply, Int.cast_neg, mul_neg]

/-- Reversing an edge preserves its unordered conductance index. -/
theorem edgeAdd_reverse (q w : Site d) (hw : w ≠ 0) :
    edgeAdd (q + w) (-w) (neg_ne_zero.mpr hw) = edgeAdd q w hw := by
  apply Subtype.ext
  change s(q + w, q + w + -w) = s(q, q + w)
  rw [add_neg_cancel_right]
  exact Sym2.eq_swap

/-- Reversal of the two endpoints of a directed lattice increment. -/
def edgeReverse (d : ℕ) : Site d × Site d ≃ Site d × Site d where
  toFun p := (p.1 + p.2, -p.2)
  invFun p := (p.1 + p.2, -p.2)
  left_inv p := by
    exact Prod.ext (add_neg_cancel_right _ _) (neg_neg _)
  right_inv p := by
    exact Prod.ext (add_neg_cancel_right _ _) (neg_neg _)

/-- The directed generator pairing before summing over sites and increments. -/
def generatorPair (ε : ℝ) (a : Edge d → ℝ) (f η : Site d → ℝ)
    (p : Site d × Site d) : ℝ :=
  if hw : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hw) *
    jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) * η p.1

/-- Absolute convergence of the directed pairing with a finitely supported test function. -/
theorem summable_generatorPair (hd : 1 ≤ d) {ε lam C : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hC : 0 ≤ C) (hf : ∀ q w, |f (q + w) - f q| ≤
      C * (1 + radius (physical ε w))) (hη : Function.HasFiniteSupport η) :
    Summable (generatorPair ε a f η) := by
  have hηs : Summable (fun q => |η q|) := by
    simpa only [Real.norm_eq_abs] using (summable_of_hasFiniteSupport hη).norm
  have hk := (summable_jumpKernel_weight hd hε).mul_left (lam⁻¹ * C)
  have hn : ∀ w : Site d, 0 ≤ lam⁻¹ * C *
      (jumpKernel (physical ε w) * (1 + radius (physical ε w))) := by
    intro w
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le) hC)
      (mul_nonneg (jumpKernel_nonneg _) (add_nonneg zero_le_one (radius_nonneg _)))
  refine (hηs.mul_of_nonneg hk (fun _ => abs_nonneg _) hn).of_norm_bounded ?_
  intro p
  unfold generatorPair
  by_cases hw : p.2 = 0
  · simp only [hw, ↓reduceDIte, norm_zero]
    exact mul_nonneg (abs_nonneg _) (hn _)
  · simp only [hw, ↓reduceDIte, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg (jumpKernel_nonneg _)]
    calc
      _ ≤ lam⁻¹ * jumpKernel (physical ε p.2) *
          (C * (1 + radius (physical ε p.2))) * |η p.1| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul
            (mul_le_mul_of_nonneg_right (ha _).2 (jumpKernel_nonneg _))
            (hf _ _) (abs_nonneg _)
            (mul_nonneg (inv_nonneg.mpr hlam.le) (jumpKernel_nonneg _))) (abs_nonneg _)
      _ = _ := by ring

/-- The bilinear summand splits into two oppositely oriented generator pairings. -/
theorem bilinForm_summand_eq (ε : ℝ) (a : Edge d → ℝ) (f η : Site d → ℝ)
    (p : Site d × Site d) :
    (if hw : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hw) *
      jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) *
        (η (p.1 + p.2) - η p.1)) =
      -generatorPair ε a f η (edgeReverse d p) - generatorPair ε a f η p := by
  rcases p with ⟨q, w⟩
  by_cases hw : w = 0
  · simp only [hw, edgeReverse, generatorPair, Equiv.coe_fn_mk, neg_zero, ↓reduceDIte,
      neg_zero, sub_zero]
  · simp only [hw, edgeReverse, generatorPair, Equiv.coe_fn_mk, neg_eq_zero,
      ↓reduceDIte, add_neg_cancel_right, physical_neg, jumpKernel_neg]
    rw [edgeAdd_reverse q w hw]
    ring

/-- Absolute convergence of the defining bilinear series with one finite test support. -/
theorem summable_bilinForm_of_increment_bound (hd : 1 ≤ d) {ε lam C : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hC : 0 ≤ C) (hf : ∀ q w, |f (q + w) - f q| ≤
      C * (1 + radius (physical ε w))) (hη : Function.HasFiniteSupport η) :
    Summable (fun p : Site d × Site d => if hw : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        (f (p.1 + p.2) - f p.1) * (η (p.1 + p.2) - η p.1)) := by
  have hs := summable_generatorPair hd hε hlam ha hC hf hη
  have hr : Summable (fun p : Site d × Site d =>
      generatorPair ε a f η (edgeReverse d p)) :=
    (Equiv.summable_iff (f := generatorPair ε a f η) (edgeReverse d)).mpr hs
  exact (hr.neg.sub hs).congr (fun p => (bilinForm_summand_eq ε a f η p).symm)

/-- The defining bilinear series is absolutely summable on bounded data with finite test
support. -/
theorem summable_bilinForm_bounded (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hf : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |f q| ≤ M)
    (hη : Function.HasFiniteSupport η) :
    Summable (fun p : Site d × Site d => if hw : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        (f (p.1 + p.2) - f p.1) * (η (p.1 + p.2) - η p.1)) := by
  obtain ⟨M, hM, hf⟩ := hf
  exact summable_bilinForm_of_increment_bound hd hε hlam ha (C := 2 * M)
    (mul_nonneg (by norm_num) hM) (bounded_increment_bound hM hf) hη

/-- The defining bilinear series converges for a physical linear function plus bounded data
with a finitely supported test function. -/
theorem summable_bilinForm_affine (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) {φ η : Site d → ℝ}
    (hφ : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |φ q| ≤ M)
    (hη : Function.HasFiniteSupport η) :
    Summable (fun r : Site d × Site d => if hw : r.2 = 0 then 0 else
      a (edgeAdd r.1 r.2 hw) * jumpKernel (physical ε r.2) *
        ((linearFn ε p (r.1 + r.2) + φ (r.1 + r.2)) -
          (linearFn ε p r.1 + φ r.1)) * (η (r.1 + r.2) - η r.1)) := by
  obtain ⟨M, hM, hφ⟩ := hφ
  exact summable_bilinForm_of_increment_bound hd hε hlam ha
    (C := (∑ i, |p i|) + 2 * M) (f := fun q => linearFn ε p q + φ q)
    (add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity))
    (affine_increment_bound ε p hM hφ) hη

/-- Summation by parts under the kernel first-moment increment estimate. -/
theorem bilinForm_eq_neg_generator_of_increment_bound (hd : 1 ≤ d) {ε lam C : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hC : 0 ≤ C) (hf : ∀ q w, |f (q + w) - f q| ≤
      C * (1 + radius (physical ε w))) (hη : Function.HasFiniteSupport η) :
    bilinForm ε a f η = -(ε ^ d * ∑' q : Site d, η q * generator ε a f q) := by
  have hs := summable_generatorPair hd hε hlam ha hC hf hη
  have hr : Summable (fun p : Site d × Site d =>
      generatorPair ε a f η (edgeReverse d p)) :=
    (Equiv.summable_iff (f := generatorPair ε a f η) (edgeReverse d)).mpr hs
  have hsum : (∑' p, generatorPair ε a f η (edgeReverse d p)) =
      ∑' p, generatorPair ε a f η p := (edgeReverse d).tsum_eq _
  have hpair : (∑' p, generatorPair ε a f η p) =
      ∑' q, η q * ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (f (q + w) - f q) * jumpKernel (physical ε w) := by
    rw [hs.tsum_prod]
    apply tsum_congr
    intro q
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    unfold generatorPair
    by_cases hw : w = 0 <;> simp only [hw, ↓reduceDIte] <;> ring
  have hgen : (∑' q : Site d, η q * generator ε a f q) =
      (ε ^ d / kappa d ε) * ∑' p, generatorPair ε a f η p := by
    rw [hpair, ← tsum_mul_left]
    apply tsum_congr
    intro q
    unfold generator
    ring
  have hn : Summable (fun p : Site d × Site d =>
      -generatorPair ε a f η (edgeReverse d p)) := hr.neg
  unfold bilinForm
  simp_rw [bilinForm_summand_eq]
  rw [Summable.tsum_sub hn hs, tsum_neg, hsum, hgen]
  have he : ε ^ (2 * d) = ε ^ d * ε ^ d := by rw [two_mul, pow_add]
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Green's identity for bounded data and a finitely supported test function. -/
theorem bilinForm_eq_neg_generator_bounded (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hf : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |f q| ≤ M)
    (hη : Function.HasFiniteSupport η) :
    bilinForm ε a f η = -(ε ^ d * ∑' q : Site d, η q * generator ε a f q) := by
  obtain ⟨M, hM, hf⟩ := hf
  exact bilinForm_eq_neg_generator_of_increment_bound hd hε hlam ha (C := 2 * M)
    (mul_nonneg (by norm_num) hM) (bounded_increment_bound hM hf) hη

/-- Green's identity for a physical linear function plus bounded data. -/
theorem bilinForm_eq_neg_generator_affine (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) {φ η : Site d → ℝ}
    (hφ : ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |φ q| ≤ M)
    (hη : Function.HasFiniteSupport η) :
    bilinForm ε a (fun q => linearFn ε p q + φ q) η =
      -(ε ^ d * ∑' q : Site d, η q *
        generator ε a (fun x => linearFn ε p x + φ x) q) := by
  obtain ⟨M, hM, hφ⟩ := hφ
  exact bilinForm_eq_neg_generator_of_increment_bound hd hε hlam ha
    (C := (∑ i, |p i|) + 2 * M) (f := fun q => linearFn ε p q + φ q)
    (add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity))
    (affine_increment_bound ε p hM hφ) hη

end

end LongRange
