import LongRange.Calculus.Green

/-!
# Algebra and ellipticity of the discrete energy

Finite support guarantees absolute convergence of all energy series. The unordered-edge
bilinear form is symmetric and bilinear, nonnegative on the diagonal, and comparable to the
critical seminorm with the paper's factor of one half.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The normalization is nonnegative at nonnegative scales. -/
theorem kappa_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ kappa d ε := by
  unfold kappa
  exact mul_nonneg (pow_nonneg hε _) (Finset.sum_nonneg (fun _ _ =>
    inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)))

/-- Symmetry of the bilinear energy follows termwise, without a convergence assumption. -/
theorem bilinForm_comm (ε : ℝ) (a : Edge d → ℝ) (u v : Site d → ℝ) :
    bilinForm ε a u v = bilinForm ε a v u := by
  unfold bilinForm
  congr 1
  apply tsum_congr
  intro p
  by_cases hw : p.2 = 0
  · simp only [hw, ↓reduceDIte]
  · simp only [hw, ↓reduceDIte]
    ring

/-- Nonnegative conductances give a nonnegative diagonal energy. -/
theorem bilinForm_self_nonneg {ε : ℝ} (hε : 0 ≤ ε) {a : Edge d → ℝ}
    (ha : ∀ e, 0 ≤ a e) (u : Site d → ℝ) : 0 ≤ bilinForm ε a u u := by
  unfold bilinForm
  apply mul_nonneg
  · exact div_nonneg (pow_nonneg hε _) (mul_nonneg (by norm_num) (kappa_nonneg hε))
  · apply tsum_nonneg
    intro p
    by_cases hw : p.2 = 0
    · simp only [hw, ↓reduceDIte, le_refl]
    · simp only [hw, ↓reduceDIte]
      convert mul_nonneg (mul_nonneg (ha (edgeAdd p.1 p.2 hw))
        (jumpKernel_nonneg (physical ε p.2)))
        (sq_nonneg (u (p.1 + p.2) - u p.1)) using 1
      ring

/-- The bilinear series converges when both factors have finite support. -/
theorem summable_bilinForm (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {u v : Site d → ℝ} (hu : Function.HasFiniteSupport u)
    (hv : Function.HasFiniteSupport v) :
    Summable (fun p : Site d × Site d => if hw : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        (u (p.1 + p.2) - u p.1) * (v (p.1 + p.2) - v p.1)) := by
  obtain ⟨M, hM, hu⟩ := exists_bound_of_finite_support hu
  exact summable_bilinForm_of_increment_bound hd hε hlam ha (C := 2 * M)
    (mul_nonneg (by norm_num) hM) (bounded_increment_bound hM hu) hv

/-- Additivity in the first argument on finitely supported functions. -/
theorem bilinForm_add_left (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {u v w : Site d → ℝ} (hu : Function.HasFiniteSupport u)
    (hv : Function.HasFiniteSupport v) (hw : Function.HasFiniteSupport w) :
    bilinForm ε a (u + v) w = bilinForm ε a u w + bilinForm ε a v w := by
  have hu' := summable_bilinForm hd hε hlam ha hu hw
  have hv' := summable_bilinForm hd hε hlam ha hv hw
  unfold bilinForm
  rw [show (fun p : Site d × Site d => if hz : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hz) * jumpKernel (physical ε p.2) *
        ((u + v) (p.1 + p.2) - (u + v) p.1) * (w (p.1 + p.2) - w p.1)) =
      (fun p : Site d × Site d => (if hz : p.2 = 0 then 0 else
        a (edgeAdd p.1 p.2 hz) * jumpKernel (physical ε p.2) *
          (u (p.1 + p.2) - u p.1) * (w (p.1 + p.2) - w p.1)) +
        (if hz : p.2 = 0 then 0 else
        a (edgeAdd p.1 p.2 hz) * jumpKernel (physical ε p.2) *
          (v (p.1 + p.2) - v p.1) * (w (p.1 + p.2) - w p.1))) by
    funext p
    by_cases hz : p.2 = 0 <;> simp only [hz, ↓reduceDIte, Pi.add_apply] <;> ring]
  rw [Summable.tsum_add hu' hv', mul_add]

/-- Scalar homogeneity in the first argument holds for the exact energy definition. -/
theorem bilinForm_smul_left (ε : ℝ) (a : Edge d → ℝ) (c : ℝ) (u v : Site d → ℝ) :
    bilinForm ε a (c • u) v = c * bilinForm ε a u v := by
  unfold bilinForm
  rw [show (fun p : Site d × Site d => if hw : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        ((c • u) (p.1 + p.2) - (c • u) p.1) * (v (p.1 + p.2) - v p.1)) =
      (fun p : Site d × Site d => c * (if hw : p.2 = 0 then 0 else
        a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
          (u (p.1 + p.2) - u p.1) * (v (p.1 + p.2) - v p.1))) by
    funext p
    by_cases hw : p.2 = 0 <;>
      simp only [hw, ↓reduceDIte, Pi.smul_apply, smul_eq_mul] <;> ring]
  rw [tsum_mul_left]
  ring

/-- Additivity in the second argument on finitely supported functions. -/
theorem bilinForm_add_right (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {u v w : Site d → ℝ} (hu : Function.HasFiniteSupport u)
    (hv : Function.HasFiniteSupport v) (hw : Function.HasFiniteSupport w) :
    bilinForm ε a u (v + w) = bilinForm ε a u v + bilinForm ε a u w := by
  rw [bilinForm_comm ε a u (v + w), bilinForm_add_left hd hε hlam ha hv hw hu,
    bilinForm_comm ε a v u, bilinForm_comm ε a w u]

/-- Scalar homogeneity in the second argument. -/
theorem bilinForm_smul_right (ε : ℝ) (a : Edge d → ℝ) (c : ℝ) (u v : Site d → ℝ) :
    bilinForm ε a u (c • v) = c * bilinForm ε a u v := by
  rw [bilinForm_comm, bilinForm_smul_left, bilinForm_comm ε a v u]

/-- The critical seminorm series is absolutely summable on finitely supported functions. -/
theorem summable_h1CritSq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {w : Site d → ℝ} (hw : Function.HasFiniteSupport w) :
    Summable (fun p : Site d × Site d => jumpKernel (physical ε p.2) *
      (w (p.1 + p.2) - w p.1) ^ 2) := by
  have hs := summable_bilinForm hd hε (lam := 1) zero_lt_one
    (a := fun _ => 1) (fun _ => by norm_num) hw hw
  refine hs.congr (fun p => ?_)
  by_cases hz : p.2 = 0
  · simp only [hz, ↓reduceDIte, add_zero, sub_self, zero_pow (by decide : 2 ≠ 0),
      mul_zero]
  · simp only [hz, ↓reduceDIte, one_mul]
    ring

/-- Ellipticity compares the energy and critical seminorm with the factor `1/2` in the paper. -/
theorem bilinForm_self_bounds (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {w : Site d → ℝ} (hw : Function.HasFiniteSupport w) :
    lam / 2 * h1CritSq ε w ≤ bilinForm ε a w w ∧
      bilinForm ε a w w ≤ lam⁻¹ / 2 * h1CritSq ε w := by
  have hs := summable_bilinForm hd hε hlam ha hw hw
  have ht := summable_h1CritSq hd hε hw
  have hpoint : ∀ p : Site d × Site d,
      lam * (jumpKernel (physical ε p.2) * (w (p.1 + p.2) - w p.1) ^ 2) ≤
        (if hz : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hz) *
          jumpKernel (physical ε p.2) * (w (p.1 + p.2) - w p.1) *
            (w (p.1 + p.2) - w p.1)) ∧
      (if hz : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hz) *
          jumpKernel (physical ε p.2) * (w (p.1 + p.2) - w p.1) *
            (w (p.1 + p.2) - w p.1)) ≤
        lam⁻¹ * (jumpKernel (physical ε p.2) * (w (p.1 + p.2) - w p.1) ^ 2) := by
    intro p
    by_cases hz : p.2 = 0
    · simp only [hz, ↓reduceDIte, add_zero, sub_self, mul_zero,
        zero_pow (by decide : 2 ≠ 0), le_refl, and_self]
    · simp only [hz, ↓reduceDIte]
      have hn := mul_nonneg (jumpKernel_nonneg (physical ε p.2))
        (sq_nonneg (w (p.1 + p.2) - w p.1))
      constructor
      · simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right (ha (edgeAdd p.1 p.2 hz)).1 hn
      · simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right (ha (edgeAdd p.1 p.2 hz)).2 hn
  have hlo := Summable.tsum_le_tsum (fun p => (hpoint p).1) (ht.mul_left lam) hs
  have hhi := Summable.tsum_le_tsum (fun p => (hpoint p).2) hs (ht.mul_left lam⁻¹)
  rw [tsum_mul_left] at hlo hhi
  have hc : 0 ≤ ε ^ (2 * d) / (2 * kappa d ε) :=
    div_nonneg (pow_nonneg hε.le _) (mul_nonneg (by norm_num) (kappa_nonneg hε.le))
  have hscale (r : ℝ) : r / 2 * h1CritSq ε w =
      ε ^ (2 * d) / (2 * kappa d ε) *
        (r * ∑' p : Site d × Site d, jumpKernel (physical ε p.2) *
          (w (p.1 + p.2) - w p.1) ^ 2) := by
    unfold h1CritSq
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  constructor
  · rw [hscale lam]
    exact mul_le_mul_of_nonneg_left hlo hc
  · rw [hscale lam⁻¹]
    exact mul_le_mul_of_nonneg_left hhi hc

/-- Cauchy--Schwarz for the nonnegative discrete energy on finite supports. -/
theorem abs_bilinForm_le (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {u v : Site d → ℝ} (hu : Function.HasFiniteSupport u)
    (hv : Function.HasFiniteSupport v) :
    |bilinForm ε a u v| ≤ Real.sqrt (bilinForm ε a u u) *
      Real.sqrt (bilinForm ε a v v) := by
  have hquad : ∀ t : ℝ, 0 ≤ bilinForm ε a u u * (t * t) +
      (2 * bilinForm ε a u v) * t + bilinForm ε a v v := by
    intro t
    have htu : Function.HasFiniteSupport (t • u) := by
      change Function.HasFiniteSupport (fun q => t * u q)
      exact Function.HasFiniteSupport.mul_right (fun _ => t) hu
    have hn := bilinForm_self_nonneg hε.le (fun e => hlam.le.trans (ha e).1)
      (t • u + v)
    rw [bilinForm_add_left hd hε hlam ha htu hv (htu.add hv),
      bilinForm_add_right hd hε hlam ha htu htu hv,
      bilinForm_add_right hd hε hlam ha hv htu hv,
      bilinForm_smul_left, bilinForm_smul_right, bilinForm_smul_left,
      bilinForm_smul_right, bilinForm_comm ε a v u] at hn
    convert hn using 1
    ring
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  have hsq : bilinForm ε a u v ^ 2 ≤ bilinForm ε a u u * bilinForm ε a v v := by
    nlinarith only [hdisc]
  exact (Real.abs_le_sqrt hsq).trans_eq
    (Real.sqrt_mul (bilinForm_self_nonneg hε.le
      (fun e => hlam.le.trans (ha e).1) u) _)

end

end LongRange
