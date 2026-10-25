import LongRange.HeatKernel.UniformPropositionA
import LongRange.HeatKernel.UniformDavies

/-!
# A field-uniform off-diagonal heat-kernel bound

The indexed truncation argument uses the same on-diagonal and Davies constants for
all admissible fields. Its spatial estimate and the common on-diagonal estimate give
the minimum bound with one constant depending only on dimension and ellipticity.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

/-- One positive constant gives the minimum heat bound for every admissible field. -/
theorem unitHeat_offDiagonal_uniform
    (hMSCUniform : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (d : ℕ) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Edge d → ℝ,
      ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
      ∀ t : ℝ≥0, 0 < t → ∀ x y : Site d, x ≠ y →
      ((unitRates hd hlam a ha).transitionKernel t x).real {y} ≤
        C * min ((1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)))
          (t * Real.log (2 + radius (physical 1 (y - x))) /
            radius (physical 1 (y - x)) ^ (d + 2)) := by
  obtain ⟨Ca, hCa, hdiag⟩ := unitHeat_onDiagonal_uniform hMSCUniform d hd hlam
  obtain ⟨A, B, _hA, _hB, hdav⟩ :=
    truncHeat_davies_uniform hMSCUniform hNash hDavies d hd hlam
  let Index := {a : Edge d → ℝ // ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹}
  obtain ⟨C, _hC, hoff⟩ := offDiagonal_of_truncated_bounds_uniform hd
    (fun (i : Index) t x y ↦
      ((unitRates hd hlam i.val i.property).transitionKernel t x).real {y})
    (fun (i : Index) ρ t x y ↦
      ((truncRates hd hlam i.val i.property ρ).transitionKernel t x).real {y})
    (fun i ↦ hdiag i.val i.property)
    (fun i ρ hρ t x y ↦ unitHeat_le_trunc_add hd hlam i.val i.property hρ t x y)
    (fun i ρ hρ hρ₁ t x y hxy ↦
      truncHeat_zero_of_lt_one hd hlam i.val i.property hρ hρ₁ t x y hxy)
    (fun i ↦ hdav i.val i.property)
  refine ⟨max Ca C, lt_of_lt_of_le hCa (le_max_left _ _), ?_⟩
  intro a ha t ht x y hxy
  rw [mul_min_of_nonneg _ _ (le_of_lt (lt_of_lt_of_le hCa (le_max_left _ _)))]
  apply le_min
  · apply (hdiag a ha t x y).trans
    have hlog : 0 ≤ Real.log (2 + (t : ℝ)) := Real.log_nonneg (by linarith [t.coe_nonneg])
    exact mul_le_mul_of_nonneg_right (le_max_left Ca C)
      (Real.rpow_nonneg (by positivity) _)
  · have hsp : 0 ≤ (t : ℝ) * Real.log (2 + radius (physical 1 (y - x))) /
        radius (physical 1 (y - x)) ^ (d + 2) := by
      apply div_nonneg
      · exact mul_nonneg t.coe_nonneg
          (zero_le_one.trans (one_le_log_two_add (one_le_radius_displacement hxy)))
      · exact pow_nonneg (radius_nonneg _) _
    have ho := hoff ⟨a, ha⟩ t ht x y hxy
    rw [mul_assoc, mul_div_assoc] at ho
    exact ho.trans (mul_le_mul_of_nonneg_right (le_max_right Ca C) hsp)

/-- Constant-one conductances are admissible at dimension one and ellipticity one half. -/
theorem one_field_admissible_half :
    ∀ e : Edge 1, (1 / 2 : ℝ) ≤ (fun _ : Edge 1 ↦ (1 : ℝ)) e ∧
      (fun _ : Edge 1 ↦ (1 : ℝ)) e ≤ (1 / 2 : ℝ)⁻¹ := by
  intro e
  norm_num

/-- The uniform minimum bound applies to the actual constant-one field at ellipticity
one half in dimension one. -/
theorem unitHeat_offDiagonal_one_half
    (hMSCUniform : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ≥0, 0 < t → ∀ x y : Site 1, x ≠ y →
      ((unitRates (by norm_num : 1 ≤ 1) (by norm_num : (0 : ℝ) < 1 / 2)
        (fun _ : Edge 1 ↦ (1 : ℝ)) one_field_admissible_half).transitionKernel t x).real {y} ≤
        C * min ((1 + t * Real.log (2 + t)) ^ (-(1 / (2 : ℝ))))
          (t * Real.log (2 + radius (physical 1 (y - x))) /
            radius (physical 1 (y - x)) ^ 3) := by
  obtain ⟨C, hC, hbound⟩ := unitHeat_offDiagonal_uniform hMSCUniform hNash hDavies
    1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨C, hC, ?_⟩
  intro t ht x y hxy
  simpa only [Nat.cast_one, Nat.reduceAdd] using
    hbound (fun _ : Edge 1 ↦ (1 : ℝ)) one_field_admissible_half t ht x y hxy

end

end LongRange
