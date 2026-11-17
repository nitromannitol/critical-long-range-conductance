import LongRangeHeat.LatticeSemigroup

/-!
# Norm inequalities for lattice scaling

The weighted lattice norm satisfies the triangle inequality for square-summable fields and
scales by the square root of the lattice volume under halving.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

private theorem norm_lp_eq_latticeNorm (ε : ℝ) (hε : 0 ≤ ε)
    (v : lp (fun _ : Site d => ℝ) 2) :
    latticeNorm ε v = Real.sqrt (ε ^ d) * ‖v‖ := by
  have hv := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) v
  have hv' : ‖v‖ ^ 2 = ∑' q, v q ^ 2 := by
    simpa [Real.norm_eq_abs, Real.rpow_two] using hv
  unfold latticeNorm latticeNormSq
  rw [Real.sqrt_mul (pow_nonneg hε _), ← hv', Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-- The weighted lattice norm satisfies the triangle inequality on square-summable fields. -/
theorem latticeNorm_add_le {ε : ℝ} (hε : 0 ≤ ε) {v w : Site d → ℝ}
    (hv : MemL2 v) (hw : MemL2 w) :
    latticeNorm ε (fun q => v q + w q) ≤ latticeNorm ε v + latticeNorm ε w := by
  have hv' : Memℓp v 2 := by
    apply memℓp_gen
    simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using hv
  have hw' : Memℓp w 2 := by
    apply memℓp_gen
    simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using hw
  let V : lp (fun _ : Site d => ℝ) 2 := ⟨v, hv'⟩
  let W : lp (fun _ : Site d => ℝ) 2 := ⟨w, hw'⟩
  change latticeNorm ε (V + W) ≤ latticeNorm ε V + latticeNorm ε W
  rw [norm_lp_eq_latticeNorm ε hε, norm_lp_eq_latticeNorm ε hε,
    norm_lp_eq_latticeNorm ε hε, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le V W) (Real.sqrt_nonneg _)

/-- Halving the spacing multiplies the weighted norm by the square root of the volume factor. -/
theorem latticeNorm_half (ε : ℝ) (v : Site d → ℝ) :
    latticeNorm (ε / 2) v = Real.sqrt ((2 : ℝ)⁻¹ ^ d) * latticeNorm ε v := by
  unfold latticeNorm latticeNormSq
  rw [div_eq_mul_inv, mul_pow, mul_comm (ε ^ d), mul_assoc,
    Real.sqrt_mul (by positivity)]

end
end LongRangeHeat
