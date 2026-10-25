import LongRange.Dirichlet.ColumnBound
import LongRange.Dirichlet.Weights

/-!
# Square sums of short-range columns

The column estimate, punctured radial summability, and the lattice count give the
deterministic square-sum estimate used in Proposition 3.3.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- Short-range column squares satisfy the uniform domain-counting bound. -/
theorem short_column_sq_sum_bound (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (U : Set (Fin d → ℝ)) (hU : Bornology.IsBounded U),
      euclideanDiam U ≤ R → ∀ p : Fin d → ℝ,
        ∑ r ∈ (shortIndex_finite hε.1 hU).toFinset,
          (∑ x ∈ (latticeSet_finite hε.1 hU).toFinset, ∑ i : Fin d,
            (|shortCoeff ε U p x (unit i) r| +
              |shortCoeff ε U p x (-unit i) r|)) ^ 2 ≤
        C * radius p ^ 2 * ε ^ (-(3 * (d : ℝ) + 2)) := by
  classical
  obtain ⟨A, hA, ha⟩ := shortCoeff_column_sum_bound hd
  obtain ⟨B, hB, hb⟩ := ncard_latticeSet_le d R
  obtain ⟨D, hD, hdSum⟩ := punctured_radial_sum_bound hd (2 * d) (by omega)
  refine ⟨A ^ 2 * B * D, by positivity, ?_⟩
  intro ε hε U hU hdiam p
  let S := (latticeSet_finite hε.1 hU).toFinset
  let T := (shortIndex_finite hε.1 hU).toFinset
  let V := T.image (fun r => r.1.2)
  let g := fun v : Site d => if v = 0 then (0 : ℝ)
    else (radius (physical ε v) ^ (2 * d))⁻¹
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
  have hp := radius_nonneg p
  have he0 := hε.1.le
  obtain ⟨hg, hsum⟩ := hdSum ε hε.1
  have hcount : (S.card : ℝ) ≤ B * (ε ^ d)⁻¹ := by
    simpa only [S, ← Set.ncard_eq_toFinset_card _ (latticeSet_finite hε.1 hU),
      Real.rpow_neg hε.1.le, Real.rpow_natCast] using hb U hU hdiam ε hε
  have hradial : ∑ r ∈ T, g r.1.2 ≤ (S.card : ℝ) * (D / ε ^ (2 * d)) := by
    calc
      _ = ∑ q ∈ T.image Subtype.val, g q.2 := by
        rw [Finset.sum_image Subtype.val_injective.injOn]
      _ ≤ ∑ q ∈ S ×ˢ V, g q.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
          exact Finset.mem_product.mpr
            ⟨(latticeSet_finite hε.1 hU).mem_toFinset.mpr r.2.1,
              Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩
        · intro q _ _
          exact hg0 q.2
      _ = (S.card : ℝ) * ∑ v ∈ V, g v := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card : ℝ) * (∑' v, g v) :=
        mul_le_mul_of_nonneg_left
          (hg.sum_le_tsum V (fun v _ => hg0 v)) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((le_div_iff₀ (pow_pos hε.1 _)).mpr
          (by simpa only [g, mul_comm] using hsum)) (Nat.cast_nonneg _)
  have hcol : ∀ r : Cycle.indexSet ε U,
      (∑ x ∈ S, ∑ i : Fin d, (|shortCoeff ε U p x (unit i) r| +
        |shortCoeff ε U p x (-unit i) r|)) ^ 2 ≤
      (A * radius p / ε) ^ 2 * g r.1.2 := by
    intro r
    have hc := ha ε hε U hU p r
    have hn : 0 ≤ ∑ x ∈ S, ∑ i : Fin d,
        (|shortCoeff ε U p x (unit i) r| +
          |shortCoeff ε U p x (-unit i) r|) := by positivity
    have hr : 0 ≤ A * radius p / ε *
        (radius (physical ε r.1.2) ^ d)⁻¹ :=
      mul_nonneg (div_nonneg (mul_nonneg hA.le hp) he0)
        (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))
    have hs := (sq_le_sq₀ hn hr).mpr hc
    simpa only [g, if_neg r.2.2.1, mul_pow, inv_pow, ← pow_mul,
      show d * 2 = 2 * d by omega] using hs
  calc
    _ ≤ ∑ r ∈ T, (A * radius p / ε) ^ 2 * g r.1.2 :=
      Finset.sum_le_sum (fun r _ => hcol r)
    _ = (A * radius p / ε) ^ 2 * ∑ r ∈ T, g r.1.2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (A * radius p / ε) ^ 2 *
        ((S.card : ℝ) * (D / ε ^ (2 * d))) :=
      mul_le_mul_of_nonneg_left hradial (sq_nonneg _)
    _ ≤ (A * radius p / ε) ^ 2 *
        ((B * (ε ^ d)⁻¹) * (D / ε ^ (2 * d))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcount (by positivity)) (sq_nonneg _)
    _ = _ := by
      rw [show 3 * (d : ℝ) + 2 = ((3 * d + 2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hε.1.le, Real.rpow_natCast,
        show 3 * d + 2 = 2 + d + 2 * d by omega, pow_add, pow_add]
      simp only [mul_pow, mul_inv, div_eq_mul_inv]
      ring

end

end LongRange.Dirichlet
