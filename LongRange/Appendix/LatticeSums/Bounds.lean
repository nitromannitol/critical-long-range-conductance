import LongRange.Model.Kernel
import LatticeProb.Euclidean.Estimates

/-!
# Radial upper bounds for Proposition A.1

The Euclidean library supplies the three regimes of the interior sum and the summable exterior
bound. Their constants are enlarged to a common positive constant depending only on the exponent
and dimension. In dimension zero both index sums vanish.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

namespace LatticeSums

/-- In dimension zero the nonzero unit-ball index set is empty. -/
lemma unit_ball_zero (ε : ℝ) : unitBallIndices 0 ε = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hn := (Finset.mem_filter.mp hq).2.1
  exact hn (Subsingleton.elim q 0)

/-- The exterior summand vanishes in dimension zero. -/
lemma exterior_zero (ε α : ℝ) (q : Site 0) :
    (if 1 ≤ radius (physical ε q) then 1 / radius (physical ε q) ^ α else 0) = 0 := by
  simp only [radius, Finset.univ_eq_empty, Finset.sum_empty, Real.sqrt_zero]
  norm_num

/-- The interior and exterior radial bounds share one positive constant for every dimension. -/
theorem radial_bounds (d : ℕ) :
    ∀ α : ℝ, 0 ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ d * (∑ q ∈ unitBallIndices d ε, 1 / radius (physical ε q) ^ α) ≤
          (if α < d then C else if α = d then C * (1 + |Real.log ε|)
            else C * ε ^ ((d : ℝ) - α)) ∧
        ((d : ℝ) < α →
          Summable (fun q : Site d =>
            if 1 ≤ radius (physical ε q) then 1 / radius (physical ε q) ^ α else 0) ∧
          ε ^ d * ∑' q : Site d,
            (if 1 ≤ radius (physical ε q) then 1 / radius (physical ε q) ^ α else 0) ≤ C) := by
  intro α hα
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε
    constructor
    · simp only [unit_ball_zero, Finset.sum_empty, mul_zero]
      split_ifs
      · exact zero_le_one
      · positivity
      · exact mul_nonneg zero_le_one (Real.rpow_nonneg hε.1.le _)
    · intro _
      simp only [exterior_zero]
      exact ⟨summable_zero, by simp only [tsum_zero, mul_zero]; norm_num⟩
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  obtain ⟨A, hA, hupper⟩ := Euclidean.Estimates.rpow_sum_upper_bound d hd1 α hα
  have hconvert (x : Fin d → ℝ) : 1 / radius x ^ α = radius x ^ (-α) := by
    rw [Real.rpow_neg (radius_nonneg x), one_div]
  by_cases hαd : (d : ℝ) < α
  · obtain ⟨B, hB, hexterior⟩ := Euclidean.Estimates.exterior_rpow_sum_bound d hd1 α hαd
    refine ⟨max A B, lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
    intro ε hε
    constructor
    · simp_rw [hconvert]
      apply (hupper ε hε).trans
      split_ifs
      · exact le_max_left _ _
      · exact mul_le_mul_of_nonneg_right (le_max_left A B) (by positivity)
      · exact mul_le_mul_of_nonneg_right (le_max_left A B)
          (Real.rpow_nonneg hε.1.le _)
    · intro _
      simp_rw [hconvert]
      exact ⟨(hexterior ε hε).1, (hexterior ε hε).2.trans (le_max_right A B)⟩
  · refine ⟨A, hA, ?_⟩
    intro ε hε
    constructor
    · simpa only [hconvert] using hupper ε hε
    · exact fun h => (hαd h).elim

end LatticeSums
end
end LongRange
