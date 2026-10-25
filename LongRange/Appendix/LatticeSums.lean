import LongRange.Appendix.LatticeSums.Bounds
import LongRange.Appendix.LatticeSums.Diagonal

/-!
# Euclidean lattice sums

Proposition A.1 bounds interior and exterior radial sums on the rescaled Euclidean lattice.
Coordinate symmetry and the critical shell asymptotic give the normalized diagonal limit and
exact cancellation of mixed moments.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

/-- **Proposition A.1.** Interior radial sums have bounded, logarithmic, or power growth according
as the exponent is below, equal to, or above the dimension. Above the dimension the exterior
sum is summable and uniformly bounded after scaling. The critical diagonal moments approach
the Euclidean unit-ball volume with logarithmic error, and all mixed moments vanish. -/
theorem lattice_sums (d : ℕ) :
    (∀ α : ℝ, 0 ≤ α → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ d * (∑ q ∈ unitBallIndices d ε, 1 / radius (physical ε q) ^ α) ≤
          (if α < d then C else if α = d then C * (1 + |Real.log ε|)
            else C * ε ^ ((d : ℝ) - α)) ∧
        ((d : ℝ) < α →
          Summable (fun q : Site d =>
            if 1 ≤ radius (physical ε q) then 1 / radius (physical ε q) ^ α else 0) ∧
          ε ^ d * ∑' q : Site d,
            (if 1 ≤ radius (physical ε q) then 1 / radius (physical ε q) ^ α else 0) ≤ C)) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) (1 / 2) →
      (∀ i : Fin d,
        ε ^ d / |Real.log ε| *
            ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i ^ 2 =
          ε ^ d / (d * |Real.log ε|) *
            ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * radius (physical ε q) ^ 2 ∧
        |ε ^ d / |Real.log ε| *
            ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i ^ 2 -
          Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)| ≤ K / |Real.log ε|) ∧
      ∀ i j : Fin d, i ≠ j →
        ε ^ d / |Real.log ε| *
          ∑ q ∈ unitBallIndices d ε,
            jumpKernel (physical ε q) * physical ε q i * physical ε q j = 0) := by
  refine ⟨LatticeSums.radial_bounds d, ?_⟩
  by_cases hd : d = 0
  · subst d
    refine ⟨0, le_rfl, ?_⟩
    intro ε _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · obtain ⟨K, hK, hdiag⟩ :=
      LatticeSums.diagonal_asymptotic (Nat.one_le_iff_ne_zero.mpr hd)
    refine ⟨K, hK, ?_⟩
    intro ε hε
    constructor
    · intro i
      exact ⟨LatticeSums.diagonal_identity hε.1 i, hdiag ε hε i⟩
    · intro i j hij
      rw [LatticeSums.mixed_sum_eq_zero hε.1 hij, mul_zero]

end LongRange
