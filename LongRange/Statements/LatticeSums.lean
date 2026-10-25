import LongRange.Appendix.LatticeSums

/-!
# Euclidean lattice sums

A statement-preserving wrapper for Proposition A.1.
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- The complete Euclidean lattice-sum estimates of Proposition A.1. -/

theorem LongRange.Statements.lattice_sums (d : ℕ) :
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
            jumpKernel (physical ε q) * physical ε q i * physical ε q j = 0) :=

by exact LongRange.lattice_sums d
