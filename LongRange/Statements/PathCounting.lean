import LongRange.Preliminaries.PathCounting

/-!
# path counting

A statement-preserving wrapper for Lemma 2.3 (`l.path`).
-/

open LongRange LatticeProb LatticeProb.Euclidean.Lattice

/-- Lemma 2.3 (`l.path`): the integer and scaled-lattice path-counting bounds. -/

theorem LongRange.Statements.path_counting (d : ℕ) :
    (∀ z : Site d, z ≠ 0 → ∀ e : Sym2 (Site d), IsNNEdge e →
      {p : Site d × Site d | p.2 - p.1 = z ∧ e ∈ pathEdges (coordPath p.2 p.1)}.Finite ∧
      Nat.card {p : Site d × Site d | p.2 - p.1 = z ∧ e ∈ pathEdges (coordPath p.2 p.1)} ≤
        ∑ i, (z i).natAbs) ∧
    (∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ z : Fin d → ℝ,
      z ∈ Set.range (physical ε) → z ≠ 0 →
      ∀ e : Sym2 (Fin d → ℝ), IsScaledNNEdge ε e →
        {p : (Fin d → ℝ) × (Fin d → ℝ) | p.2 - p.1 = z ∧ ∃ u v : Site d,
            p.1 = physical ε u ∧ p.2 = physical ε v ∧
              e ∈ pathEdges (scaledCoordPath ε v u)}.Finite ∧
        (Nat.card {p : (Fin d → ℝ) × (Fin d → ℝ) | p.2 - p.1 = z ∧ ∃ u v : Site d,
            p.1 = physical ε u ∧ p.2 = physical ε v ∧
              e ∈ pathEdges (scaledCoordPath ε v u)} : ℝ) ≤ (∑ i, |z i|) / ε) :=

by exact LongRange.path_counting d
