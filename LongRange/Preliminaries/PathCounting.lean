import LongRange.Model.Path
import LongRange.Preliminaries.PathCounting.Scaling

/-!
# Coordinate-path counting

Lemma 2.3 (`l.path`) bounds the number of pairs of a fixed displacement whose coordinate path
uses a fixed nearest-neighbour edge. The physical statement follows by positive rescaling.
-/

namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice

/-- Lemma 2.3 (`l.path`): at most the ℓ¹ path length many translates use a fixed edge, on both
integer and positively scaled lattices. -/
theorem path_counting (d : ℕ) :
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
              e ∈ pathEdges (scaledCoordPath ε v u)} : ℝ) ≤ (∑ i, |z i|) / ε) := by
  constructor
  · intro z _ e _
    exact integer_path_counting z e
  · rintro ε hε z ⟨q, rfl⟩ _ e ⟨x, i, rfl⟩
    exact scaled_path_counting ε hε.1 q s(x, x + unit i)

end LongRange
