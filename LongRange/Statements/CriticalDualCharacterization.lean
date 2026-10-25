import LongRange.Poincare.CriticalDual

/-!
# Well-definedness and the complete critical dual norm characterization
-/

namespace LongRange.Statements

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The source supremum is nonempty and bounded above, has the exact arbitrary-test
characterization, and is positive for every supported field nonzero at any site. -/

theorem critical_dual_characterization {d : ℕ} (D : CriticalDomain d) (g : D.Field) :
    (criticalDualValues D g).Nonempty ∧ BddAbove (criticalDualValues D g) ∧
      (∀ B : ℝ, LongRange.criticalDualNorm D g ≤ B ↔
        0 ≤ B ∧ ∀ h : Site d → ℝ, SupportedIn D.spacing D.domain h →
          |D.spacing ^ d * ∑' q, g.val q * h q| ≤
            B * Real.sqrt (h1CritSq D.spacing h)) ∧
      (∀ q : Site d, g.val q ≠ 0 → 0 < LongRange.criticalDualNorm D g) :=

by
  refine ⟨criticalDualValues_nonempty D g, criticalDualValues_bddAbove D g, ?_, ?_⟩
  · intro B
    exact criticalDualNorm_le_iff D g B
  · intro q hq
    exact criticalDualNorm_pos D g q hq

end

end LongRange.Statements
