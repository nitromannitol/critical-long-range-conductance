import LongRange.Poincare.CriticalDual

/-!
# The signed critical dual norm on the complete supported-field carrier
-/

namespace LongRange.Statements

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The literal signed critical dual supremum of (e.Hm1crit), on its source carrier.
The source formula and its full test characterization are proved in the imported provider. -/

def critical_dual_norm {d : ℕ} (D : CriticalDomain d) (g : D.Field) : ℝ :=
  LongRange.criticalDualNorm D g


end

end LongRange.Statements
