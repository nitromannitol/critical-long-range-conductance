import LongRange.Model.Energy

/-!
# The literal critical negative Sobolev norm

The source carrier consists of supported functions on a bounded physical lattice domain,
with positive dimension and spacing in `(0, 1)`. The norm is the signed supremum in
(e.Hm1crit); its boundedness and full test characterization are proved in
`LongRange.Poincare.CriticalDual`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- Exactly the standing domain conditions of the source norms subsection. -/
structure CriticalDomain (d : ℕ) where
  dimension_pos : 1 ≤ d
  spacing : ℝ
  spacing_mem : spacing ∈ Set.Ioo (0 : ℝ) 1
  domain : Set (Fin d → ℝ)
  bounded : Bornology.IsBounded domain

variable {d : ℕ}

/-- A real function on the physical lattice, vanishing outside the source domain. -/
abbrev CriticalDomain.Field (D : CriticalDomain d) :=
  {g : Site d → ℝ // SupportedIn D.spacing D.domain g}

/-- Restriction to the source domain, extended by zero to the physical lattice. -/
def CriticalDomain.restrict (D : CriticalDomain d) (g : Site d → ℝ) : D.Field := by
  classical
  exact ⟨fun q => if q ∈ latticeSet D.spacing D.domain then g q else 0,
    fun q hq => if_neg hq⟩

/-- The physical-volume pairing in (e.Hm1crit), indexed by integer lattice sites. -/
def criticalPairing (ε : ℝ) (g h : Site d → ℝ) : ℝ :=
  ε ^ d * ∑' q, g q * h q

/-- The actual signed pairings against the supported critical unit ball. -/
def criticalDualValues (D : CriticalDomain d) (g : D.Field) : Set ℝ :=
  {r | ∃ h : Site d → ℝ, SupportedIn D.spacing D.domain h ∧
    Real.sqrt (h1CritSq D.spacing h) ≤ 1 ∧ r = criticalPairing D.spacing g h}

/-- The literal signed supremum of (e.Hm1crit), on its source carrier only. -/
def criticalDualNorm (D : CriticalDomain d) (g : D.Field) : ℝ :=
  sSup (criticalDualValues D g)

end

end LongRange
