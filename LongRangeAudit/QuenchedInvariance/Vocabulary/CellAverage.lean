import LongRangeAudit.QuenchedInvariance.Vocabulary.WalkRates

/-! # Independent CellAverage vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LongRange
open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The full half-open cube centered at the physical lattice point. -/
def cellCube (ε : ℝ) (q : Site d) : Set (Fin d → ℝ) :=
  {y | ∀ i, physical ε q i - ε / 2 ≤ y i ∧ y i < physical ε q i + ε / 2}

/-- A cell is a product of half-open intervals. -/
theorem cellCube_eq_pi (ε : ℝ) (q : Site d) :
    cellCube ε q = Set.pi Set.univ
      (fun i => Set.Ico (physical ε q i - ε / 2) (physical ε q i + ε / 2)) := by
  ext y
  simp only [cellCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
    forall_const]

/-- Full cells are Lebesgue measurable. -/
theorem measurableSet_cellCube (ε : ℝ) (q : Site d) : MeasurableSet (cellCube ε q) := by
  rw [cellCube_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

/-- Distinct lattice sites have disjoint full cells. -/
theorem cellCube_disjoint {ε : ℝ} (hε : 0 < ε) {q q' : Site d} (hne : q ≠ q') :
    Disjoint (cellCube ε q) (cellCube ε q') := by
  apply Set.disjoint_left.mpr
  intro y hy hy'
  apply hne
  funext i
  have h₁ := hy i
  have h₂ := hy' i
  dsimp [physical] at h₁ h₂
  have hlt : |(q i : ℝ) - q' i| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hint : |q i - q' i| < (1 : ℤ) := by exact_mod_cast hlt
  have := abs_lt.mp hint
  omega

/-- Zero extension averaged over a full cell, with denominator `ε^d`. -/
def cellAverage (ε : ℝ) (U : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ)
    (q : Site d) : ℝ :=
  (ε ^ d)⁻¹ * ∫ y in cellCube ε q, U.indicator f y

end LongRange
end

end LongRangeAudit.QuenchedInvariance
