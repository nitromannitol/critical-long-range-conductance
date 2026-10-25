import LongRange.Model.Lattice

/-!
# Random conductances indexed by unordered edges (Assumption (U))

The conductances `{a(x, y)}_{x ≠ y}` are indexed by unordered edges `{x, y}` of the complete
graph on `ℤ^d`, so `a(x, y) = a(y, x)` holds by construction.  An edge is an off-diagonal
element of `Sym2 (Site d)`.  Assumption (U) asks for a probability space carrying a family of
measurable conductances that are independent, identically distributed and satisfy
`λ ≤ a(x, y) ≤ λ⁻¹` for a fixed `λ ∈ (0, 1]`, in dimension `d ≥ 1`.
-/

namespace LongRange

open MeasureTheory ProbabilityTheory LatticeProb

noncomputable section

variable {d : ℕ}

/-- An unordered edge `{x, y}` with `x ≠ y` of the complete graph on `ℤ^d`. -/
abbrev Edge (d : ℕ) : Type := {e : Sym2 (Site d) // ¬ e.IsDiag}

/-- The unordered edge `{x, y}` for distinct sites `x ≠ y`. -/
def edge (x y : Site d) (h : x ≠ y) : Edge d :=
  ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using h⟩

/-- The edge `{q, q + w}` for a nonzero increment `w`. -/
def edgeAdd (q w : Site d) (hw : w ≠ 0) : Edge d :=
  edge q (q + w) (by simpa using fun h : q = q + w => hw (by simpa using h.symm))

/-- The edge `{x, y}` is symmetric in its endpoints. -/
theorem edge_comm (x y : Site d) (h : x ≠ y) : edge x y h = edge y x (Ne.symm h) :=
  Subtype.ext Sym2.eq_swap

/-- Assumption (U): in dimension `d ≥ 1`, with `λ ∈ (0, 1]`, the conductances
`a = {a(e)}_e`, indexed by unordered edges, are measurable, independent and identically
distributed under the probability measure `P`, and satisfy `λ ≤ a(e) ≤ λ⁻¹` for every `ω`
(an almost-sure bound reduces to this by modifying `a` on a null set, which changes no law). -/
structure AssumptionU {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ)
    (a : Ω → Edge d → ℝ) : Prop where
  one_le_dim : 1 ≤ d
  lam_pos : 0 < lam
  lam_le_one : lam ≤ 1
  isProbabilityMeasure : IsProbabilityMeasure P
  measurable : ∀ e, Measurable fun ω => a ω e
  iIndep : iIndepFun (fun e ω => a ω e) P
  identDistrib : ∀ e e', IdentDistrib (fun ω => a ω e) (fun ω => a ω e') P P
  bounds : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹

/-- The first unit vector `e₁` of `ℤ^d`, for `d ≥ 1`. -/
def firstUnit (hd : 1 ≤ d) : Site d :=
  unit ⟨0, hd⟩

/-- The edge `{0, e₁}`. -/
def baseEdge (hd : 1 ≤ d) : Edge d :=
  edge 0 (firstUnit hd) (fun h => unit_ne_zero (⟨0, hd⟩ : Fin d) h.symm)

/-- The mean conductance `E[a(0, e₁)]`. -/
def meanConductance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hd : 1 ≤ d)
    (a : Ω → Edge d → ℝ) : ℝ :=
  ∫ ω, a ω (baseEdge hd) ∂P

end

end LongRange
