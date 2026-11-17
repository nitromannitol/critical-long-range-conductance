import Mathlib

/-!
# Heat equation vocabulary

Definitions for the quantitative heat homogenization estimate, expressed with integer sites
and the Euclidean norm.
-/

namespace LongRangeAudit.HeatHomogenization

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- Integer sites of the lattice. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- Unordered pairs of distinct lattice sites. -/
abbrev Edge (d : ℕ) := {e : Sym2 (Site d) // ¬ e.IsDiag}

/-- The edge joining distinct sites. -/
def edge {d : ℕ} (x y : Site d) (h : x ≠ y) : Edge d :=
  ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using h⟩

/-- The edge from a site in a nonzero direction. -/
def edgeAdd {d : ℕ} (q w : Site d) (hw : w ≠ 0) : Edge d :=
  edge q (q + w) (by simpa using fun h : q = q + w => hw (by simpa using h.symm))

/-- The Euclidean position of an integer site on the scaled lattice. -/
def physical {d : ℕ} (ε : ℝ) (z : Site d) : Fin d → ℝ := fun k => ε * (z k : ℝ)

/-- The Euclidean radius. -/
def radius {d : ℕ} (v : Fin d → ℝ) : ℝ := Real.sqrt (∑ k, (v k) ^ 2)

/-- A finite box containing all indices of the scaled unit ball. -/
def cutoffBox (d : ℕ) (ε : ℝ) : Finset (Site d) :=
  Fintype.piFinset (fun _ => Finset.Icc (-⌈1 / ε⌉) ⌈1 / ε⌉)

/-- Nonzero indices in the scaled unit ball. -/
def unitBallIndices (d : ℕ) (ε : ℝ) : Finset (Site d) :=
  (cutoffBox d ε).filter (fun z => z ≠ 0 ∧ radius (physical ε z) ≤ 1)

/-- The normalization of the critical kernel. -/
def kappa (d : ℕ) (ε : ℝ) : ℝ :=
  ε ^ d * ∑ q ∈ unitBallIndices d ε, (radius (physical ε q) ^ d)⁻¹

/-- The critical jump kernel. -/
def jumpKernel {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  if z = 0 then 0 else (radius z ^ (d + 2))⁻¹

/-- The long-range lattice generator. -/
def generator {d : ℕ} (ε : ℝ) (a : Edge d → ℝ) (h : Site d → ℝ) (q : Site d) : ℝ :=
  ε ^ d / kappa d ε * ∑' w : Site d,
    if hw : w = 0 then 0
    else a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w)

/-- The conductances are independent, bounded and have mean one. -/
structure ConductanceLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ)
    (a : Ω → Edge d → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  lam_mem : lam ∈ Ioc (0 : ℝ) 1
  measurable : ∀ e, Measurable fun ω => a ω e
  indep : iIndepFun (fun e ω => a ω e) P
  bounds : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹
  mean_one : ∀ e, ∫ ω, a ω e ∂P = 1

/-- Restriction to the scaled lattice. -/
def restrict {d : ℕ} (ε : ℝ) (f : (Fin d → ℝ) → ℝ) (q : Site d) : ℝ := f (physical ε q)

/-- The scaled square-integrable norm. -/
def latticeNorm {d : ℕ} (ε : ℝ) (v : Site d → ℝ) : ℝ :=
  Real.sqrt (ε ^ d * ∑' q, v q ^ 2)

/-- Square summability on the lattice. -/
def MemL2 {d : ℕ} (v : Site d → ℝ) : Prop := Summable fun q => v q ^ 2

/-- The exponential moment bound of order `q`. -/
def IsOq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q : ℕ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  AEMeasurable X P ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / A) ^ q)) ∂P ≤ 2

/-- The heat kernel for the operator `(2d)⁻¹ Δ`. -/
def heatKernel (d : ℕ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  if 0 < t then ∏ i : Fin d, ((2 * Real.pi * t / d) ^ (-(1 : ℝ) / 2) *
    Real.exp (-(d : ℝ) * x i ^ 2 / (2 * t))) else 0

/-- The continuum heat flow. -/
def continuumHeat {d : ℕ} (f : (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  if t = 0 then f x else ∫ y, heatKernel d t (x - y) * f y

/-- The lattice heat flow as the exponential series of its generator. -/
def latticeHeat {d : ℕ} (ε : ℝ) (a : Edge d → ℝ) (f : (Fin d → ℝ) → ℝ)
    (t : ℝ) (q : Site d) : ℝ :=
  ∑' n : ℕ, t ^ n / (n.factorial : ℝ) * (generator ε a)^[n] (restrict ε f) q

end
end LongRangeAudit.HeatHomogenization
