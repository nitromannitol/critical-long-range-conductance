import LongRange.TwoScale.SmoothError
import LongRange.TwoScale.BoundaryDefect
import LongRange.Model.Corrector

/-!
# The objects of the two-scale expansion (main proof, Steps 1–2)

For a function `v` on `ℝ^d` (the smooth extension `ũ_μ` of the homogenized solution) and
correctors `φ i` (slopes `e_i`), the lattice objects of (e.ubar0), (e.weps), (e.rdef),
(e.E1sm.def) and (e.E2.def). The boundary error (e.E1bd.def) is `boundaryDefect` applied to
`exteriorDefect`. The homogenized solution itself does not appear: on `U` it equals `v`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

open Classical in
/-- The zero extension `ū⁰` of (e.ubar0) sampled at the lattice sites. -/
def zeroExtension (ε : ℝ) (U : Set (Fin d → ℝ)) (v : (Fin d → ℝ) → ℝ) (q : Site d) : ℝ :=
  if physical ε q ∈ U then v (physical ε q) else 0

/-- The coefficient `b_i = ∂_i ũ` sampled at the lattice sites. -/
def gradientCoeff (ε : ℝ) (v : (Fin d → ℝ) → ℝ) (i : Fin d) (q : Site d) : ℝ :=
  Elliptic.partialDeriv i v (physical ε q)

/-- The approximate solution `w^ε = ū⁰ + ∑ᵢ bᵢ φᵢ` of (e.weps). -/
def approxSolution (ε : ℝ) (U : Set (Fin d → ℝ)) (v : (Fin d → ℝ) → ℝ)
    (φ : Fin d → Site d → ℝ) (q : Site d) : ℝ :=
  zeroExtension ε U v q + ∑ i, gradientCoeff ε v i q * φ i q

/-- The boundary defect `r = ũ − ū⁰` of (e.rdef) at the lattice sites. -/
def exteriorDefect (ε : ℝ) (U : Set (Fin d → ℝ)) (v : (Fin d → ℝ) → ℝ) (q : Site d) : ℝ :=
  v (physical ε q) - zeroExtension ε U v q

/-- The smooth error `E_{1,sm}` of (e.E1sm.def). -/
def smoothError (ε : ℝ) (a : Edge d → ℝ) (μ : ℝ) (f v : (Fin d → ℝ) → ℝ) (q : Site d) : ℝ :=
  (f (physical ε q) - μ * v (physical ε q)) + ε ^ d / kappa d ε * ∑' w : Site d,
    if hw : w = 0 then 0 else a (edgeAdd q w hw) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)

/-- The corrector error `E₂` of (e.E2.def). -/
def correctorError (ε : ℝ) (a : Edge d → ℝ) (v : (Fin d → ℝ) → ℝ)
    (φ : Fin d → Site d → ℝ) (q : Site d) : ℝ :=
  ε ^ d / kappa d ε * ∑' w : Site d, if hw : w = 0 then 0 else
    a (edgeAdd q w hw) * jumpKernel (physical ε w) *
      ∑ i, (gradientCoeff ε v i (q + w) - gradientCoeff ε v i q) * φ i (q + w)

/-- The mean-zero fluctuation `𝓕₁` of the smooth error (Step 6): the conductances replaced by
their deviation from the background coefficient `m`. -/
def smoothFluctuation (ε : ℝ) (a : Edge d → ℝ) (m : ℝ) (v : (Fin d → ℝ) → ℝ) (q : Site d) : ℝ :=
  ε ^ d / kappa d ε * ∑' w : Site d, if hw : w = 0 then 0 else
    (a (edgeAdd q w hw) - m) * jumpKernel (physical ε w) *
      smoothRemainder v (physical ε q) (physical ε w)

end

end LongRange
