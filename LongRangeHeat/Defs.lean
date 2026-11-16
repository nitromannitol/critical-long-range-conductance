import LongRange.Model.Operator
import LongRange.Model.Energy
import LatticeProb.Analysis.HeatKernel
import Mathlib.Probability.Independence.Basic

/-!
# Notation of the heat-kernel version

This file fixes the objects of the heat-kernel version of the critical long-range paper that
are shared by its statements. Points of `εℤ^d` are written `ε q` with an integer site `q`, as in
`LongRange.Model`. The operator `L^ε` of (1.2) is `LongRange.generator`, the normalization `κ_ε`
of (1.1) is `LongRange.kappa`, the jump kernel `J` is `LongRange.jumpKernel`, and the Dirichlet
form `B_a` of (2.4) is `LongRange.bilinForm`.

* `ConductanceLaw P lam a`: the standing assumptions on the conductances (independent, with
  values in `[λ, λ⁻¹]` and mean one; not necessarily identically distributed).
* `latticeInner`, `latticeNormSq`, `latticeNorm`: the rescaled `L²(εℤ^d)` pairing and norm (1.5).
* `discreteDeriv`, `gradNormSq`: the nearest-neighbor derivative `D_i` and energy `‖Dv‖²`.
* `meanGenerator`: the mean operator `L̄` of (3.1), every conductance replaced by `1`.
* `IsOq P q X A`: the relation `X ≤ 𝒪_q(A)` of (1.6) and its variant `𝒪₁`.
* `continuumHeat f t x`: the solution `ū` of (1.4), the convolution with the heat kernel of
  `(2d)⁻¹ Δ`.
* `latticeHeat ε a f t`: the solution `u_ε(t, ·) = e^{t L^ε} f` of (1.3), the exponential series.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LongRange LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Heat (heatKernel)

noncomputable section

variable {d : ℕ}

/-- The standing assumptions on the conductances: a probability measure `P` and a random field
`a` indexed by the unordered pairs of distinct sites, whose coordinates are measurable,
independent, take values in `[λ, λ⁻¹]` and have mean one. -/
structure ConductanceLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ)
    (a : Ω → Edge d → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  lam_mem : lam ∈ Set.Ioc (0 : ℝ) 1
  measurable : ∀ e, Measurable fun ω => a ω e
  indep : iIndepFun (fun e ω => a ω e) P
  bounds : ∀ ω e, lam ≤ a ω e ∧ a ω e ≤ lam⁻¹
  mean_one : ∀ e, ∫ ω, a ω e ∂P = 1

/-- The restriction of a function on `ℝ^d` to `εℤ^d`, indexed by integer sites. -/
def restrict (ε : ℝ) (f : (Fin d → ℝ) → ℝ) (q : Site d) : ℝ :=
  f (physical ε q)

/-- The pairing `⟨v₁, v₂⟩ = ε^d ∑_{x ∈ εℤ^d} v₁(x) v₂(x)`. -/
def latticeInner (ε : ℝ) (v₁ v₂ : Site d → ℝ) : ℝ :=
  ε ^ d * ∑' q, v₁ q * v₂ q

/-- The square `ε^d ∑_{x ∈ εℤ^d} |v(x)|²` of the rescaled norm (1.5). -/
def latticeNormSq (ε : ℝ) (v : Site d → ℝ) : ℝ :=
  ε ^ d * ∑' q, v q ^ 2

/-- The rescaled norm `‖v‖_{L²(εℤ^d)}` of (1.5). -/
def latticeNorm (ε : ℝ) (v : Site d → ℝ) : ℝ :=
  Real.sqrt (latticeNormSq ε v)

/-- Membership in `L²(εℤ^d)`: the squares are summable. -/
def MemL2 (v : Site d → ℝ) : Prop :=
  Summable fun q => v q ^ 2

/-- The discrete derivative `D_i v(x) = (v(x + ε e_i) - v(x)) / ε`. -/
def discreteDeriv (ε : ℝ) (i : Fin d) (v : Site d → ℝ) (q : Site d) : ℝ :=
  (v (q + Pi.single i 1) - v q) / ε

/-- The nearest-neighbor energy `‖D v‖² = ∑_i ‖D_i v‖²`. -/
def gradNormSq (ε : ℝ) (v : Site d → ℝ) : ℝ :=
  ∑ i, latticeNormSq ε (discreteDeriv ε i v)

/-- The mean operator `L̄` of (3.1): the operator (1.2) with every conductance equal to `1`. -/
def meanGenerator (ε : ℝ) (v : Site d → ℝ) (q : Site d) : ℝ :=
  generator ε (fun _ => 1) v q

/-- `X ≤ 𝒪_q(A)`: `X` is almost everywhere measurable and
`𝔼[exp((max(X, 0) / A)^q)] ≤ 2`. For `q = 2` this is (1.6), for `q = 1` its variant. -/
def IsOq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q : ℕ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  AEMeasurable X P ∧ ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / A) ^ q)) ∂P ≤ 2

/-- The solution `ū` of the continuum heat equation (1.4): `ū(0, ·) = f` and, for `t > 0`,
`ū(t, x) = ∫ Φ_t(x - y) f(y) dy` with the heat kernel `Φ_t` of `(2d)⁻¹ Δ`. -/
def continuumHeat (f : (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  if t = 0 then f x else ∫ y, heatKernel d t (x - y) * f y

/-- The solution `u_ε(t, ·) = e^{t L^ε} f` of the lattice heat equation (1.3), given by the
exponential series `∑_n tⁿ (L^ε)ⁿ f / n!` applied to the restriction of `f` to `εℤ^d`. -/
def latticeHeat (ε : ℝ) (a : Edge d → ℝ) (f : (Fin d → ℝ) → ℝ) (t : ℝ) (q : Site d) : ℝ :=
  ∑' n : ℕ, t ^ n / (n.factorial : ℝ) * (generator ε a)^[n] (restrict ε f) q

end

end LongRangeHeat
