import Mathlib

/-!
# Quantitative homogenization of the weak Dirichlet solution

Independent vocabulary for Theorem 1.1. Spatial radii and Hölder distances are Euclidean.
The zero-boundary Sobolev carrier is the literal closure of compactly supported smooth graphs.
The seven cited Gilbarg–Trudinger inputs are fully expanded propositions, explicit hypotheses.
Constants precede every probability law, conductance field and datum. The unique weak solution
and its unique continuous classical representative are produced in the conclusion.
-/

namespace LongRangeAudit.QuantitativeHomogenization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Topology

namespace LatticeProb

variable {d : ℕ}

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

theorem unit_ne_zero {d : ℕ} (i : Fin d) : unit i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unit, Pi.single_eq_same] at this

end LatticeProb

namespace LatticeProb.Euclidean.Lattice

variable {d : ℕ}

/-- The physical point `ε z` of the scaled lattice, with coordinates `ε z_k`. -/
def physical {d : ℕ} (ε : ℝ) (z : Site d) : Fin d → ℝ :=
  fun k => ε * (z k : ℝ)

/-- The Euclidean radius `√(∑ v_k²)` of a real vector `v : Fin d → ℝ`; it is not the Pi sup-norm. -/
def radius {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ k, (v k) ^ 2)

/-- The finite box of integer indices with `|z_k| ≤ ⌈1/ε⌉` in every coordinate.  At `ε = 0` the
junk value `1/ε = 0` of Lean makes the box `{0}`, so `unitBallIndices` is empty there; every result
that uses the box carries `0 < ε` (or `1/R` with `R > 0`). -/
def cutoffBox (d : ℕ) (ε : ℝ) : Finset (Site d) :=
  Fintype.piFinset (fun _ => Finset.Icc (-⌈1 / ε⌉) ⌈1 / ε⌉)

/-- The nonzero integer indices of `cutoffBox d ε` whose physical point `ε z` lies in the closed
Euclidean unit ball. -/
def unitBallIndices (d : ℕ) (ε : ℝ) : Finset (Site d) :=
  (cutoffBox d ε).filter (fun z => z ≠ 0 ∧ radius (physical ε z) ≤ 1)

end LatticeProb.Euclidean.Lattice

namespace LatticeProb.Elliptic
open LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The supremum of the absolute value on `S`, with infinity allowed. -/
def supNorm (S : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ S, ENNReal.ofReal |f x|

/-- The scalar Hölder seminorm with Euclidean distance and exponent `σ`. -/
def holderSeminorm (σ : ℝ) (S : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ S, ⨆ y ∈ S, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (|f x - f y| / radius (x - y) ^ σ)

/-- The sum of the supremum norm and the Euclidean Hölder seminorm. -/
def c0HolderNorm (σ : ℝ) (S : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  supNorm S f + holderSeminorm σ S f

/-- The coordinate derivative in the direction of the `i`th standard basis vector. -/
def partialDeriv (i : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The second coordinate derivative, evaluated using the iterated Fréchet derivative. -/
def secondPartial (i j : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1]

/-- The coordinate trace of the Hessian, giving the Euclidean Laplacian. -/
def laplacian (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, secondPartial i i f x

/-- The coordinate `C^{2,σ}` norm, summing all first and second coordinate derivatives. -/
def c2HolderNorm (σ : ℝ) (S : Set (Fin d → ℝ))
    (u : (Fin d → ℝ) → ℝ) : ℝ≥0∞ :=
  supNorm S u + ∑ i, supNorm S (partialDeriv i u) +
    ∑ i, ∑ j, supNorm S (secondPartial i j u) +
    ∑ i, ∑ j, holderSeminorm σ S (secondPartial i j u)

end LatticeProb.Elliptic

namespace LatticeProb.Elliptic
open LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- A bounded domain with `C^{2,σ}` boundary, through a defining function. -/
def IsC2HolderDomain (σ : ℝ) (U : Set (Fin d → ℝ)) : Prop :=
  IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
    ∃ ρ : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 ρ ∧
      (∀ R : ℝ, c2HolderNorm σ {x | radius x < R} ρ < ⊤) ∧
      U = {x | ρ x < 0} ∧ ∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0

end LatticeProb.Elliptic

namespace LatticeProb.Elliptic

variable {d : ℕ}

/-- `u` is a classical solution of `μ u − a₀ Δ u = f` in `U`, `u = 0` on `∂U`. -/
def IsClassicalDirichletSolution (U : Set (Fin d → ℝ)) (μ a₀ : ℝ)
    (f u : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ContinuousOn u (closure U) ∧
    (∀ x ∈ frontier U, u x = 0) ∧
    ∀ x ∈ U, μ * u x - a₀ * laplacian u x = f x

end LatticeProb.Elliptic

namespace LatticeProb.Elliptic.WeakDirichlet
open MeasureTheory
variable {d : ℕ}

/-- A real smooth function whose compact topological support lies inside `U`. -/
structure TestFunction (U : Set (Fin d → ℝ)) where
  val : (Fin d → ℝ) → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) val
  compact : HasCompactSupport val
  supported : tsupport val ⊆ U

/-- Differentiation preserves smoothness and compact support inside the domain. -/
def TestFunction.deriv {U : Set (Fin d → ℝ)} (φ : TestFunction U) (i : Fin d) :
    TestFunction U where
  val := partialDeriv i φ.val
  smooth := (φ.smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  compact := φ.compact.fderiv_apply ℝ (Pi.single i 1)
  supported := (tsupport_fderiv_apply_subset ℝ _).trans φ.supported

/-- Every smooth compactly supported test is genuinely square integrable on `U`. -/
theorem TestFunction.memLp {U : Set (Fin d → ℝ)} (φ : TestFunction U) :
    MemLp φ.val 2 (volume.restrict U) :=
  (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compact).mono_measure
    Measure.restrict_le_self

/-- The L² equivalence class of a test function, with no choice of representative. -/
def TestFunction.toL2 {U : Set (Fin d → ℝ)} (φ : TestFunction U) :
    Lp ℝ 2 (volume.restrict U) := φ.memLp.toLp φ.val

/-- One L² function coordinate together with `d` L² coordinates for derivatives.
The `PiLp 2` norm is the square root of the sum of the squared L² norms. -/
abbrev H1Product (U : Set (Fin d → ℝ)) :=
  PiLp 2 (fun _ : Fin (d + 1) => Lp ℝ 2 (volume.restrict U))

/-- The zeroth coordinate is the function; successor coordinates are its derivatives. -/
def TestFunction.graph {U : Set (Fin d → ℝ)} (φ : TestFunction U) : H1Product U :=
  WithLp.toLp 2 (Fin.cons φ.toL2 (fun i => (φ.deriv i).toL2))

/-- The literal H¹₀ graph: closure of actual smooth supported graphs in the H¹ norm.
No injection of its first coordinate or trace identification is asserted here. -/
def H10 (U : Set (Fin d → ℝ)) :=
  {v : H1Product U // v ∈ closure (Set.range (TestFunction.graph (U := U)))}

/-- Literal weak equation against every real smooth compactly supported test.
Integrability is part of the predicate, so the integral cannot use its undefined-case value. -/
def IsWeakSolution (U : Set (Fin d → ℝ)) (μ a₀ : ℝ)
    (f : (Fin d → ℝ) → ℝ) (u : H10 U) : Prop :=
  ∀ φ : TestFunction U,
    Integrable (fun x => μ * u.val 0 x * φ.val x +
      a₀ * ∑ i : Fin d, u.val i.succ x * (φ.deriv i).val x) (volume.restrict U) ∧
    Integrable (fun x => f x * φ.val x) (volume.restrict U) ∧
    (∫ x in U, μ * u.val 0 x * φ.val x +
      a₀ * ∑ i : Fin d, u.val i.succ x * (φ.deriv i).val x) =
      ∫ x in U, f x * φ.val x

end LatticeProb.Elliptic.WeakDirichlet

namespace LatticeProb.External
open MeasureTheory LatticeProb.Elliptic LatticeProb.Elliptic.WeakDirichlet
variable {d : ℕ}

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.19, printed p. 111,
with `k = 0`, zero boundary data, and operator `a₀ Δ − μ`; the theorem needs no sign on `c`.
The conclusion records the finite coordinate `C^{2,σ}` norm on the open domain. -/
def GilbargTrudingerBoundaryRegularity : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f u : (Fin d → ℝ) → ℝ),
          c0HolderNorm σ (closure U) f < ⊤ →
          IsClassicalDirichletSolution U μ a₀ f u → c2HolderNorm σ U u < ⊤

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.6, printed pp. 98–99,
for zero boundary data and constant operator `a₀ Δ − μ`, with `λ = Λ⁻¹` and the book's
`C(n, α, λ, Λ, Ω)` read as `C` depending on `d`, `σ`, `U`, `Λ` only: uniform in the
coefficients `a₀`, `μ`, the datum and the solution. Finite `C^{2,σ}` regularity is an a priori
hypothesis, supplied separately by Theorem 6.19. -/
def GilbargTrudingerSchauderEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (Λ : ℝ), 1 ≤ Λ → ∃ C : ℝ, 0 < C ∧
        ∀ (a₀ μ : ℝ), a₀ ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
          ∀ (f u : (Fin d → ℝ) → ℝ),
            c0HolderNorm σ (closure U) f < ⊤ →
            IsClassicalDirichletSolution U μ a₀ f u →
            c2HolderNorm σ U u < ⊤ →
            c2HolderNorm σ U u ≤
              ENNReal.ofReal C * (supNorm U u + c0HolderNorm σ (closure U) f)

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 3.7, printed p. 36,
equality case with zero boundary data, `b = 0`, and `c = −μ ≤ 0`.
The constant depends only on the bounded domain, uniformly in positive `a₀` and `μ ≥ 0`;
the minimum eigenvalue is `a₀`, giving exactly the factor `C / a₀`. -/
def GilbargTrudingerSupEstimate : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (U : Set (Fin d → ℝ)),
    IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ C : ℝ, 0 < C ∧ ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f u : (Fin d → ℝ) → ℝ), supNorm U f < ⊤ →
          IsClassicalDirichletSolution U μ a₀ f u →
          supNorm U u ≤ ENNReal.ofReal (C / a₀) * supNorm U f

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Lemma 6.37, printed
pp. 136–137, with `k = 2` and fixed `0 < σ < 1`; the book's `C(k, Ω, Ω')` is here allowed to
depend also on `σ`. A function with interior `C²` regularity and finite `C^{2,σ}` norm on
the domain extends to a compactly supported global `C²` function, supported inside the
prescribed open neighborhood of the closure. The bound is uniform in the function. -/
def GilbargTrudingerHolderExtension : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (U' : Set (Fin d → ℝ)), IsOpen U' → closure U ⊆ U' →
        ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin d → ℝ) → ℝ),
          ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
          ∃ v : (Fin d → ℝ) → ℝ,
            ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ tsupport v ⊆ U' ∧
              Set.EqOn v u U ∧
              c2HolderNorm σ U' v ≤ ENNReal.ofReal C * c2HolderNorm σ U u

end LatticeProb.External

namespace LatticeProb.External
open MeasureTheory LatticeProb.Elliptic LatticeProb.Elliptic.WeakDirichlet
variable {d : ℕ}

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.14, printed p. 107,
for operator `a₀ Δ − μ`, right side `−f` and zero boundary data. The conclusion retains
existence and finite interior coordinate norm; no uniqueness of total extensions is claimed. -/
def GilbargTrudingerExistence : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f : (Fin d → ℝ) → ℝ), c0HolderNorm σ (closure U) f < ⊤ →
          ∃ u : (Fin d → ℝ) → ℝ,
            IsClassicalDirichletSolution U μ a₀ f u ∧ c2HolderNorm σ U u < ⊤

end LatticeProb.External

namespace LatticeProb.External
open MeasureTheory LatticeProb.Elliptic LatticeProb.Elliptic.WeakDirichlet
variable {d : ℕ}

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics in Mathematics (2001), §7.5, printed p. 154, final paragraph before §7.6:
a W¹,² function vanishing continuously on the boundary belongs to W¹,²₀.
All coordinates are actual L² elements; the displayed identities assert every
coordinate weak derivative against every supported smooth test. Their integrals
are finite by `integrable_mul_test`. The connected open set is the book's domain;
no boundary smoothness is required. -/
def GilbargTrudingerZeroBoundaryApproximation : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (U : Set (Fin d → ℝ)),
    IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∀ (v : H1Product U),
        (∀ (ψ : TestFunction U) (i : Fin d),
          (∫ x in U, v 0 x * (ψ.deriv i).val x) =
            -(∫ x in U, v i.succ x * ψ.val x)) →
        ∀ (u : (Fin d → ℝ) → ℝ), ContinuousOn u (closure U) →
          Set.EqOn u (fun _ => 0) (frontier U) →
          (fun x => v 0 x) =ᵐ[volume.restrict U] u →
          v ∈ closure (Set.range (TestFunction.graph (U := U)))

/-- Gilbarg–Trudinger, same edition, Corollary 8.2, printed p. 180, with
(8.2)–(8.8), pp. 177–179: a homogeneous zero-boundary weak solution is zero
as a Sobolev element, hence in every coordinate of its Sobolev graph.
Strict ellipticity is `a₀ > 0`; the sign condition (8.8) is `−μ ≤ 0` and permits
`μ = 0`. The bounded constant coefficients satisfy (8.6). Smooth compactly
supported tests are used here. The continuous-functional argument (8.7), p. 178,
and the defining H¹₀ closure extend the equation to H¹₀ tests; this extension is
proved in `WeakDirichletAlgebra`. There is no existence or classical-solution claim. -/
def GilbargTrudingerWeakHomogeneousUniqueness : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (U : Set (Fin d → ℝ)),
    IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ → ∀ (u : H10 U),
        IsWeakSolution U μ a₀ (fun _ => 0) u → u.val = 0

end LatticeProb.External

namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The critical jump kernel `J(z) = |z|^{-(d+2)}` on `ℝ^d ∖ {0}`, with `J(0) = 0`, where `|z|`
is the Euclidean radius. -/
def jumpKernel (z : Fin d → ℝ) : ℝ :=
  if z = 0 then 0 else (radius z ^ (d + 2))⁻¹

/-- The normalization `κ_ε = ε^d ∑_{z ∈ εℤ^d ∖ {0}, |z| ≤ 1} |z|^{-d}`, written over the integer
indices `q` of the points `z = εq`. -/
def kappa (d : ℕ) (ε : ℝ) : ℝ :=
  ε ^ d * ∑ q ∈ unitBallIndices d ε, (radius (physical ε q) ^ d)⁻¹

end LongRange

namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The lattice set `U^ε = U ∩ εℤ^d`, as the integer sites `q` whose physical point `εq` lies
in `U`. -/
def latticeSet (ε : ℝ) (U : Set (Fin d → ℝ)) : Set (Site d) :=
  {q | physical ε q ∈ U}

/-- `h` is supported in `U^ε`: it vanishes at every lattice point outside `U`. -/
def SupportedIn (ε : ℝ) (U : Set (Fin d → ℝ)) (h : Site d → ℝ) : Prop :=
  ∀ q, q ∉ latticeSet ε U → h q = 0

/-- The squared discrete norm `‖g‖²_{L²(U^ε)} = ε^d ∑_{x ∈ U^ε} g(x)²`. -/
def l2NormSq (ε : ℝ) (U : Set (Fin d → ℝ)) (g : Site d → ℝ) : ℝ :=
  ε ^ d * ∑' q : latticeSet ε U, g q ^ 2

/-- The discrete norm `‖g‖_{L²(U^ε)}`. -/
def l2Norm (ε : ℝ) (U : Set (Fin d → ℝ)) (g : Site d → ℝ) : ℝ :=
  Real.sqrt (l2NormSq ε U g)

end LongRange

namespace LongRange
open MeasureTheory ProbabilityTheory LatticeProb
variable {d : ℕ}

/-- An unordered edge `{x, y}` with `x ≠ y` of the complete graph on `ℤ^d`. -/
abbrev Edge (d : ℕ) : Type := {e : Sym2 (Site d) // ¬ e.IsDiag}

/-- The unordered edge `{x, y}` for distinct sites `x ≠ y`. -/
def edge (x y : Site d) (h : x ≠ y) : Edge d :=
  ⟨s(x, y), by simpa [Sym2.mk_isDiag_iff] using h⟩

/-- The edge `{q, q + w}` for a nonzero increment `w`. -/
def edgeAdd (q w : Site d) (hw : w ≠ 0) : Edge d :=
  edge q (q + w) (by simpa using fun h : q = q + w => hw (by simpa using h.symm))

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

end LongRange

namespace LongRange
open LatticeProb LatticeProb.Euclidean.Lattice
variable {d : ℕ}

/-- The rescaled operator `L^ε h` evaluated at the physical point `εq`. -/
def generator (ε : ℝ) (a : Edge d → ℝ) (h : Site d → ℝ) (q : Site d) : ℝ :=
  ε ^ d / kappa d ε * ∑' w : Site d,
    if hw : w = 0 then 0
    else a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w)

end LongRange

end

end LongRangeAudit.QuantitativeHomogenization
