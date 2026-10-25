import LongRangeAudit.QuenchedInvariance.Vocabulary.EuclideanSummability

/-! # Independent Elliptic vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance
noncomputable section
open scoped BigOperators ENNReal Topology
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

end
end LongRangeAudit.QuenchedInvariance
