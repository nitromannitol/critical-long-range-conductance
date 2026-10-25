import LongRange.Model.Operator
import LongRange.Model.CorrectorEnergy

/-!
# The first-order corrector (Definition 3.1, (eq:elleqdefnu))

The corrector `φ_p^ε` is the minimizer of the functional (e.nu) over functions supported in
`U^ε`, equivalently the solution of `L^ε(ℓ_p + φ) = 0` in `U^ε` with `φ = 0` outside. Both
characterizations are recorded as predicates; existence, uniqueness and their equivalence are
theorems (`LongRange.corrector_wellDefined`).
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

variable {d : ℕ}

/-- `φ` minimizes the corrector functional (e.nu) among functions supported in `U^ε`. -/
def IsCorrectorMinimizer (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (φ : Site d → ℝ) : Prop :=
  SupportedIn ε U φ ∧ ∀ w, SupportedIn ε U w →
    correctorFunctional ε U a p φ ≤ correctorFunctional ε U a p w

/-- `φ` solves the corrector equation (eq:elleqdefnu): `L^ε(ℓ_p + φ) = 0` in `U^ε` and `φ = 0`
outside `U^ε`. -/
def IsCorrectorSolution (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (φ : Site d → ℝ) : Prop :=
  SupportedIn ε U φ ∧
    ∀ q ∈ latticeSet ε U, generator ε a (fun x => linearFn ε p x + φ x) q = 0

end LongRange
