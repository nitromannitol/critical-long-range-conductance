import LongRange.Model.Kernel

/-!
# Lattice sets, supports and discrete norms on `εℤ^d`

For `U ⊆ ℝ^d`, the paper writes `U^ε = U ∩ εℤ^d`; here it is the set `latticeSet ε U` of integer
sites `q` with `εq ∈ U`.  A function `h : εℤ^d → ℝ` is supported in `U^ε` when it vanishes at
every lattice point outside `U`.  The discrete `L²` norm is
`‖g‖²_{L²(U^ε)} = ε^d ∑_{x ∈ U^ε} g(x)²`, and `ℓ_p(x) = p · x` is the linear function of slope
`p` evaluated at the physical point `x = εq`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

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

/-- The linear function `ℓ_p(x) = p · x` at the physical point `x = εq`. -/
def linearFn (ε : ℝ) (p : Fin d → ℝ) (q : Site d) : ℝ :=
  ∑ i, p i * physical ε q i

/-- Membership in `latticeSet` is membership of the physical point in `U`. -/
theorem mem_latticeSet {ε : ℝ} {U : Set (Fin d → ℝ)} {q : Site d} :
    q ∈ latticeSet ε U ↔ physical ε q ∈ U :=
  Iff.rfl

end

end LongRange
