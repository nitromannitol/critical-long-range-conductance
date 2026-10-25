import LongRange.Dirichlet.Young
import LatticeProb.Analysis.AntisymmetricPairing

/-!
# Delta tests characterize solenoidal fields

For the paper's antisymmetric fields with absolutely summable local rows, the pairing
with every supported test vanishes exactly when every local divergence vanishes.
The pairing is the unnormalized source pairing: a unit delta test gives minus twice
the row sum. Boundedness makes all supported tests finitely supported.
-/

namespace LongRange

open Classical LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Antisymmetry forces the diagonal contribution, omitted in the source divergence, to vanish. -/
theorem antisymmetric_diagonal_eq_zero (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d) : g x x = 0 := by
  exact LatticeProb.AntisymmetricPairing.antisymmetric_diagonal_eq_zero g hanti x

/-- Including the zero displacement leaves the source divergence unchanged. -/
theorem antisymmetric_tsum_nonzero (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d) :
    (∑' z : {z : Site d // z ≠ 0}, g (x + z) x) = ∑' z, g (x + z) x := by
  exact LatticeProb.AntisymmetricPairing.antisymmetric_tsum_nonzero g hanti x

/-- Absolute convergence of the source row excluding zero is equivalent to convergence
of the full row, since antisymmetry kills the diagonal. -/
theorem antisymmetric_summable_nonzero_iff (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d) :
    Summable (fun z : {z : Site d // z ≠ 0} => g (x + z) x) ↔
      Summable (fun z => g (x + z) x) := by
  exact LatticeProb.AntisymmetricPairing.antisymmetric_summable_nonzero_iff g hanti x

/-- A supported test in a finite lattice domain has finite support. -/
theorem SupportedIn.hasFiniteSupport_of_finite_latticeSet {ε : ℝ} {U : Set (Fin d → ℝ)}
    {w : Site d → ℝ} (hw : SupportedIn ε U w) (hU : (latticeSet ε U).Finite) :
    Function.HasFiniteSupport w := by
  apply hU.subset
  intro x hx
  by_contra h
  exact hx (hw x h)

/-- Antisymmetry and local row summability suffice for pairing summability and summation
by parts against every finite test. This generic identity includes the factor two. -/
theorem antisymmetric_pairing_eq (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) {w : Site d → ℝ}
    (hw : Function.HasFiniteSupport w)
    (hrow : ∀ x ∈ Function.support w, Summable (fun z => g (x + z) x)) :
    Summable (fun q : Site d × Site d =>
      g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) ∧
      (∑' q : Site d × Site d,
        g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) =
        -2 * ∑' x, (∑' z, g (x + z) x) * w x := by
  exact LatticeProb.AntisymmetricPairing.antisymmetric_pairing_eq g hanti hw hrow

/-- The unit delta test at an integer lattice site. -/
def deltaTest (x : Site d) (y : Site d) : ℝ := if y = x then 1 else 0

/-- A delta test has support exactly its distinguished singleton. -/
theorem support_deltaTest (x : Site d) : Function.support (deltaTest x) = {x} := by
  exact LatticeProb.AntisymmetricPairing.support_deltaTest x

/-- Delta tests are finitely supported. -/
theorem hasFiniteSupport_deltaTest (x : Site d) :
    Function.HasFiniteSupport (deltaTest x) := by
  exact LatticeProb.AntisymmetricPairing.hasFiniteSupport_deltaTest x

/-- Every site in the domain supplies an admissible source delta test. -/
theorem supportedIn_deltaTest {ε : ℝ} {U : Set (Fin d → ℝ)} {x : Site d}
    (hx : x ∈ latticeSet ε U) : SupportedIn ε U (deltaTest x) := by
  intro y hy
  change (if y = x then (1 : ℝ) else 0) = 0
  exact if_neg (fun h : y = x => hy (h.symm ▸ hx))

/-- Pairing with a unit delta gives minus twice the absolutely convergent divergence row. -/
theorem antisymmetric_pairing_deltaTest (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d)
    (hrow : Summable (fun z => g (x + z) x)) :
    Summable (fun q : Site d × Site d =>
      g (q.1 + q.2) q.1 * (deltaTest x (q.1 + q.2) - deltaTest x q.1)) ∧
      (∑' q : Site d × Site d,
        g (q.1 + q.2) q.1 * (deltaTest x (q.1 + q.2) - deltaTest x q.1)) =
        -2 * ∑' z, g (x + z) x := by
  exact LatticeProb.AntisymmetricPairing.antisymmetric_pairing_deltaTest g hanti x hrow

/-- The full source test class detects pointwise solenoidality. Local absolute row
summability is a standing assumption; absolute pairing summability is a consequence. -/
theorem solenoidal_iff_pairing_eq_zero {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hfinite : (latticeSet ε U).Finite) (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x)
    (hrow : ∀ x ∈ latticeSet ε U, Summable (fun z => g (x + z) x)) :
    (∀ x ∈ latticeSet ε U, (∑' z, g (x + z) x) = 0) ↔
      (∀ w : Site d → ℝ, SupportedIn ε U w →
        (∑' q : Site d × Site d,
          g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) = 0) := by
  constructor
  · intro hsol w hw
    have hpair := antisymmetric_pairing_eq g hanti
      (hw.hasFiniteSupport_of_finite_latticeSet hfinite) (by
        intro x hx
        apply hrow x
        by_contra h
        exact hx (hw x h))
    rw [hpair.2]
    have hz (x : Site d) : (∑' z, g (x + z) x) * w x = 0 := by
      by_cases hx : x ∈ latticeSet ε U
      · rw [hsol x hx, zero_mul]
      · rw [hw x hx, mul_zero]
    simp only [hz, tsum_zero, mul_zero]
  · intro hweak x hx
    have hdelta := (antisymmetric_pairing_deltaTest g hanti x (hrow x hx)).2
    rw [hweak (deltaTest x) (supportedIn_deltaTest hx)] at hdelta
    linarith

/-- Every supported source test has an absolutely convergent pairing, independently of
whether the field is solenoidal. -/
theorem summable_antisymmetric_pairing {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hfinite : (latticeSet ε U).Finite) (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x)
    (hrow : ∀ x ∈ latticeSet ε U, Summable (fun z => g (x + z) x))
    {w : Site d → ℝ} (hw : SupportedIn ε U w) :
    Summable (fun q : Site d × Site d =>
      g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) := by
  apply (antisymmetric_pairing_eq g hanti (hw.hasFiniteSupport_of_finite_latticeSet hfinite) ?_).1
  intro x hx
  apply hrow x
  by_contra h
  exact hx (hw x h)

/-- The source equivalence on a bounded physical domain at positive lattice spacing,
with no restriction on the supported test family and no pairing summability premise. -/
theorem solenoidal_iff_pairing_eq_zero_bounded {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (g : Site d → Site d → ℝ) (hanti : ∀ x y, g x y = -g y x)
    (hrow : ∀ x ∈ latticeSet ε U, Summable (fun z => g (x + z) x)) :
    (∀ x ∈ latticeSet ε U, (∑' z, g (x + z) x) = 0) ↔
      (∀ w : Site d → ℝ, SupportedIn ε U w →
        (∑' q : Site d × Site d,
          g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) = 0) :=
  solenoidal_iff_pairing_eq_zero (latticeSet_finite hε hU) g hanti hrow

/-- The source statement with the zero displacement literally omitted from divergence. -/
theorem solenoidal_nonzero_iff_pairing_eq_zero {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (g : Site d → Site d → ℝ) (hanti : ∀ x y, g x y = -g y x)
    (hrow : ∀ x ∈ latticeSet ε U, Summable (fun z : {z : Site d // z ≠ 0} => g (x + z) x)) :
    (∀ x ∈ latticeSet ε U, (∑' z : {z : Site d // z ≠ 0}, g (x + z) x) = 0) ↔
      (∀ w : Site d → ℝ, SupportedIn ε U w →
        (∑' q : Site d × Site d,
          g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) = 0) := by
  simp_rw [antisymmetric_tsum_nonzero g hanti]
  exact solenoidal_iff_pairing_eq_zero_bounded hε hU g hanti
    (fun x hx => (antisymmetric_summable_nonzero_iff g hanti x).mp (hrow x hx))

/-- The genuine zero field has summable zero divergence and zero pairing with every test. -/
theorem zeroField_solenoidal_and_pairing (w : Site d → ℝ) :
    (∀ _ : Site d, Summable (fun _ : Site d => (0 : ℝ)) ∧
      (∑' _ : Site d, (0 : ℝ)) = 0) ∧
    Summable (fun q : Site d × Site d =>
      (0 : ℝ) * (w (q.1 + q.2) - w q.1)) ∧
      (∑' q : Site d × Site d, (0 : ℝ) * (w (q.1 + q.2) - w q.1)) = 0 := by
  simp only [zero_mul, tsum_zero, and_true]
  exact ⟨fun _ => summable_zero, summable_zero⟩

/-- Translation of a delta test shifts its distinguished site by the opposite amount. -/
theorem deltaTest_add (a x z : Site d) : deltaTest a (x + z) = deltaTest (a - x) z := by
  exact LatticeProb.AntisymmetricPairing.deltaTest_add a x z

/-- A unit delta has total mass one. -/
theorem tsum_deltaTest (x : Site d) : (∑' y, deltaTest x y) = 1 := by
  exact LatticeProb.AntisymmetricPairing.tsum_deltaTest x

/-- The antisymmetric unit edge oriented from `a` to `b`. -/
def singleEdgeField (a b x y : Site d) : ℝ :=
  deltaTest b x * deltaTest a y - deltaTest a x * deltaTest b y

/-- The unit edge field obeys the literal source antisymmetry convention. -/
theorem singleEdgeField_antisymmetric (a b x y : Site d) :
    singleEdgeField a b x y = -singleEdgeField a b y x := by
  exact LatticeProb.AntisymmetricPairing.singleEdgeField_antisymmetric a b x y

/-- The unit edge field is supported on its two orientations. -/
theorem hasFiniteSupport_singleEdgeField (a b : Site d) :
    Function.HasFiniteSupport (fun q : Site d × Site d => singleEdgeField a b q.1 q.2) := by
  exact LatticeProb.AntisymmetricPairing.hasFiniteSupport_singleEdgeField a b

/-- Every row of a unit edge field is absolutely summable, with divergence equal to
one at its initial site and minus one at its terminal site. -/
theorem singleEdgeField_row (a b x : Site d) :
    Summable (fun z => singleEdgeField a b (x + z) x) ∧
      (∑' z, singleEdgeField a b (x + z) x) = deltaTest a x - deltaTest b x := by
  exact LatticeProb.AntisymmetricPairing.singleEdgeField_row a b x

/-- A nontrivial unit edge is not solenoidal, and its delta pairing is exactly minus two. -/
theorem singleEdgeField_not_solenoidal {a b : Site d} (hab : a ≠ b) :
    (∑' z, singleEdgeField a b (a + z) a) = 1 ∧
      (∑' q : Site d × Site d,
        singleEdgeField a b (q.1 + q.2) q.1 *
          (deltaTest a (q.1 + q.2) - deltaTest a q.1)) = -2 := by
  exact LatticeProb.AntisymmetricPairing.singleEdgeField_not_solenoidal hab


end

end LongRange
