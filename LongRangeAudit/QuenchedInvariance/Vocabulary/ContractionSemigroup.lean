import LongRangeAudit.QuenchedInvariance.Vocabulary.CadlagChainPathLaw

/-! # Independent ContractionSemigroup vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# Strongly continuous contraction semigroups and varying-space approximation

Strongly continuous contraction semigroups on real Banach spaces, their generators as exact
right-derivative graphs (Ethier–Kurtz, *Markov Processes* (1986), (1.1.10)), cores (§1.3), and the
convergence conventions of §1.6 for semigroups acting on a sequence of Banach spaces `L n` linked
to `L` by bounded linear maps `π n`. The identity semigroup is a worked example.
-/

namespace LatticeProb.ContractionSemigroup


open Filter Topology
open scoped NNReal

/-- A contraction semigroup with continuous orbits on nonnegative real time.
Orbit continuity is EK Corollary 1.2's equivalent form of continuity at zero. -/
structure StronglyContinuousContractionSemigroup (L : Type*)
    [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L] where
  operator : ℝ≥0 → L →L[ℝ] L
  map_zero : operator 0 = ContinuousLinearMap.id ℝ L
  map_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  norm_le_one : ∀ t, ‖operator t‖ ≤ 1
  continuous_orbit : ∀ f, Continuous (fun t => operator t f)

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]

/-- The generator graph: `(f,g)` belongs exactly when the right difference quotient
converges to `g`, as in EK (1.10), printed p.8. -/
def generatorGraph (T : StronglyContinuousContractionSemigroup L) : Set (L × L) :=
  {p | Tendsto (fun t : ℝ => t⁻¹ • (T.operator ⟨max t 0, le_max_right t 0⟩ p.1 - p.1))
    (𝓝[>] (0 : ℝ)) (𝓝 p.2)}

/-- The generator domain consists of exactly the vectors admitting a derivative value. -/
def generatorDomain (T : StronglyContinuousContractionSemigroup L) : Set L :=
  {f | ∃ g, (f, g) ∈ generatorGraph T}

/-- A right derivative has a unique value, so the graph represents a partial operator. -/
theorem generatorGraph_unique (T : StronglyContinuousContractionSemigroup L)
    {f g h : L} (hg : (f, g) ∈ generatorGraph T)
    (hh : (f, h) ∈ generatorGraph T) : g = h :=
  tendsto_nhds_unique hg hh

/-- A subspace of the generator domain is a core when its restricted graph has closure
exactly the generator graph (EK §1.3, printed p.17). -/
def IsCore (T : StronglyContinuousContractionSemigroup L) (D : Submodule ℝ L) : Prop :=
  (∀ f ∈ D, f ∈ generatorDomain T) ∧
    closure {p : L × L | p.1 ∈ D ∧ p ∈ generatorGraph T} = generatorGraph T

variable {Ln : ℕ → Type*}
  [∀ n, NormedAddCommGroup (Ln n)] [∀ n, NormedSpace ℝ (Ln n)]
  [∀ n, CompleteSpace (Ln n)]

/-- EK §1.6 convergence convention, expressed as convergence of real norm errors. -/
def VaryingConverges (π : ∀ n, L →L[ℝ] Ln n) (fn : ∀ n, Ln n) (f : L) : Prop :=
  Tendsto (fun n => ‖fn n - π n f‖) atTop (𝓝 0)

/-- Condition (c): approximate each core graph pair by actual discrete generator pairs. -/
def GraphApproximation (π : ∀ n, L →L[ℝ] Ln n)
    (T : StronglyContinuousContractionSemigroup L)
    (Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n))
    (D : Submodule ℝ L) : Prop :=
  ∀ f ∈ D, ∀ g, (f, g) ∈ generatorGraph T →
    ∃ (fn : ∀ n, Ln n) (gn : ∀ n, Ln n),
      (∀ n, (fn n, gn n) ∈ generatorGraph (Tn n)) ∧
      VaryingConverges π fn f ∧ VaryingConverges π gn g

/-- Condition (a): uniform strong convergence on every bounded nonnegative time interval.
The epsilon formulation avoids a supremum convention for empty intervals. -/
def UniformSemigroupConvergence (π : ∀ n, L →L[ℝ] Ln n)
    (T : StronglyContinuousContractionSemigroup L)
    (Tn : ∀ n, StronglyContinuousContractionSemigroup (Ln n)) : Prop :=
  ∀ f : L, ∀ b : ℝ≥0, ∀ δ : ℝ, 0 < δ →
    ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ b →
      ‖(Tn n).operator t (π n f) - π n (T.operator t f)‖ < δ

end LatticeProb.ContractionSemigroup

end LongRangeAudit.QuenchedInvariance
