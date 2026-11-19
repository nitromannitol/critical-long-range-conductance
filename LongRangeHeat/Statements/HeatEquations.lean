import LongRangeHeat.LatticeSemigroup
import LongRangeHeat.MeanOperator

/-!
# The lattice and continuum heat equations

Characterizations of the two solutions compared in Theorem 1.1. The lattice solution
`u_ε = latticeHeat ε a f` of (1.3) is defined by the exponential series `∑ₙ tⁿ (L^ε)ⁿ f / n!`,
and the continuum solution `ū = continuumHeat f` of (1.4) by convolution with the heat kernel of
`(2d)⁻¹ Δ`. The theorems below state that the series converges, that both functions solve
their equations with the given initial data, and that the lattice solution is the only bounded
classical solution.
-/

namespace LongRangeHeat.Statements

open Set LongRange LatticeProb LatticeProb.Euclidean.Lattice
open scoped ContDiff

/-- **The lattice heat equation (1.3).** Let `d ≥ 1`, `ε > 0`, `λ > 0`, let `a` be a conductance
field with values in `[λ, λ⁻¹]` and let `f` be continuous with compact support. Then

* the exponential series defining `u_ε(t, q)` converges at every time `t` and site `q`;
* `u_ε(0, ·)` is the restriction of `f` to `εℤ^d`;
* `∂_t u_ε(t, q) = L^ε u_ε(t, ·)(q)` at every time `t` and site `q`, and for `t ≥ 0` the series
  defining `L^ε u_ε(t, ·)(q)` converges absolutely;
* `u_ε` is bounded on `[0, T] × εℤ^d` for every `T`;
* every function that is bounded on each `[0, T] × εℤ^d`, continuous in time on `[0, ∞)`,
  equal to the restriction of `f` at time `0`, and that solves `∂_t u = L^ε u` at positive times
  agrees with `u_ε` at all times `t ≥ 0`. -/
theorem lattice_heat_equation {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∀ (t : ℝ) (q : Site d), Summable (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
      (generator ε a)^[n] (restrict ε f) q)) ∧
    latticeHeat ε a f 0 = restrict ε f ∧
    (∀ (t : ℝ) (q : Site d), HasDerivAt (fun s => latticeHeat ε a f s q)
      (generator ε a (latticeHeat ε a f t) q) t) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ q : Site d, Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (latticeHeat ε a f t (q + w) - latticeHeat ε a f t q) *
        jumpKernel (physical ε w))) ∧
    (∀ T : ℝ, ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ q : Site d, |latticeHeat ε a f t q| ≤ C) ∧
    (∀ u : ℝ → Site d → ℝ, (∀ q, u 0 q = restrict ε f q) →
      (∀ T : ℝ, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ q, |u t q| ≤ M) →
      (∀ q, ContinuousOn (fun t => u t q) (Ici 0)) →
      (∀ t ∈ Ioi (0 : ℝ), ∀ q, HasDerivAt (fun s => u s q) (generator ε a (u t) q) t) →
      ∀ t ∈ Ici (0 : ℝ), ∀ q, u t q = latticeHeat ε a f t q) := by
  refine ⟨summable_latticeHeat hd hε hlam ha hf hfc, latticeHeat_zero ε a f,
    hasDerivAt_latticeHeat hd hε hlam ha hfc, fun t ht q => ?_,
    latticeHeat_bounded_on_interval hd hε hlam ha hf hfc,
    fun u hu0 huB huC huD => latticeHeat_unique hd hε hlam ha hf hfc u hu0 huB huC huD⟩
  obtain ⟨C, hC⟩ := latticeHeat_bounded_on_interval hd hε hlam ha hf hfc t
  have hbound : ∀ p, |latticeHeat ε a f t p| ≤ C := hC t ⟨ht, le_rfl⟩
  exact summable_generator_of_bounded hd hε hlam ha ((abs_nonneg _).trans (hbound q)) hbound q

/-- **The continuum heat equation (1.4).** Let `d ≥ 1` and `f ∈ C_c^∞(ℝ^d)`. Then
`ū(0, ·) = f`; for every `t ≥ 0`, `ū(t, ·)` is smooth; for every `t > 0` and `x`,
`∂_t ū(t, x) = (2d)⁻¹ Δ ū(t, x)`; and for every `t ≥ 0` and `x` the right time derivative exists
and equals `(2d)⁻¹ Δ ū(t, x)`, so that the derivative `derivWithin` of Lemma 3.1 is this right
derivative. Here `LatticeProb.WhiteNoise.contOp d g = (2d)⁻¹ Δ g`. -/
theorem continuum_heat_equation {d : ℕ} (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    continuumHeat f 0 = f ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ ∞ (continuumHeat f t)) ∧
    (∀ t : ℝ, 0 < t → ∀ x : Fin d → ℝ, HasDerivAt (fun s => continuumHeat f s x)
      (LatticeProb.WhiteNoise.contOp d (continuumHeat f t) x) t) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ x : Fin d → ℝ,
      HasDerivWithinAt (fun s => continuumHeat f s x)
        (LatticeProb.WhiteNoise.contOp d (continuumHeat f t) x) (Ici t) t ∧
      derivWithin (fun s => continuumHeat f s x) (Ici t) t =
        LatticeProb.WhiteNoise.contOp d (continuumHeat f t) x) :=
  ⟨continuumHeat_zero f, fun _ ht => contDiff_continuumHeat hd hf hfc ht,
    fun _ ht x => hasDerivAt_continuumHeat hd hf hfc ht x,
    fun _ ht x => ⟨hasDerivWithinAt_continuumHeat hd hf hfc ht x,
      derivWithin_continuumHeat hd hf hfc ht x⟩⟩

end LongRangeHeat.Statements
