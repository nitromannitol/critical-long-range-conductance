import LongRangeHeat.SampledForcing

/-!
# Lemma 3.3: Gaussian tails of the field `G`

Statement of Lemma 3.3 (`lem:G`) of the heat-kernel version for the vector field `G` of (3.3),
first for a square-summable function `g` with the increment bound
`‖g(· + z) - g‖ ≤ K min(|z|, 1)` and then for the sampled solution
`ū_s = restrict ε (continuumHeat f s)`.
-/

namespace LongRangeHeat.Statements

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (Edge)
open scoped ContDiff

/-- **Lemma 3.3** (`lem:G`, Gaussian tails of the field `G`), for a function `g ∈ L²(εℤ^d)`
with the increment bound `‖g(· + z) - g‖ ≤ K min(|z|, 1)` in place of `ū_s`. There is `C > 0`,
depending only on `d` and `λ`, such that for every probability space `(Ω, P)`, every field of
conductances `a` satisfying the standing assumptions with ellipticity `λ`, every `ε ∈ (0, 1/2)`,
every `K > 0` and every such `g`, each component of `G` lies in `L²(εℤ^d)` for every realization
and `‖G‖_{L²(εℤ^d)} = (∑_i ‖G_i‖²)^{1/2} ≤ 𝒪₂(C K)`. -/
theorem G_gaussian_tails_of_increment {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ),
      ConductanceLaw P lam a → ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ K > 0, ∀ g : Site d → ℝ,
      MemL2 g → (∀ w : Site d,
        latticeNorm ε (fun q => g (q + w) - g q) ≤ K * min (radius (physical ε w)) 1) →
      (∀ r i, MemL2 (forcingField ε (a r) g i)) ∧
      IsOq P 2 (fun r => Real.sqrt (∑ i, latticeNormSq ε (forcingField ε (a r) g i)))
        (C * K) :=
  forcingField_gaussian_tails_of_increment hd hlam

/-- **Lemma 3.3** (`lem:G`, Gaussian tails of the field `G`). For `f ∈ C_c^∞(ℝ^d)` there is
`C = C(d, λ, f) > 0` such that for every probability space `(Ω, P)`, every field of conductances
`a` satisfying the standing assumptions with ellipticity `λ`, every `ε ∈ (0, 1/2)` and every
`s ≥ 0`, the components of `G(s, ·)` lie in `L²(εℤ^d)` and
`‖G(s, ·)‖_{L²(εℤ^d)} ≤ 𝒪₂(C)`. -/
theorem G_gaussian_tails {d : ℕ} (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ),
      ConductanceLaw P lam a → ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s →
      (∀ r i, MemL2 (forcingField ε (a r) (restrict ε (continuumHeat f s)) i)) ∧
      IsOq P 2 (fun r => Real.sqrt (∑ i, latticeNormSq ε
        (forcingField ε (a r) (restrict ε (continuumHeat f s)) i))) C :=
  LongRangeHeat.forcingField_gaussian_tails_sampled hd hf hfc hlam

end LongRangeHeat.Statements
