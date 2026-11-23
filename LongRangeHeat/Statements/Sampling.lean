import LongRangeHeat.Sampling

/-!
# Lemma 2.2 and the bounds (2.6), (2.7)

Regularity of the continuum solution `ū = continuumHeat f` of (1.5), sampled on the translates of
`εℤ^d`. Here `∂^β` is the iterated partial derivative `multiDeriv β`, `|z|` is the Euclidean norm
`radius z`, `z · ∇ū_s(x)` is `fderiv ℝ ū_s x z` and `z · ∇²ū_s(x) z` is
`fderiv ℝ (fderiv ℝ ū_s) x z z`.
-/

namespace LongRangeHeat.Statements

open Set LatticeProb LatticeProb.Euclidean.Lattice
open scoped ContDiff

variable {d : ℕ}

/-- **Lemma 2.2** (`lem:sampling`, regularity of the continuum solution). For `f ∈ C_c^∞(ℝ^d)` and
a multi-index `β` there is `C = C(d, f, β)` such that, for every `ε ∈ (0, 1/2)`, every `s ≥ 0` and
every `y ∈ ℝ^d`, `ε^d ∑_{x ∈ εℤ^d} |∂^β ū(s, x + y)|² ≤ C` (the series converges). -/
theorem sampling (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (β : Fin d → ℕ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s → ∀ y : Fin d → ℝ,
      Summable (fun q : Site d => |multiDeriv β (continuumHeat f s) (physical ε q + y)| ^ 2) ∧
      ε ^ d * ∑' q : Site d, |multiDeriv β (continuumHeat f s) (physical ε q + y)| ^ 2 ≤ C :=
  sampling_bound hd hf hfc β

/-- **(2.6)** (`eq:increment`). For `f ∈ C_c^∞(ℝ^d)` there is `C = C(d, f)` such that, for every
`ε ∈ (0, 1/2)`, every `s ≥ 0` and every `z ∈ ℝ^d`, the lattice function
`x ↦ ū_s(x + z) - ū_s(x)` on `εℤ^d` lies in `L²(εℤ^d)` and
`‖ū_s(· + z) - ū_s‖_{L²(εℤ^d)} ≤ C min(|z|, 1)`. -/
theorem increment_bound (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s → ∀ z : Fin d → ℝ,
      MemL2 (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q)) ∧
      latticeNorm ε (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q)) ≤
          C * min (radius z) 1 :=
  _root_.LongRangeHeat.increment_bound hd hf hfc

/-- **(2.7)** (`eq:taylor`). For `f ∈ C_c^∞(ℝ^d)` there is `C = C(d, f)` such that, for every
`ε ∈ (0, 1/2)`, every `s ≥ 0` and every `z ∈ ℝ^d`, the lattice function
`x ↦ ū_s(x + z) - ū_s(x) - z · ∇ū_s(x) - ½ z · ∇²ū_s(x) z` on `εℤ^d` lies in `L²(εℤ^d)` with
norm at most `C |z|³`. -/
theorem taylor_bound (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s → ∀ z : Fin d → ℝ,
      MemL2 (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q) -
          fderiv ℝ (continuumHeat f s) (physical ε q) z -
          1 / 2 * fderiv ℝ (fderiv ℝ (continuumHeat f s)) (physical ε q) z z) ∧
      latticeNorm ε (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q) -
          fderiv ℝ (continuumHeat f s) (physical ε q) z -
          1 / 2 * fderiv ℝ (fderiv ℝ (continuumHeat f s)) (physical ε q) z z) ≤
        C * radius z ^ 3 :=
  _root_.LongRangeHeat.taylor_bound hd hf hfc

end LongRangeHeat.Statements
