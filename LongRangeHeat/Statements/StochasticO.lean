import LongRangeHeat.StochasticO

/-!
# Lemma 2.3: properties of the notation `𝒪_q`

Statements of the five items of Lemma 2.3 (`lem:O`) of the heat-kernel version, for `q ∈ {1, 2}`
and random variables on an arbitrary probability space: squares, expectation, sums (over `ℕ` as in
the paper, and over any countable index set), integrals over `[0, T]`, and constants.
-/

namespace LongRangeHeat.Statements

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 2.3 (i)** (`lem:O`, squares). For every nonnegative random variable `X` and every
`A > 0`, `X ≤ 𝒪₂(A)` if and only if `X² ≤ 𝒪₁(A²)`. -/
theorem O_squares (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {A : ℝ} (_hA : 0 < A) : IsOq P 2 X A ↔ IsOq P 1 (fun ω => X ω ^ 2) (A ^ 2) :=
  isOq_two_iff hX A

/-- **Lemma 2.3 (ii)** (`lem:O`, expectation). For every random variable `X` and every `A > 0`
with `X ≤ 𝒪₂(A)`, `max(X, 0)` is integrable and `𝔼[max(X, 0)] ≤ 2A`. -/
theorem O_expectation (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {A : ℝ}
    (hA : 0 < A) (h : IsOq P 2 X A) :
    Integrable (fun ω => max (X ω) 0) P ∧ ∫ ω, max (X ω) 0 ∂P ≤ 2 * A :=
  integrable_and_integral_max_le hA h

/-- **Lemma 2.3 (iii)** (`lem:O`, sums). Let `q ∈ {1, 2}`, let `(X_k)_{k ∈ ℕ}` be nonnegative
random variables and `(A_k)_{k ∈ ℕ}` positive numbers with `∑ A_k < ∞`. If `X_k ≤ 𝒪_q(A_k)` for
every `k`, then `∑ X_k` converges almost surely and `∑ X_k ≤ 𝒪_q(∑ A_k)`. -/
theorem O_sums (P : Measure Ω) [IsProbabilityMeasure P] {q : ℕ} (hq : q = 1 ∨ q = 2)
    {X : ℕ → Ω → ℝ} (hX : ∀ k ω, 0 ≤ X k ω) {A : ℕ → ℝ} (hA : ∀ k, 0 < A k)
    (hAs : Summable A) (h : ∀ k, IsOq P q (X k) (A k)) :
    (∀ᵐ ω ∂P, Summable fun k => X k ω) ∧ IsOq P q (fun ω => ∑' k, X k ω) (∑' k, A k) :=
  isOq_tsum (by omega) hX hA hAs h

/-- **Lemma 2.3 (iii)** (`lem:O`, sums), over any countable index set. -/
theorem O_sums_countable (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} [Countable ι]
    {q : ℕ} (hq : q = 1 ∨ q = 2) {X : ι → Ω → ℝ} (hX : ∀ k ω, 0 ≤ X k ω) {A : ι → ℝ}
    (hA : ∀ k, 0 < A k) (hAs : Summable A) (h : ∀ k, IsOq P q (X k) (A k)) :
    (∀ᵐ ω ∂P, Summable fun k => X k ω) ∧ IsOq P q (fun ω => ∑' k, X k ω) (∑' k, A k) :=
  isOq_tsum (by omega) hX hA hAs h

/-- **Lemma 2.3 (iv)** (`lem:O`, integrals). Let `q ∈ {1, 2}`, `T > 0`, `A > 0`, and let
`(X(s))_{s ∈ [0, T]}` be a family of nonnegative random variables that is jointly measurable on
`[0, T] × Ω`. If `X(s) ≤ 𝒪_q(A)` for every `s ∈ [0, T]`, then almost surely `s ↦ X(s)` is
integrable on `[0, T]`, and `∫_0^T X(s) ds ≤ 𝒪_q(T A)`. -/
theorem O_integrals (P : Measure Ω) [IsProbabilityMeasure P] {q : ℕ} (hq : q = 1 ∨ q = 2)
    {X : ℝ → Ω → ℝ} {T A : ℝ} (hXm : Measurable fun p : Set.Icc 0 T × Ω => X p.1 p.2)
    (hT : 0 < T) (hA : 0 < A) (hX : ∀ s ∈ Set.Icc 0 T, ∀ ω, 0 ≤ X s ω)
    (h : ∀ s ∈ Set.Icc 0 T, IsOq P q (X s) A) :
    (∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (fun s => X s ω) (Set.Icc 0 T)) ∧
      IsOq P q (fun ω => ∫ s in (0)..T, X s ω) (T * A) :=
  isOq_intervalIntegral (by omega) hXm hT hA hX h

/-- **Lemma 2.3 (v)** (`lem:O`, constants). For every `q ∈ {1, 2}` and every real `A > 0`, the
constant random variable `A` satisfies `A ≤ 𝒪_q(2A)`. -/
theorem O_constants (P : Measure Ω) [IsProbabilityMeasure P] {q : ℕ} (hq : q = 1 ∨ q = 2)
    {A : ℝ} (hA : 0 < A) : IsOq P q (fun _ => A) (2 * A) :=
  isOq_const (by omega) hA

end LongRangeHeat.Statements
