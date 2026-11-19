import Mathlib

/-!
# Finite symmetric jump forms

Finite jump forms with killing, their semigroups, and the quantities used in Davies' method.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies

noncomputable section

/-- A symmetric nonnegative jump kernel and a nonnegative killing rate on a finite set. -/
structure FiniteJumpForm (ι : Type*) [Fintype ι] where
  q : ι → ι → ℝ
  κ : ι → ℝ
  q_nonneg : ∀ i j, 0 ≤ q i j
  q_symm : ∀ i j, q i j = q j i
  κ_nonneg : ∀ i, 0 ≤ κ i

namespace FiniteJumpForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The generator of the killed chain. -/
def gen : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ F.q i j - if i = j then (∑ k, F.q i k) + F.κ i else 0

/-- The bilinear form associated with the killed generator. -/
def form (u v : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, F.q i j * (u j - u i) * (v j - v i)) / 2 +
    ∑ i, F.κ i * u i * v i

/-- The matrix exponential semigroup of the killed generator. -/
def semigroup (t : ℝ) : Matrix ι ι ℝ := NormedSpace.exp (t • F.gen)

/-- The semigroup conjugated by the exponential of a real-valued weight. -/
def twist (ψ f : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  Real.exp (ψ i) * (F.semigroup t *ᵥ fun j ↦ Real.exp (-ψ j) * f j) i

/-- A common upper bound for the two jump carré du champ expressions. -/
def LambdaBound (ψ : ι → ℝ) (Λsq : ℝ) : Prop :=
  0 ≤ Λsq ∧
    (∀ i, ∑ j, F.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2 / 2 ≤ Λsq) ∧
    (∀ i, ∑ j, F.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2 / 2 ≤ Λsq)

/-- The finite-set Nash inequality for the form. -/
def Nash (θ : ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ g : ι → ℝ, (∑ i, |g i|) ≤ 1 → 0 < ∑ i, (g i) ^ 2 →
    θ (∑ i, (g i) ^ 2) ≤ F.form g g + δ * ∑ i, (g i) ^ 2

/-- The finite sum of a natural power of a real-valued function. -/
def powSum (f : ι → ℝ) (p : ℕ) : ℝ := ∑ i, (f i) ^ p

end FiniteJumpForm
end
end LatticeProb.Davies
