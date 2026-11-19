import LongRange.Support.Analysis.Davies.FiniteForm

/-!
# Perturbation inequalities for finite jump forms

Two-point estimates for conjugating a jump form by an exponential weight.
-/

open Matrix
open scoped Matrix.Norms.Operator

namespace LatticeProb.Davies

noncomputable section

/-- The one-power perturbation estimate on a pair of points. -/
theorem pair_one (a b h : ℝ) :
    (Real.exp h * b - a) * (Real.exp (-h) * b - a) ≥
      (b - a) ^ 2 - a ^ 2 * (Real.exp h - 1) ^ 2 / 2 -
        b ^ 2 * (Real.exp (-h) - 1) ^ 2 / 2 := by
  let x := Real.exp h
  let y := Real.exp (-h)
  have hxy : x * y = 1 := by
    dsimp [x, y]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hid : (x * b - a) * (y * b - a) -
      ((b - a) ^ 2 - a ^ 2 * (x - 1) ^ 2 / 2 - b ^ 2 * (y - 1) ^ 2 / 2) =
      (a * (x - 1) + b * (y - 1)) ^ 2 / 2 := by
    calc
      _ = (a * (x - 1) + b * (y - 1)) ^ 2 / 2 +
          (x * y - 1) * (b ^ 2 - a * b) := by ring
      _ = _ := by rw [hxy]; ring
  have hs := sq_nonneg (a * (x - 1) + b * (y - 1))
  change (x * b - a) * (y * b - a) ≥
    (b - a) ^ 2 - a ^ 2 * (x - 1) ^ 2 / 2 - b ^ 2 * (y - 1) ^ 2 / 2
  linarith

namespace FiniteJumpForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The two bounds on the weight are interchanged by changing its sign. -/
theorem LambdaBound.neg {ψ : ι → ℝ} {Λsq : ℝ} (h : F.LambdaBound ψ Λsq) :
    F.LambdaBound (-ψ) Λsq := by
  rcases h with ⟨h₀, h₁, h₂⟩
  refine ⟨h₀, ?_, ?_⟩
  · intro i
    simpa only [Pi.neg_apply, neg_sub_neg] using h₂ i
  · intro i
    simpa only [Pi.neg_apply, neg_sub_neg] using h₁ i

end FiniteJumpForm
end
end LatticeProb.Davies
