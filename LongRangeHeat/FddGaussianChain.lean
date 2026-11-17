import LongRangeHeat.FddGaussian
import LongRangeHeat.FddChain
import LongRangeHeat.FddAlgebra

/-!
# Products of observations of a sum of independent Gaussian steps

For independent centered Gaussian vectors `D_0, …, D_{k-1}` in `ℝ^d` with independent coordinates
of variances `s_0, …, s_{k-1}`, the partial sums `S_u = D_0 + ⋯ + D_u` satisfy
`E[∏_u ψ_u(x + d^{-1/2} S_u)] = contExp k s ψ x`, the backward recursion with the heat flow
`P̄_{s_u}` (`integral_prod_gaussian_steps`). This is the Markov property of Brownian motion for
finitely many times.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff

noncomputable section

variable {d : ℕ}

/-- The partial sums `D_0 + ⋯ + D_u` of a family of vectors. -/
def cumSum {k : ℕ} (D : Fin k → Fin d → ℝ) (u : Fin k) : Fin d → ℝ :=
  ∑ v : Fin k, if v ≤ u then D v else 0

theorem cumSum_zero {k : ℕ} (D : Fin (k + 1) → Fin d → ℝ) : cumSum D 0 = D 0 := by
  rw [cumSum, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

theorem cumSum_succ {k : ℕ} (D : Fin (k + 1) → Fin d → ℝ) (u : Fin k) :
    cumSum D u.succ = D 0 + cumSum (fun v => D v.succ) u := by
  rw [cumSum, Fin.sum_univ_succ]
  simp [cumSum, Fin.succ_le_succ_iff]

/-- The backward recursion `E[∏ g_u(X_{t_u})] = e^{s_0 Δ}(g_0 e^{s_1 Δ}(g_1 ⋯))` in the continuum,
with the empty product equal to `1`. -/
def contExp {d : ℕ} : (k : ℕ) → (Fin k → ℝ≥0) → (Fin k → (Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | 0, _, _ => fun _ => 1
  | k + 1, s, g =>
      continuumHeat (fun y => g 0 y * contExp k (Fin.tail s) (Fin.tail g) y) ((s 0 : ℝ≥0) : ℝ)

theorem contExp_contDiff (hd : 1 ≤ d) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin k → (Fin d → ℝ) → ℝ),
      (∀ u, IsTestFunction (g u)) → ContDiff ℝ ∞ (contExp k s g)
  | 0, s, g, _ => contDiff_const
  | k + 1, s, g, hg => by
      have ih := contExp_contDiff hd k (Fin.tail s) (Fin.tail g) fun u => hg u.succ
      exact contDiff_continuumHeat hd ((hg 0).1.mul ih)
        ((hg 0).2.mul_right) (s 0).2

theorem abs_contExp_le (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin k → (Fin d → ℝ) → ℝ),
      (∀ u, IsTestFunction (g u)) → (∀ u y, |g u y| ≤ M) → ∀ x, |contExp k s g x| ≤ M ^ k
  | 0, s, g, _, _, x => by simp [contExp]
  | k + 1, s, g, hg, hgM, x => by
      have ih := abs_contExp_le hd hM k (Fin.tail s) (Fin.tail g) (fun u => hg u.succ)
        (fun u => hgM u.succ)
      have hc : Continuous fun y => g 0 y * contExp k (Fin.tail s) (Fin.tail g) y :=
        ((hg 0).1.continuous).mul
          (contExp_contDiff hd k (Fin.tail s) (Fin.tail g) fun u => hg u.succ).continuous
      have hb : ∀ y, |g 0 y * contExp k (Fin.tail s) (Fin.tail g) y| ≤ M ^ (k + 1) := fun y => by
        rw [abs_mul, pow_succ']
        exact mul_le_mul (hgM 0 y) (ih y) (abs_nonneg _) hM
      exact abs_continuumHeat_le hd hc hb (s 0).2 x

/-- The recursion `contExp` is the function `F̄_0` of the proof of Proposition 4.3. -/
theorem mul_contExp_eq_continuumChain {d : ℕ} :
    ∀ (m : ℕ) (s : Fin m → ℝ≥0) (g : Fin (m + 1) → (Fin d → ℝ) → ℝ),
      (fun y => g 0 y * contExp m s (Fin.tail g) y) = continuumChain m s g
  | 0, s, g => by
      funext y
      simp [contExp, continuumChain]
  | m + 1, s, g => by
      funext y
      have ih := mul_contExp_eq_continuumChain m (Fin.tail s) (Fin.tail g)
      show g 0 y * continuumHeat (fun y' => Fin.tail g 0 y' *
        contExp m (Fin.tail s) (Fin.tail (Fin.tail g)) y') ((s 0 : ℝ≥0) : ℝ) y = _
      rw [ih]
      rfl

end

end LongRangeHeat
