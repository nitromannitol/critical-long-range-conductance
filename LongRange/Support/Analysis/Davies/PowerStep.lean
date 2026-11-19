import LongRange.Support.Analysis.Davies.NashDerivative
import LongRange.Support.Analysis.Davies.Comparison

/-!
# Normalized power sums for the Davies iteration

Positivity and monotonicity of the finite power sums used in the Nash comparison.
-/

namespace LatticeProb.Davies.FiniteJumpForm

open Set

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- A nonzero nonnegative initial vector has positive twisted power sums. -/
theorem twist_powSum_pos (ψ f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (p : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < ∑ i, (F.twist ψ f t i) ^ p := by
  have hnonneg : ∀ i, 0 ≤ F.twist ψ f t i := F.twist_nonneg ψ f hf ht
  have hne := F.twist_ne_zero ψ f hf0 t
  have hex : ∃ i, 0 < F.twist ψ f t i := by
    by_contra h
    apply hne
    funext i
    exact le_antisymm (le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)) (hnonneg i)
  obtain ⟨j, hj⟩ := hex
  exact Finset.sum_pos' (fun i _ ↦ pow_nonneg (hnonneg i) p)
    ⟨j, Finset.mem_univ _, pow_pos hj p⟩

/-- A stronger exponential compensation preserves decay of an even power sum. -/
theorem antitoneOn_compensated_powSum {ψ : ι → ℝ} {Λsq δ : ℝ}
    (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (q : ℕ) (hq : 1 ≤ q) :
    let p : ℕ := 2 * q
    let c : ℝ := (2 * (p : ℝ) + 1) * Λsq + δ / p
    AntitoneOn (fun t ↦ Real.exp (-(p : ℝ) * c * t) *
      ∑ i, (F.twist ψ f t i) ^ p) (Ici 0) := by
  let p : ℕ := 2 * q
  let c : ℝ := (2 * (p : ℝ) + 1) * Λsq + δ / p
  let r : ℝ := levelRate Λsq q
  let d : ℝ := (p : ℝ) * (c - r)
  let N : ℝ → ℝ := fun t ↦ ∑ i, (F.twist ψ f t i) ^ p
  have hp : 0 < (p : ℝ) := by dsimp [p]; positivity
  have hrle : r ≤ (2 * (p : ℝ) + 1) * Λsq := by
    dsimp only [r, levelRate]
    split_ifs with hq1
    · have hq0 : 0 ≤ (p : ℝ) := hp.le
      nlinarith [mul_nonneg hq0 hΛ.1]
    · have hqp : (q : ℝ) ≤ p := by
        exact_mod_cast (show q ≤ 2 * q by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hqp) hΛ.1]
  have hd0 : 0 ≤ d := by
    dsimp [d, c]
    apply mul_nonneg hp.le
    have hdiv : 0 ≤ δ / (p : ℝ) := div_nonneg hδ hp.le
    linarith
  have hbase := F.antitoneOn_level hΛ f hf q hq
  have hbase' : AntitoneOn (fun t ↦ Real.exp (-(p : ℝ) * r * t) * N t) (Ici 0) := by
    simpa only [p, r, N, Nat.cast_mul, Nat.cast_ofNat, neg_mul] using hbase
  have heq (t : ℝ) : Real.exp (-(p : ℝ) * c * t) * N t =
      Real.exp (-d * t) * (Real.exp (-(p : ℝ) * r * t) * N t) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [d]
    ring
  change AntitoneOn (fun t ↦ Real.exp (-(p : ℝ) * c * t) * N t) (Ici 0)
  intro x hx y hy hxy
  dsimp only
  rw [heq x, heq y]
  have hE : Real.exp (-d * y) ≤ Real.exp (-d * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hxy)]
  have hN : 0 ≤ Real.exp (-(p : ℝ) * r * y) * N y := by
    apply mul_nonneg (Real.exp_pos _).le
    exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf hy i) p
  exact mul_le_mul hE (hbase' hx hy hxy) hN (Real.exp_pos _).le

end
end LatticeProb.Davies.FiniteJumpForm
