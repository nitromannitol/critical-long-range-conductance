import LongRange.Support.Analysis.Davies.GridPower

/-!
# Endpoint estimates for Davies iteration

Coordinate bounds and perturbation rates at the endpoint of the time grid.
-/

namespace LatticeProb.Davies.FiniteJumpForm

open scoped Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- Every power-level perturbation rate is at most three times its power. -/
theorem levelRate_le {Λsq : ℝ} (hΛ : 0 ≤ Λsq) (p : ℕ) (hp : 1 ≤ p) :
    levelRate Λsq p ≤ 3 * (p : ℝ) * Λsq := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  by_cases h : p = 1
  · simp only [levelRate, h, ↓reduceIte, Nat.cast_one]
    nlinarith
  · simp only [levelRate, h, ↓reduceIte]
    nlinarith [mul_nonneg hΛ (sub_nonneg.mpr hp1)]

/-- A coordinate at the terminal time is bounded by a compensated grid power. -/
theorem coordinate_le_gridPower {ψ : ι → ℝ} {Λsq l t : ℝ}
    (hΛ : F.LambdaBound ψ Λsq) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hl : 2 < l) (ht : 0 < t) (n : ℕ) (i : ι) :
    F.twist ψ f t i ≤
      Real.exp (levelRate Λsq (2 ^ n) * (t - timeGrid l t (n + 1))) *
        F.gridPower ψ f l t n := by
  have hq : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hs := timeGrid_nonneg hl ht.le (n + 1)
  have hst := (timeGrid_lt hl ht (n + 1)).le
  have hcoord := coordinate_le_powSum (F.twist ψ f t)
    (fun j ↦ F.twist_nonneg ψ f hf ht.le j) (2 * 2 ^ n) (by positivity) i
  have hroot := F.twist_powSum_root_le hΛ f hf (2 ^ n) hq hs hst
  have hnat : 2 * (2 ^ n : ℕ) = 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hr : (2 * (2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) / 2 ^ n := by field_simp
  rw [hnat] at hcoord hroot
  push_cast at hcoord hroot
  have hr1 : ((2 : ℝ) ^ (n + 1))⁻¹ = (1 / 2 : ℝ) / 2 ^ n := by
    rw [pow_succ]
    field_simp
  rw [hr1] at hcoord
  rw [hr] at hroot
  exact hcoord.trans hroot

/-- The remaining perturbation cost is bounded by a geometric sequence. -/
theorem levelRate_mul_remaining_le {Λsq l t : ℝ} (hΛ : 0 ≤ Λsq)
    (hl : 2 < l) (ht : 0 ≤ t) (n : ℕ) :
    levelRate Λsq (2 ^ n) * (t - timeGrid l t (n + 1)) ≤
      (3 * Λsq * t / l) * (2 / l) ^ n := by
  have hlpos : 0 < l := by linarith
  have hrem : t - timeGrid l t (n + 1) = t * l⁻¹ ^ (n + 1) := by
    dsimp [timeGrid]
    ring
  have hq : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  rw [hrem]
  calc
    _ ≤ (3 * ((2 ^ n : ℕ) : ℝ) * Λsq) * (t * l⁻¹ ^ (n + 1)) :=
      mul_le_mul_of_nonneg_right (levelRate_le hΛ _ hq)
        (mul_nonneg ht (pow_nonneg (inv_nonneg.mpr hlpos.le) _))
    _ = _ := by
      push_cast
      rw [div_pow, pow_succ]
      simp only [div_eq_mul_inv, inv_pow]
      ring

/-- The exponential correction at the endpoint tends to one. -/
theorem tendsto_exp_levelRate_remaining {Λsq l t : ℝ} (hΛ : 0 ≤ Λsq)
    (hl : 2 < l) (ht : 0 ≤ t) :
    Filter.Tendsto (fun n : ℕ ↦ Real.exp
      (levelRate Λsq (2 ^ n) * (t - timeGrid l t (n + 1)))) Filter.atTop (𝓝 1) := by
  have hlpos : 0 < l := by linarith
  have hr0 (n : ℕ) : 0 ≤ levelRate Λsq (2 ^ n) := by
    unfold levelRate
    split_ifs <;> positivity
  have hrem0 (n : ℕ) : 0 ≤ t - timeGrid l t (n + 1) := by
    dsimp [timeGrid]
    have hpow : 0 ≤ l⁻¹ ^ (n + 1) := pow_nonneg (inv_nonneg.mpr hlpos.le) _
    nlinarith
  have hq0 : 0 ≤ 2 / l := by positivity
  have hq1 : 2 / l < 1 := (div_lt_one hlpos).2 hl
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hbound : Filter.Tendsto (fun n : ℕ ↦ (3 * Λsq * t / l) * (2 / l) ^ n)
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (3 * Λsq * t / l)
  have harg : Filter.Tendsto
      (fun n : ℕ ↦ levelRate Λsq (2 ^ n) * (t - timeGrid l t (n + 1)))
      Filter.atTop (𝓝 0) := squeeze_zero
    (fun n ↦ mul_nonneg (hr0 n) (hrem0 n))
    (fun n ↦ levelRate_mul_remaining_le hΛ hl ht n) hbound
  simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp harg

end
end LatticeProb.Davies.FiniteJumpForm
