import LongRangeHeat.ScalingSampling
import LongRangeHeat.ScalingTimeNeighborhood

/-!
# Lower bounds for sampled heat increments

Continuum time increments have a uniform lower bound in lattice norm at sufficiently small
spacing.
-/

namespace LongRangeHeat

open Filter LatticeProb LatticeProb.Euclidean.Lattice
open scoped Topology ContDiff

noncomputable section

variable {d : ℕ}

/-- A pointwise absolute-value comparison implies a lattice norm comparison. -/
theorem latticeNorm_const_mul_le {ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 ≤ a)
    {v w : Site d → ℝ} (hv : MemL2 v) (hw : MemL2 w)
    (h : ∀ q, a * |v q| ≤ |w q|) :
    a * latticeNorm ε v ≤ latticeNorm ε w := by
  have hsc : MemL2 (fun q => a * v q) := memL2_const_mul hv a
  have hsum : (∑' q, (a * v q) ^ 2) ≤ ∑' q, w q ^ 2 := by
    apply Summable.tsum_le_tsum _ hsc hw
    intro q
    have hq : |a * v q| ≤ |w q| := by simpa only [abs_mul, abs_of_nonneg ha] using h q
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hq
  have hn := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum (pow_nonneg hε d))
  have heq : latticeNorm ε (fun q => a * v q) = a * latticeNorm ε v := by
    unfold latticeNorm latticeNormSq
    simp_rw [mul_pow, tsum_mul_left]
    rw [mul_left_comm (ε ^ d), Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
      abs_of_nonneg ha]
  rw [← heq]
  exact hn


/-- The lattice norm of a continuum time increment is bounded below uniformly at small mesh. -/
theorem eventually_latticeNorm_continuumHeat_increment_lower_bound (hd : 1 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {x : Fin d → ℝ} (hx : f x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Ioo (0 : ℝ) T, ∃ C > 0, ∃ δ > 0,
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ s ∈ Set.Ioo (max 0 (t - δ)) t,
        MemL2 (fun q => continuumHeat f t (physical ε q) -
          continuumHeat f s (physical ε q)) ∧
        C * (t - s) ≤ latticeNorm ε (fun q =>
          continuumHeat f t (physical ε q) - continuumHeat f s (physical ε q)) := by
  obtain ⟨t, ht, y, c, hc, r, hr, δ, hδ, hb⟩ :=
    exists_continuumHeat_time_increment_lower_bound hd hf hfc hx hT
  let χ : ContDiffBump y := ⟨r / 2, r, by positivity, by linarith⟩
  have hχy : χ y = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
  have hχ : ContDiff ℝ ∞ (χ : (Fin d → ℝ) → ℝ) := χ.contDiff
  obtain ⟨k, hk, hklim⟩ := eventually_latticeNorm_sample_pos hχ.continuous
    χ.hasCompactSupport (x := y) (by rw [hχy]; norm_num)
  refine ⟨t, ht, c * k, mul_pos hc hk, δ, hδ, ?_⟩
  filter_upwards [hklim, self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with ε hkn hε hε1
  intro s hs
  have hs0 : 0 < s := (le_max_left 0 (t - δ)).trans_lt hs.1
  obtain ⟨R, hR⟩ := exists_sampledHeat_uniform_l2_bound hd hε hε1.le hf.continuous hfc
  have hv : MemL2 (fun q => χ (physical ε q)) := by
    change MemL2 (restrict ε χ)
    exact memL2_restrict hε χ.hasCompactSupport
  have hw : MemL2 (fun q => continuumHeat f t (physical ε q) -
      continuumHeat f s (physical ε q)) := by
    simpa only [restrict] using memL2_sub (hR t ht.1.le).1 (hR s hs0.le).1
  refine ⟨hw, ?_⟩
  have ha : 0 ≤ c * (t - s) := mul_nonneg hc.le (sub_nonneg.mpr hs.2.le)
  have hp (q : Site d) : c * (t - s) * |χ (physical ε q)| ≤
      |continuumHeat f t (physical ε q) - continuumHeat f s (physical ε q)| := by
    by_cases hq : physical ε q ∈ Metric.ball y r
    · have hχ0 : 0 ≤ χ (physical ε q) := χ.nonneg
      have hχ1 : χ (physical ε q) ≤ 1 := χ.le_one
      rw [abs_of_nonneg hχ0]
      exact (mul_le_of_le_one_right ha hχ1).trans (hb s hs _ hq)
    · have hzero : χ (physical ε q) = 0 := by
        apply Function.notMem_support.mp
        simpa only [χ.support_eq] using hq
      simp only [hzero, abs_zero, mul_zero, abs_nonneg]
  have hn := latticeNorm_const_mul_le hε.le ha hv hw hp
  have hk' := mul_le_mul_of_nonneg_left hkn ha
  nlinarith

end
end LongRangeHeat
