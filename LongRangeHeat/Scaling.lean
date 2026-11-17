import LongRangeHeat.Continuum
import LongRange.Scaling.Generator
import LongRange.Scaling.AnnulusLimit

/-!
# Scaling of the lattice heat flow

Halving the lattice spacing with the same integer indexing scales the generator and time.
-/


noncomputable section

open Filter Topology
open LatticeProb.Euclidean.Shell

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LongRange

noncomputable section

/-- The lattice heat series scales under a simultaneous halving of the lattice and initial data. -/
theorem latticeHeat_half {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (a : Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (t : ℝ) (q : Site d) :
    latticeHeat (ε / 2) a (fun x => f (2 • x)) t q =
      latticeHeat ε a f ((4 * kappa d ε / kappa d (ε / 2)) * t) q := by
  let c : ℝ := 4 * kappa d ε / kappa d (ε / 2)
  have hr : restrict (ε / 2) (fun x => f (2 • x)) = restrict ε f := by
    funext q
    change f (2 • physical (ε / 2) q) = f (physical ε q)
    apply congrArg f
    funext i
    simp only [physical, Pi.smul_apply]
    ring
  have hi (n : ℕ) : (generator (ε / 2) a)^[n] (restrict ε f) =
      fun q => c ^ n * (generator ε a)^[n] (restrict ε f) q := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext q
      rw [generator_const_mul, Scaling.generator_half hd hε]
      rw [Function.iterate_succ_apply']
      dsimp only [c]
      rw [pow_succ]
      ring
  unfold latticeHeat
  rw [hr]
  apply tsum_congr
  intro n
  rw [hi]
  dsimp only
  rw [mul_pow]
  ring

/-- The continuum heat flow obeys the same spatial dilation with diffusive time scaling. -/
theorem continuumHeat_half {d : ℕ} (hd : 1 ≤ d) (f : (Fin d → ℝ) → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    continuumHeat (fun y => f (2 • y)) t ((1 / 2 : ℝ) • x) =
      continuumHeat f (4 * t) x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [continuumHeat, mul_zero, ↓reduceIte]
    apply congrArg f
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [continuumHeat_eq_integral _ ht, continuumHeat_eq_integral _ (by positivity)]
    rw [LatticeProb.Heat.integral_heatKernel_mul_eq hd (τ := t) ht,
      LatticeProb.Heat.integral_heatKernel_mul_eq hd (τ := 4 * t) (by positivity)]
    have hs : Real.sqrt ((4 * t) / d) = 2 * Real.sqrt (t / d) := by
      rw [show (4 * t) / (d : ℝ) = 4 * (t / d) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hs]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    congr 1
    congr 1
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- The halving time defect has the exact inverse-logarithmic coefficient. -/
theorem kappa_half_ratio_tendsto {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun ε : ℝ =>
      ((kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2)) * |Real.log ε|)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  have hA : 0 < A := by
    dsimp [A]
    rw [← unitBallVolume_eq_pi_div_gamma]
    exact mul_pos (Nat.cast_pos.mpr (by omega)) (unitBallVolume_pos d)
  have hL : Tendsto (fun ε : ℝ => |Real.log ε|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  obtain ⟨K, _, hK⟩ := kappa_asymptotic hd
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hε hε'
    exact ⟨hε, hε'.le⟩
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      -K ≤ kappa d ε - A * |Real.log ε| ∧ kappa d ε - A * |Real.log ε| ≤ K := by
    filter_upwards [hsmall] with ε hε
    exact abs_le.mp (hK ε hε)
  have hz : Tendsto (fun ε : ℝ => (kappa d ε - A * |Real.log ε|) / |Real.log ε|)
      (𝓝[>] 0) (𝓝 0) := tendsto_bdd_div_atTop_nhds_zero (hb.mono fun _ h => h.1)
        (hb.mono fun _ h => h.2) hL
  have hLpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < |Real.log ε| := hL.eventually_gt_atTop 0
  have hk : Tendsto (fun ε : ℝ => kappa d ε / |Real.log ε|) (𝓝[>] 0) (𝓝 A) := by
    have h := hz.add (tendsto_const_nhds (x := A))
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [hLpos] with ε hε
    field_simp
    ring
  have hi : Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε)
      (𝓝[>] 0) (𝓝 (A * Real.log 2)) := by
    simpa [A] using tendsto_kappa_half_sub hd
  have hi0 := hi.div_atTop hL
  have hkhalf : Tendsto (fun ε : ℝ => kappa d (ε / 2) / |Real.log ε|)
      (𝓝[>] 0) (𝓝 A) := by
    have h := hi0.add hk
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [] with ε
    ring
  have hfinal := hi.div hkhalf hA.ne'
  have htarget : A * Real.log 2 / A = Real.log 2 := by field_simp
  rw [htarget] at hfinal
  apply hfinal.congr'
  filter_upwards [] with ε
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end
end LongRangeHeat
