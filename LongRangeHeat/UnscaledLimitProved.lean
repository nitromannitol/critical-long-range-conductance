import LongRangeHeat.UnscaledLimit
import LongRangeHeat.Statements.InvariancePrincipleProved

/-!
# Unscaled annealed convergence

The rescaled invariance principle gives the Brownian limit of the unit walk.
-/

namespace LongRangeHeat

open Set Filter MeasureTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.Euclidean.Lattice
open scoped Topology NNReal
open LongRange (Edge)

noncomputable section

/-- The unit walk has the unscaled annealed Brownian limit. -/
theorem normalizedUnitLaw_tendsto_proved
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hEK : LatticeProb.External.EthierKurtzRelativeCompactnessStopping)
    (hFdd : LatticeProb.External.EthierKurtzConvergenceFromFdd)
    {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a)
    (B : ProbabilityMeasure (LatticeProb.BrownianPath d))
    (hB : IsStandardBrownianLaw (B : Measure (LatticeProb.BrownianPath d))) :
    let A : ℝ := (d : ℝ) *
      (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
    Tendsto (normalizedUnitLaw hd P a hP) atTop
      (𝓝 (B.map (scaledBrownianPath (Real.sqrt (A / (2 * d)))))) := by
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  change Tendsto (normalizedUnitLaw hd P a hP) atTop
    (𝓝 (B.map (scaledBrownianPath (Real.sqrt (A / (2 * d))))))
  have hA : 0 < A := by
    dsimp [A]
    rw [← LatticeProb.Euclidean.Shell.unitBallVolume_eq_pi_div_gamma]
    exact mul_pos (Nat.cast_pos.mpr (by omega))
      (LatticeProb.Euclidean.Shell.unitBallVolume_pos d)
  have hspacing : Tendsto (fun n : ℕ => unscaledSpacing A n) atTop (𝓝[>] 0) :=
    (tendsto_unscaledSpacing hA).comp tendsto_natCast_atTop_atTop
  have hvalid : ∀ᶠ n : ℕ in atTop, unscaledSpacing A n ∈ Ioo (0 : ℝ) (1 / 2) := by
    filter_upwards [hspacing.eventually self_mem_nhdsWithin,
      hspacing.eventually ((eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
        nhdsWithin_le_nhds)] with n hn hn'
    exact ⟨hn, hn'⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hvalid
  let N := max N₀ 2
  let m : ℕ → ℕ := fun n => n + N
  have hm (n : ℕ) : 2 ≤ m n := (le_max_right _ _).trans (Nat.le_add_left _ _)
  have he (n : ℕ) : unscaledSpacing A (m n) ∈ Ioo (0 : ℝ) (1 / 2) :=
    hN₀ (m n) ((le_max_left _ _).trans (Nat.le_add_left _ _))
  let e : ℕ → Ioo (0 : ℝ) (1 / 2) := fun n => ⟨unscaledSpacing A (m n), he n⟩
  have hmAt : Tendsto (fun n : ℕ => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N)
  have he0 : Tendsto e atTop (Filter.comap Subtype.val (𝓝 0)) := by
    apply Filter.tendsto_comap_iff.mpr
    exact ((tendsto_unscaledSpacing hA).comp hmAt).mono_right nhdsWithin_le_nhds
  let s : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2)
  have hbase : Tendsto (fun n => annealedLaw hd P a hP (e n).2.1) atTop
      (𝓝 (B.map (scaledBrownianPath s))) := by
    exact (Statements.annealed_invariance_principle_proved hNash hDavies hEK hFdd
      hd P a hP B hB).2.comp he0
  have hclock : Tendsto (fun n => LongRange.kappa d (e n) * (e n : ℝ) ^ 2 *
      (m n : ℝ)) atTop (𝓝 1) := (tendsto_kappa_unscaledSpacing hd).comp hmAt
  exact normalizedUnitLaw_tendsto_of_spacing hd P a hP B A s hA
    (sqrt_mul_dimension_rpow hA.le) N e (fun n => by have := hm n; omega)
    (fun n => by simp only [e, m, Nat.cast_add]) hclock hbase

end
end LongRangeHeat
