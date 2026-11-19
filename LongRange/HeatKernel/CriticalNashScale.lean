import LongRange.HeatKernel.CriticalNashBalance
import LongRange.HeatKernel.CriticalHoldingReal
import LongRange.Support.Analysis.NashProfile

/-!
# Logarithmic scale for the critical Nash estimate

The radius scale is controlled by an increasing logarithmic scale.
-/

open Set
open LatticeProb
open scoped NNReal ENNReal

namespace LatticeProb.Graph.LongRangeKernel

/-- The logarithmic scale is increasing on the positive half-line. -/
theorem nashScale_strictMonoOn : StrictMonoOn nashScale (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro r hr
    exact (hasDerivAt_nashScale hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ioi, mem_Ioi] using hr
    rw [(hasDerivAt_nashScale hr').deriv]
    exact nashScaleDeriv_pos hr'

/-- The radius form of the critical scale is bounded by an increasing scale. -/
theorem criticalRadiusScale_le_nashScale {R : ℝ} (hR : 1 ≤ R) :
    R ^ 2 / Real.log (1 + R) ≤ 5 * nashScale ((1 + R) ^ 2) := by
  let v : ℝ := 1 + R
  have hv : 2 ≤ v := by dsimp [v]; linarith
  have hvpos : 0 < v := by linarith
  have hlog : 0 < Real.log v := Real.log_pos (by linarith)
  have hlog2 := nashScale_log_lower (u := 1) (by norm_num)
  have hlog2v : Real.log 2 ≤ Real.log v := Real.log_le_log (by norm_num) hv
  have hlogbound : Real.log (1 + v ^ 2) ≤ Real.log 2 + 2 * Real.log v := by
    have hh := Real.log_le_log (by positivity : 0 < 1 + v ^ 2)
      (show 1 + v ^ 2 ≤ 2 * v ^ 2 by nlinarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hden : 1 + Real.log (1 + v ^ 2) ≤ 5 * Real.log v := by
    norm_num at hlog2
    linarith
  have hv2 : R ^ 2 ≤ v ^ 2 := by dsimp [v]; nlinarith
  have hdenpos : 0 < 1 + Real.log (1 + v ^ 2) :=
    nashScale_denominator_pos (sq_pos_of_pos hvpos)
  change R ^ 2 / Real.log v ≤ 5 * (v ^ 2 / (1 + Real.log (1 + v ^ 2)))
  apply (div_le_iff₀ hlog).2
  rw [show 5 * (v ^ 2 / (1 + Real.log (1 + v ^ 2))) * Real.log v =
    (5 * v ^ 2 * Real.log v) / (1 + Real.log (1 + v ^ 2)) by ring]
  apply (le_div_iff₀ hdenpos).2
  nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hden),
    mul_nonneg (sub_nonneg.mpr hv2) hlog.le]

/-- The critical logarithmic Nash inequality, with constants uniform in the kernel. -/
theorem weightedLattice_critical_nash {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => |f x|) → 0 < ∑' x, f x ^ 2 →
        (∑' x, f x ^ 2) ≤ N * realKernelEnergy k f *
          nashScale ((D * (∑' x, |f x|) ^ 2 / (∑' x, f x ^ 2)) ^ (2 / (d : ℝ))) := by
  obtain ⟨D, N, hD, hN, hn⟩ := weightedLattice_critical_nash_at_radius hd C hC
  refine ⟨D, 5 * N, hD, by positivity, ?_⟩
  intro k hk hsym hlower f hf hQ
  have hE0 : 0 ≤ realKernelEnergy k f := by
    unfold realKernelEnergy
    exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => tsum_nonneg fun _ =>
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  have hE : 0 < realKernelEnergy k f := by
    refine lt_of_le_of_ne hE0 ?_
    intro heq
    have hz := weightedLattice_critical_square_sum_eq_zero_of_energy_eq_zero
      hd C hC k hk hsym hlower f hf heq.symm
    linarith
  obtain ⟨R, hR, hvol, hbound⟩ := hn k hk hsym hlower f hf hE
  let T : ℝ := D * (∑' x, |f x|) ^ 2 / (∑' x, f x ^ 2)
  have hV : 0 < latticeVolumeProfile d R := by unfold latticeVolumeProfile; positivity
  have hVT : latticeVolumeProfile d R ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hQ).2
    nlinarith [hvol]
  have hT : 0 < T := lt_of_lt_of_le hV hVT
  have hroot := le_rpow_inv_of_latticeVolumeProfile_le hd hR hVT
  have hsq : (1 + R) ^ 2 ≤ T ^ (2 / (d : ℝ)) := by
    have hh := pow_le_pow_left₀ (show 0 ≤ 1 + R by linarith) hroot 2
    have heq : (T ^ (1 / (d : ℝ))) ^ 2 = T ^ (2 / (d : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
      congr 1
      ring
    rwa [heq] at hh
  have hscale : nashScale ((1 + R) ^ 2) ≤ nashScale (T ^ (2 / (d : ℝ))) :=
    nashScale_strictMonoOn.monotoneOn (show (1 + R) ^ 2 ∈ Ioi 0 from
      sq_pos_of_pos (show 0 < 1 + R by linarith)) (show T ^ (2 / (d : ℝ)) ∈ Ioi 0 from
      Real.rpow_pos_of_pos hT _) hsq
  have hs := criticalRadiusScale_le_nashScale hR
  calc
    _ ≤ N * (R ^ 2 / Real.log (1 + R)) * realKernelEnergy k f := hbound
    _ ≤ N * (5 * nashScale ((1 + R) ^ 2)) * realKernelEnergy k f := by
      gcongr
    _ ≤ (5 * N) * realKernelEnergy k f * nashScale (T ^ (2 / (d : ℝ))) := by
      nlinarith [mul_nonneg (mul_nonneg hN.le hE.le) (sub_nonneg.mpr hscale)]

/-- The critical Nash inequality with the two-step Dirichlet energy. -/
theorem weightedLattice_critical_nash_two_step {d : ℕ} (hd : 0 < d)
    (C : ℝ) (hC : 0 < C) :
    ∃ D N : ℝ, 0 < D ∧ 0 < N ∧ ∀ (k : Site d → Site d → ℝ≥0∞),
      (∀ x, ∑' y, k x y = 1) → (∀ x y, k x y = k y x) →
      (∀ x y, ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d ((weightedLattice d hd).graph.dist x y : ℝ) *
          quadraticScale ((weightedLattice d hd).graph.dist x y : ℝ))) ≤ k x y) →
      ∀ f : lp (fun _ : Site d => ℝ) 2,
        Summable (fun x => |f x|) → 0 < ∑' x, f x ^ 2 →
        (∑' x, f x ^ 2) ≤ N *
          realKernelEnergy (densityPower (weightedLattice d hd).mass k 2) f *
          nashScale ((D * (∑' x, |f x|) ^ 2 / (∑' x, f x ^ 2)) ^ (2 / (d : ℝ))) := by
  obtain ⟨D, N, hD, hN, hn⟩ := weightedLattice_critical_nash hd C hC
  refine ⟨D, N * C, hD, by positivity, ?_⟩
  intro k hk hsym hlower f hf hQ
  have hhold (x : Site d) : ENNReal.ofReal C⁻¹ ≤ k x x := by
    simpa [SimpleGraph.dist_self, latticeVolumeProfile, quadraticScale] using hlower x x
  have hfin : (∑' x, ENNReal.ofReal (f x ^ 2)) < ∞ := by
    have hs : Summable (fun x => f x ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        f.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs]
    exact ENNReal.ofReal_lt_top
  have hcomp := lattice_real_energy_le_two_step hd k hk hsym C⁻¹ (by positivity) hhold f hfin
  have henergy : realKernelEnergy k f ≤
      C * realKernelEnergy (densityPower (weightedLattice d hd).mass k 2) f := by
    have hc := mul_le_mul_of_nonneg_left hcomp hC.le
    simpa [mul_assoc, hC.ne'] using hc
  have hnash := hn k hk hsym hlower f hf hQ
  have hscale : 0 ≤ nashScale ((D * (∑' x, |f x|) ^ 2 / (∑' x, f x ^ 2)) ^
      (2 / (d : ℝ))) := by
    have hT : 0 < D * (∑' x, |f x|) ^ 2 / (∑' x, f x ^ 2) := by
      have hsq := tsum_sq_le_tsum_abs_sq f hf
      exact div_pos (mul_pos hD (lt_of_lt_of_le hQ hsq)) hQ
    exact (nashScale_pos (Real.rpow_pos_of_pos hT _)).le
  nlinarith [mul_nonneg (mul_nonneg hN.le hscale) (sub_nonneg.mpr henergy)]

end LatticeProb.Graph.LongRangeKernel
