import LongRange.Dirichlet.ShortDifference
import LongRange.Dirichlet.ColumnSquares
import LongRange.Dirichlet.McDiarmid
import LongRange.Dirichlet.Hoeffding

/-!
# Concentration of the short-range energy

Finite coordinate influences and the square sum of coefficient columns give the
short-range concentration estimate of Proposition 3.3.
-/

namespace LongRange.Dirichlet

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped BigOperators

noncomputable section

/-- The finite short-range energy is a continuous polynomial in its coordinates. -/
theorem continuous_shortEnergyFn {d : ℕ} (ε : ℝ) (U : Set (Fin d → ℝ))
    (S : Finset (Site d)) (J : Finset (Cycle.indexSet ε U)) (p : Fin d → ℝ)
    (m : ℝ) : Continuous (shortEnergyFn ε U S J p m) := by
  classical
  unfold shortEnergyFn nnEnergy
  fun_prop

/-- McDiarmid and the column-square estimate give short-range energy concentration. -/
theorem shortPart_concentration (d : ℕ) (lam R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a) (ε : ℝ)
      (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (U : Set (Fin d → ℝ))
      (hU : Bornology.IsBounded U), euclideanDiam U ≤ R → ∀ p : Fin d → ℝ,
        OsBound P 2 (C * radius p ^ 2 * ε ^ ((d : ℝ) / 2))
          (fun ω => |nnEnergy ε (latticeSet_finite hε.1 hU).toFinset
              (shortDefect ε U (a ω) (meanConductance P hA.one_le_dim a) p) -
            ∫ ω', nnEnergy ε (latticeSet_finite hε.1 hU).toFinset
              (shortDefect ε U (a ω') (meanConductance P hA.one_le_dim a) p) ∂P|) := by
  classical
  by_cases hd : 1 ≤ d
  · obtain ⟨A, hApos, hdiff⟩ := shortEnergyFn_update_le hd
    obtain ⟨B, hB, hcol⟩ := short_column_sq_sum_bound d hd R
    obtain ⟨c, hc, hk⟩ := le_kappa hd
    obtain ⟨M, hM, hmc⟩ := edge_mcdiarmid
    let D := 2 * lam⁻¹ ^ 2 * A * Real.sqrt B / c
    refine ⟨M * D + 1, by dsimp [D]; positivity, ?_⟩
    intro Ω _ P a hA ε hε U hU hdiam p
    let S := (latticeSet_finite hε.1 hU).toFinset
    let J := (shortIndex_finite hε.1 hU).toFinset
    let m := meanConductance P hA.one_le_dim a
    let col : J → ℝ := fun j => ∑ x ∈ S, ∑ i : Fin d,
      (|shortCoeff ε U p x (unit i) j| + |shortCoeff ε U p x (-unit i) j|)
    let w := ε ^ (3 * d + 2) / kappa d ε *
      (2 * lam⁻¹ ^ 2 * (A * radius p * ε ^ (-((d : ℝ) + 1)) *
        (1 + |Real.log ε|)))
    have heps := hε.1
    have hp := radius_nonneg p
    have hkap := kappa_pos hd hε
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have hcols : (∑ j : J, col j ^ 2) ≤
        B * radius p ^ 2 * ε ^ (-(3 * (d : ℝ) + 2)) := by
      calc
        _ = ∑ r ∈ J, (∑ x ∈ S, ∑ i : Fin d,
            (|shortCoeff ε U p x (unit i) r| +
              |shortCoeff ε U p x (-unit i) r|)) ^ 2 :=
          Finset.sum_coe_sort J (fun r => (∑ x ∈ S, ∑ i : Fin d,
            (|shortCoeff ε U p x (unit i) r| +
              |shortCoeff ε U p x (-unit i) r|)) ^ 2)
        _ ≤ _ := hcol ε hε U hU hdiam p
    have hbound := hmc hA
      (fun j : J => edgeAdd j.1.1.1 j.1.1.2 j.1.2.2.1)
      ((reprEdge_injective ε U).comp Subtype.val_injective)
      (shortEnergyFn ε U S J p m)
      (continuous_shortEnergyFn ε U S J p m).measurable
      (fun j => w * col j) (fun j => mul_nonneg hw (by dsimp [col]; positivity))
      (fun j y t hy ht => by
        simpa only [w, col, S, J, mul_assoc] using
          hdiff ε hε U hU p hA.lam_pos hA.mean_mem_Icc y hy j ht)
    have hsum : (∑ j : J, (w * col j) ^ 2) = w ^ 2 * ∑ j : J, col j ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    let q := ε ^ (-(3 * (d : ℝ) + 2) / 2)
    have hq : 0 ≤ q := Real.rpow_nonneg hε.1.le _
    have hq2 : q ^ 2 = ε ^ (-(3 * (d : ℝ) + 2)) := by
      dsimp only [q]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.1.le]
      congr 1
      ring
    have hsqrt : Real.sqrt (∑ j : J, col j ^ 2) ≤
        Real.sqrt B * radius p * q := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      calc
        _ ≤ B * radius p ^ 2 * ε ^ (-(3 * (d : ℝ) + 2)) := hcols
        _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hB.le, hq2]
    have hscale : ε ^ (3 * d + 2) * ε ^ (-((d : ℝ) + 1)) * q =
        ε ^ ((d : ℝ) / 2) := by
      dsimp only [q]
      rw [← Real.rpow_natCast, ← Real.rpow_add hε.1,
        ← Real.rpow_add hε.1]
      congr 1
      push_cast
      ring
    have hlog : (1 + |Real.log ε|) / kappa d ε ≤ 1 / c := by
      apply (div_le_div_iff₀ (kappa_pos hd hε) hc).mpr
      simpa only [one_mul, mul_one, mul_comm] using hk ε hε
    have hnorm : w * (Real.sqrt B * radius p * q) ≤
        D * radius p ^ 2 * ε ^ ((d : ℝ) / 2) := by
      calc
        _ = (2 * lam⁻¹ ^ 2 * A * Real.sqrt B * radius p ^ 2 *
            ε ^ ((d : ℝ) / 2)) * ((1 + |Real.log ε|) / kappa d ε) := by
          rw [← hscale]
          dsimp [w]
          ring
        _ ≤ (2 * lam⁻¹ ^ 2 * A * Real.sqrt B * radius p ^ 2 *
            ε ^ ((d : ℝ) / 2)) * (1 / c) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by dsimp [D]; ring
    have hroot : Real.sqrt (∑ j : J, (w * col j) ^ 2) ≤
        D * radius p ^ 2 * ε ^ ((d : ℝ) / 2) := by
      rw [hsum, Real.sqrt_mul (sq_nonneg w), Real.sqrt_sq hw]
      exact (mul_le_mul_of_nonneg_left hsqrt hw).trans hnorm
    have hscaleBound : M * Real.sqrt (∑ j : J, (w * col j) ^ 2) ≤
        (M * D + 1) * radius p ^ 2 * ε ^ ((d : ℝ) / 2) := by
      calc
        _ ≤ M * (D * radius p ^ 2 * ε ^ ((d : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hroot hM.le
        _ ≤ _ := by
          have hp := mul_nonneg (sq_nonneg (radius p))
            (Real.rpow_nonneg hε.1.le ((d : ℝ) / 2))
          nlinarith only [hp]
    have hfinal := OsBound.mono hscaleBound
      (mul_nonneg hM.le (Real.sqrt_nonneg _)) (fun _ => le_rfl) hbound
    simpa only [nnEnergy_shortDefect_eq hε.1 hU, S, J, m] using hfinal
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hd hA.one_le_dim).elim

end

end LongRange.Dirichlet
