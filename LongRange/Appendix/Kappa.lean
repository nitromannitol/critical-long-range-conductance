import LongRange.Appendix.LatticeSums

/-!
# Bounds and normalization of the critical kernel

The Euclidean critical shell sum gives the logarithmic asymptotic of `κ_ε`.
A coordinate unit vector supplies a positive contribution at every admissible scale.
Coordinate symmetry then gives the exact normalized second moment.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The normalization is the scaled radial second moment of the critical kernel. -/
lemma kappa_eq_radial_sum {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    kappa d ε = ε ^ d * ∑ q ∈ unitBallIndices d ε,
      jumpKernel (physical ε q) * radius (physical ε q) ^ 2 := by
  unfold kappa
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [LatticeSums.kernel_mul_radius_sq (unitBallIndices_physical_ne_zero hε hq),
    Real.rpow_neg (radius_nonneg _), Real.rpow_natCast]

/-- Removing physical scaling identifies `κ_ε` with the critical integer shell sum. -/
lemma kappa_eq_integer_sum {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    kappa d ε = ∑ q ∈ unitBallIndices d ε,
      radius (physical 1 q) ^ (-(d : ℝ)) := by
  rw [kappa_eq_radial_sum hε, LatticeSums.scaled_radial_sum hε]

/-- One coordinate unit vector contributes exactly one to the normalization. -/
lemma one_le_kappa {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) : 1 ≤ kappa d ε := by
  classical
  let i : Fin d := ⟨0, hd⟩
  let q : Site d := Pi.single i 1
  have hq : q ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp only [q, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hi
  have hr : radius (physical 1 q) = 1 := by
    simp [radius, physical, q, Pi.single_apply]
  have hm : q ∈ unitBallIndices d ε := by
    rw [mem_unitBallIndices hε.1, radius_physical_eq_mul hε.1.le, hr, mul_one]
    exact ⟨hq, hε.2.le⟩
  rw [kappa_eq_integer_sum hε.1]
  calc
    1 = radius (physical 1 q) ^ (-(d : ℝ)) := by rw [hr, Real.one_rpow]
    _ ≤ ∑ q ∈ unitBallIndices d ε, radius (physical 1 q) ^ (-(d : ℝ)) :=
      Finset.single_le_sum (fun q _ => Real.rpow_nonneg (radius_nonneg _) _) hm

/-- The critical normalization is strictly positive in every positive dimension. -/
theorem kappa_pos {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) : 0 < kappa d ε :=
  lt_of_lt_of_le zero_lt_one (one_le_kappa hd hε)

/-- Proposition A.1 at the critical exponent bounds the normalization logarithmically. -/
theorem kappa_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      kappa d ε ≤ C * (1 + |Real.log ε|) := by
  obtain ⟨C, hC, hbound⟩ := (lattice_sums d).1 d (Nat.cast_nonneg d)
  refine ⟨C, hC, ?_⟩
  intro ε hε
  simpa only [kappa, Real.rpow_natCast, one_div, lt_self_iff_false, ite_false,
    ite_true] using (hbound ε hε).1

/-- The critical normalization has the Euclidean ball-volume coefficient and bounded error. -/
theorem kappa_asymptotic {d : ℕ} (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) (1 / 2) →
      |kappa d ε - d *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * (|Real.log ε|)| ≤ K := by
  obtain ⟨K, hK, hbound⟩ := Euclidean.Asymptotic.shell_sum_asymp hd
  refine ⟨K, hK, ?_⟩
  intro ε hε
  have hR : 2 ≤ 1 / ε := by
    rw [le_div_iff₀ hε.1]
    linarith [hε.2]
  have hlog : Real.log (1 / ε) = |Real.log ε| := by
    rw [one_div, Real.log_inv, abs_of_nonpos
      (Real.log_nonpos hε.1.le (by linarith [hε.2]))]
  have h := hbound (1 / ε) hR
  rw [show 1 / (1 / ε) = ε by simp only [one_div, inv_inv],
    Euclidean.Shell.unitBallVolume_eq_pi_div_gamma, hlog] at h
  rw [kappa_eq_integer_sum hε.1]
  exact h

/-- The asymptotic and the unit-vector contribution give a uniform logarithmic lower bound. -/
theorem le_kappa {d : ℕ} (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      c * (1 + |Real.log ε|) ≤ kappa d ε := by
  obtain ⟨K, hK, hbound⟩ := kappa_asymptotic hd
  let A : ℝ := (d : ℝ) * Euclidean.Shell.unitBallVolume d
  have hA : 0 < A := mul_pos (Nat.cast_pos.mpr (by omega))
    (Euclidean.Shell.unitBallVolume_pos d)
  have hden : 0 < A + K + 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (A / (A + K + 1)) (1 / (1 + Real.log 2)),
    lt_min (div_pos hA hden) (div_pos zero_lt_one (by linarith)), ?_⟩
  intro ε hε
  have hk : 1 ≤ kappa d ε := one_le_kappa hd hε
  have hL : 0 ≤ 1 + |Real.log ε| := by positivity
  by_cases hsmall : ε ≤ 1 / 2
  · have hb := (abs_le.mp (hbound ε ⟨hε.1, hsmall⟩)).1
    rw [← Euclidean.Shell.unitBallVolume_eq_pi_div_gamma] at hb
    change -K ≤ kappa d ε - A * |Real.log ε| at hb
    calc
      _ ≤ A / (A + K + 1) * (1 + |Real.log ε|) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hL
      _ ≤ kappa d ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        have hprod := mul_nonneg (show 0 ≤ A + K by linarith only [hA, hK])
          (show 0 ≤ kappa d ε - 1 by linarith only [hk])
        nlinarith only [hb, hprod]
  · have hlog : |Real.log ε| ≤ Real.log 2 := by
      rw [abs_of_neg (Real.log_neg hε.1 hε.2)]
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
        (lt_of_not_ge hsmall).le
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub] at h
      linarith
    calc
      _ ≤ 1 / (1 + Real.log 2) * (1 + |Real.log ε|) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hL
      _ ≤ 1 := by
        rw [one_div_mul_eq_div, div_le_one (by linarith : 0 < 1 + Real.log 2)]
        linarith
      _ ≤ kappa d ε := hk

/-- Coordinate symmetry and the definition of `κ_ε` normalize each diagonal to `1/d`. -/
theorem second_moment_normalized {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (i j : Fin d) :
    ε ^ d / kappa d ε * ∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * physical ε q i * physical ε q j =
      if i = j then 1 / (d : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp_rw [mul_assoc, ← pow_two]
    have hr := kappa_eq_radial_sum (d := d) hε.1
    rw [LatticeSums.radial_sum_eq hε.1 i] at hr
    have hk := (kappa_pos hd hε).ne'
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply (eq_div_iff hd0).mpr
    calc
      ε ^ d / kappa d ε *
          (∑ q ∈ unitBallIndices d ε,
            jumpKernel (physical ε q) * physical ε q i ^ 2) * d =
          (ε ^ d * ((d : ℝ) * ∑ q ∈ unitBallIndices d ε,
            jumpKernel (physical ε q) * physical ε q i ^ 2)) / kappa d ε := by ring
      _ = 1 := by rw [← hr, div_self hk]
  · rw [if_neg hij, LatticeSums.mixed_sum_eq_zero hε.1 hij, mul_zero]

end
end LongRange
