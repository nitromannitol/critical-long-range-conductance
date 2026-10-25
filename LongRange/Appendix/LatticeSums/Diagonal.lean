import LongRange.Appendix.LatticeSums.Symmetry
import LatticeProb.Euclidean.Estimates
import LatticeProb.Euclidean.Asymptotic

/-!
# The critical diagonal asymptotic

The kernel identity and physical rescaling turn the radial moment into the critical integer
shell sum. The uniform Euclidean shell asymptotic then gives the Gamma-normalized diagonal
coefficient with an error bounded by a dimension-dependent constant divided by `|log ε|`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

namespace LatticeSums

/-- Multiplying the critical kernel by the squared radius gives the critical radial power. -/
lemma kernel_mul_radius_sq {d : ℕ} {z : Fin d → ℝ} (hz : z ≠ 0) :
    jumpKernel z * radius z ^ 2 = radius z ^ (-(d : ℝ)) := by
  have hr : radius z ≠ 0 := (radius_pos hz).ne'
  rw [jumpKernel_of_ne_zero hz, Real.rpow_neg (radius_nonneg z), Real.rpow_natCast,
    pow_add]
  field_simp

/-- The scaled radial moment is exactly the critical sum over the unscaled integer lattice. -/
lemma scaled_radial_sum {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ε ^ d * ∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * radius (physical ε q) ^ 2 =
      ∑ q ∈ unitBallIndices d ε, radius (physical 1 q) ^ (-(d : ℝ)) := by
  have hs : ∑ q ∈ unitBallIndices d ε,
      jumpKernel (physical ε q) * radius (physical ε q) ^ 2 =
        ∑ q ∈ unitBallIndices d ε, radius (physical ε q) ^ (-(d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact kernel_mul_radius_sq (unitBallIndices_physical_ne_zero hε hq)
  rw [hs, Euclidean.Estimates.scaled_sum_eq hε, sub_self, Real.rpow_zero, one_mul]

/-- Each normalized diagonal moment is the critical integer shell sum divided by `d |log ε|`. -/
lemma diagonal_integer_sum {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    ε ^ d / |Real.log ε| *
        ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i ^ 2 =
      (∑ q ∈ unitBallIndices d ε, radius (physical 1 q) ^ (-(d : ℝ))) /
        ((d : ℝ) * |Real.log ε|) := by
  rw [diagonal_identity hε i, div_mul_eq_mul_div, scaled_radial_sum hε]

/-- The critical diagonal coefficients converge to the Euclidean unit-ball volume uniformly
in the coordinate, with an error at most `K(d) / |log ε|` for `0 < ε ≤ 1/2`. -/
theorem diagonal_asymptotic {d : ℕ} (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) (1 / 2) → ∀ i : Fin d,
      |ε ^ d / |Real.log ε| *
          ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i ^ 2 -
        Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)| ≤ K / |Real.log ε| := by
  obtain ⟨K, hK0, hK⟩ := Euclidean.Asymptotic.shell_sum_asymp (d := d) hd
  refine ⟨K, hK0, ?_⟩
  intro ε hε i
  have hR : 2 ≤ 1 / ε := by
    rw [le_div_iff₀ hε.1]
    linarith [hε.2]
  have hscale : 1 / (1 / ε) = ε := by simp only [one_div, inv_inv]
  have hlogε : Real.log ε ≤ 0 :=
    Real.log_nonpos hε.1.le (by linarith [hε.2])
  have hlogR : Real.log (1 / ε) = |Real.log ε| := by
    rw [one_div, Real.log_inv, abs_of_nonpos hlogε]
  have hlogpos : 0 < |Real.log ε| := by
    rw [← hlogR]
    exact Real.log_pos (by linarith [hR])
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hShell := hK (1 / ε) hR
  rw [hscale, Euclidean.Shell.unitBallVolume_eq_pi_div_gamma d, hlogR] at hShell
  have hnorm (S V D L : ℝ) (hD : D ≠ 0) (hL : L ≠ 0) :
      S / (D * L) - V = (S - D * V * L) / (D * L) := by
    field_simp [hD, hL]
  rw [diagonal_integer_sum hε.1 i, hnorm _ _ _ _ hdpos.ne' hlogpos.ne',
    abs_div, abs_of_pos (mul_pos hdpos hlogpos)]
  rw [div_le_div_iff₀ (mul_pos hdpos hlogpos) hlogpos]
  calc
    _ ≤ K * |Real.log ε| := mul_le_mul_of_nonneg_right hShell hlogpos.le
    _ ≤ K * ((d : ℝ) * |Real.log ε|) :=
      mul_le_mul_of_nonneg_left
        (calc
          |Real.log ε| = 1 * |Real.log ε| := by rw [one_mul]
          _ ≤ (d : ℝ) * |Real.log ε| :=
            mul_le_mul_of_nonneg_right hd1 hlogpos.le) hK0

end LatticeSums
end
end LongRange
