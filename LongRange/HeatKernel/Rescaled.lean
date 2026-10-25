import LongRange.HeatKernel.UniformOffDiagonal
import LongRange.Appendix.Kappa
import LatticeProb.Prob.JumpChain.TimeScale
import LatticeProb.Prob.JumpChain.PositionLaw

/-!
# The rescaled heat kernel

Homogeneity of the Euclidean jump kernel identifies the actual rescaled walk
with a deterministic time change of the unit walk. The density is taken with
respect to physical lattice volume, giving the factor `ε⁻ᵈ`.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- The actual rescaled walk kernel is the unit kernel at the rescaled time. -/
theorem walk_transitionKernel_eq_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (t : ℝ≥0) :
    (walkRates hd hε.1 hlam a ha).transitionKernel t =
      (unitRates hd hlam a ha).transitionKernel
        ((NNReal.mk (1 / (kappa d ε * ε ^ 2)) (by positivity [kappa_pos hd hε])) * t) := by
  apply LatticeProb.JumpChain.BoundedRates.transitionKernel_eq_timeScale
  · exact one_div_pos.mpr (mul_pos (kappa_pos hd hε) (pow_pos hε.1 _))
  · intro x y
    change walkRate ε a x y = _ * unitRate a x y
    rw [walkRate_eq_smul_unitRate hε.1]
    congr 1
    rw [pow_add]
    field_simp [hε.1.ne']

/-- Physical volume converts the actual walk singleton mass into its density. -/
def rescaledDensity (hd : 1 ≤ d) {ε lam : ℝ} (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (t : ℝ≥0) (x y : Site d) : ℝ :=
  (ε ^ d)⁻¹ * ((walkRates hd hε.1 hlam a ha).transitionKernel t x).real {y}

/-- The density definition agrees with the actual unit walk after time change. -/
theorem rescaledDensity_eq_unit (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (t : ℝ≥0) (x y : Site d) :
    rescaledDensity hd hε hlam a ha t x y = (ε ^ d)⁻¹ *
      ((unitRates hd hlam a ha).transitionKernel
        (NNReal.mk (1 / (kappa d ε * ε ^ 2))
          (by positivity [kappa_pos hd hε]) * t) x).real {y} := by
  rw [rescaledDensity, walk_transitionKernel_eq_unit hd hε hlam a ha]

/-- Multiplication by the volume of one atom recovers the actual transition mass. -/
theorem rescaledDensity_mul_volume (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (t : ℝ≥0) (x y : Site d) :
    ε ^ d * rescaledDensity hd hε hlam a ha t x y =
      ((walkRates hd hε.1 hlam a ha).transitionKernel t x).real {y} := by
  rw [rescaledDensity, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hε.1.ne'), one_mul]

/-- The density is characterized by the physical position law of the actual walk. -/
theorem rescaledDensity_eq_position_mass (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (t : ℝ≥0) (x y : Site d) :
    rescaledDensity hd hε hlam a ha t x y = (ε ^ d)⁻¹ *
      ((walkRates hd hε.1 hlam a ha).regularLaw (MeasureTheory.Measure.dirac x)).real
        {h | physical ε (h.position t) = physical ε y} := by
  have he : {h : JumpChain.RegularHistory (Site d) |
      physical ε (h.position t) = physical ε y} = {h | h.position t = y} := by
    ext h
    exact (physical_injective hε.1).eq_iff
  rw [he, MeasureTheory.measureReal_def,
    (walkRates hd hε.1 hlam a ha).regularLaw_position]
  change _ = (ε ^ d)⁻¹ * (((MeasureTheory.Measure.dirac x).bind
    ((walkRates hd hε.1 hlam a ha).transitionKernel t)) {y}).toReal
  rw [MeasureTheory.Measure.dirac_bind
    (ProbabilityTheory.Kernel.measurable _) x]
  rfl

/-- Scaling the on-diagonal profile cancels physical lattice volume exactly. -/
theorem rescaled_diagonal_profile {ε k t : ℝ} (hε : 0 < ε) (hk : 0 < k)
    (ht : 0 ≤ t) (d : ℕ) :
    (ε ^ d)⁻¹ * (1 + t / (k * ε ^ 2) * Real.log (2 + t / (k * ε ^ 2))) ^
      (-((d : ℝ) / 2)) =
    (ε ^ 2 + t / k * Real.log (2 + t / (k * ε ^ 2))) ^ (-((d : ℝ) / 2)) := by
  have hb : 0 ≤ 1 + t / (k * ε ^ 2) * Real.log (2 + t / (k * ε ^ 2)) := by
    have hs : 0 ≤ t / (k * ε ^ 2) := by positivity
    have hl : 0 ≤ Real.log (2 + t / (k * ε ^ 2)) :=
      Real.log_nonneg (by linarith)
    positivity
  have he : ε ^ 2 + t / k * Real.log (2 + t / (k * ε ^ 2)) =
      ε ^ 2 * (1 + t / (k * ε ^ 2) * Real.log (2 + t / (k * ε ^ 2))) := by
    field_simp
  rw [he, Real.mul_rpow (by positivity) hb]
  congr 1
  rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
  have hexp : (2 : ℝ) * (-((d : ℝ) / 2)) = -(d : ℝ) := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hexp, Real.rpow_neg hε.le, Real.rpow_natCast]

/-- Scaling the spatial profile cancels physical lattice volume exactly. -/
theorem rescaled_spatial_profile {ε k t r : ℝ} (hε : 0 < ε) (hk : 0 < k)
    (hr : 0 < r) (d : ℕ) :
    (ε ^ d)⁻¹ * (t / (k * ε ^ 2) * Real.log (2 + r) / r ^ (d + 2)) =
      t / k * Real.log (2 + (ε * r) / ε) / (ε * r) ^ (d + 2) := by
  rw [mul_div_cancel_left₀ r hε.ne', mul_pow, pow_add]
  field_simp
  ring

/-- One constant gives the source rescaled minimum bound for every scale and field. -/
theorem rescaledDensity_offDiagonal_uniform
    (hMSCUniform : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (d : ℕ) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo 0 1,
      ∀ a : Edge d → ℝ, ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
      ∀ t : ℝ≥0, 0 < t → ∀ x y : Site d, x ≠ y →
      rescaledDensity hd hε hlam a ha t x y ≤ C * min
        ((ε ^ 2 + t / kappa d ε * Real.log (2 + t / (kappa d ε * ε ^ 2))) ^
          (-((d : ℝ) / 2)))
        (t / kappa d ε * Real.log (2 + radius (physical ε (y - x)) / ε) /
          radius (physical ε (y - x)) ^ (d + 2)) := by
  obtain ⟨C, hC, hbound⟩ :=
    unitHeat_offDiagonal_uniform hMSCUniform hNash hDavies d hd hlam
  refine ⟨C, hC, ?_⟩
  intro ε hε a ha t ht x y hxy
  have hk := kappa_pos hd hε
  let s : ℝ≥0 := NNReal.mk ((t : ℝ) / (kappa d ε * ε ^ 2)) (by positivity)
  have hs : 0 < s := by
    change 0 < (t : ℝ) / (kappa d ε * ε ^ 2)
    exact div_pos ht (mul_pos hk (pow_pos hε.1 _))
  have htime : (s : ℝ) = (t : ℝ) / (kappa d ε * ε ^ 2) := rfl
  have hclock : (NNReal.mk (1 / (kappa d ε * ε ^ 2)) (by positivity)) * t = s := by
    apply NNReal.coe_injective
    change 1 / (kappa d ε * ε ^ 2) * (t : ℝ) = (t : ℝ) / (kappa d ε * ε ^ 2)
    ring
  have hb := mul_le_mul_of_nonneg_left (hbound a ha s hs x y hxy)
    (inv_nonneg.mpr (pow_nonneg hε.1.le d))
  rw [rescaledDensity_eq_unit hd hε hlam a ha, hclock]
  change (ε ^ d)⁻¹ * ((unitRates hd hlam a ha).transitionKernel s x).real {y} ≤ _
  refine hb.trans_eq ?_
  rw [htime, mul_left_comm ((ε ^ d)⁻¹) C,
    mul_min_of_nonneg _ _ (inv_nonneg.mpr (pow_nonneg hε.1.le d)),
    rescaled_diagonal_profile hε.1 hk t.coe_nonneg d,
    rescaled_spatial_profile hε.1 hk (lt_of_lt_of_le zero_lt_one
      (one_le_radius_displacement hxy)) d,
    radius_physical_eq_mul hε.1.le]

end

end LongRange
