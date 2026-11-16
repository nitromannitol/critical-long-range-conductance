import LongRangeHeat.WalkPointwise
import LongRangeHeat.MeanOperator

/-!
# The one-time estimate for the walk started at the origin

For `F ∈ C_c^∞(ℝ^d)` and a time `τ`, the value `e^{τ L^ε} F(0) = E_0[F(X_τ)]` is compared with
`P̄_τ F(0)` by the Markov property at a small time `h`. The `ℓ²` distance between `e^{(τ-h) L^ε} F`
and `P̄_{τ-h} F` is transferred to the value at the origin by the on-diagonal bound, and the
displacement bound together with the regularity of the heat flow `P̄_{τ-h} F` controls the passage
from `E_0[P̄_{τ-h} F(X_h)]` to `P̄_{τ-h} F(0)`.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
  LatticeProb.Euclidean.Lattice LatticeProb.Heat LatticeProb.WhiteNoise Set
open scoped NNReal ENNReal ContDiff

noncomputable section

section Displacement

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- A Lipschitz bound and a tail bound control the deviation of an expectation from the value at
the base point. -/
theorem abs_integral_sub_le_of_lipschitz (μ : Measure S) [IsProbabilityMeasure μ] (G ρ : S → ℝ)
    (g0 : ℝ) {M L R : ℝ} (hM : ∀ y, |G y| ≤ M) (hg0 : |g0| ≤ M)
    (hL : ∀ y, |G y - g0| ≤ L * ρ y) (hL0 : 0 ≤ L) (hR : 0 ≤ R) :
    |∫ y, G y ∂μ - g0| ≤ L * R + 2 * M * μ.real {y | R < ρ y} := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg0)
  have hmeas : MeasurableSet {y | R < ρ y} := (Set.to_countable _).measurableSet
  have hpt : ∀ y, |G y - g0| ≤ L * R + 2 * M * Set.indicator {y | R < ρ y} (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : R < ρ y
    · simp only [Set.indicator_of_mem (show y ∈ {y | R < ρ y} from hy)]
      calc |G y - g0| ≤ |G y| + |g0| := abs_sub _ _
        _ ≤ 2 * M * 1 := by linarith [hM y]
        _ ≤ _ := by nlinarith [mul_nonneg hL0 hR]
    · simp only [Set.indicator_of_notMem (show y ∉ {y | R < ρ y} from hy), mul_zero, add_zero]
      exact (hL y).trans (mul_le_mul_of_nonneg_left (not_lt.mp hy) hL0)
  have hint : Integrable (fun y => G y - g0) μ :=
    (integrable_of_abs_le μ G hM).sub (integrable_const g0)
  have hind : Integrable (Set.indicator {y | R < ρ y} (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hint2 : Integrable (fun y => L * R + 2 * M *
      Set.indicator {y | R < ρ y} (fun _ => (1 : ℝ)) y) μ :=
    (integrable_const _).add (hind.const_mul (2 * M))
  calc |∫ y, G y ∂μ - g0| = |∫ y, (G y - g0) ∂μ| := by
        rw [integral_sub (integrable_of_abs_le μ G hM) (integrable_const g0)]
        simp
    _ ≤ ∫ y, |G y - g0| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, (L * R + 2 * M * Set.indicator {y | R < ρ y} (fun _ => (1 : ℝ)) y) ∂μ :=
        integral_mono hint.abs hint2 hpt
    _ = L * R + 2 * M * μ.real {y | R < ρ y} := by
        have h1 : ∫ y, 2 * M * Set.indicator {y | R < ρ y} (fun _ => (1 : ℝ)) y ∂μ =
            2 * M * μ.real {y | R < ρ y} := by
          rw [integral_const_mul, integral_indicator_const _ hmeas]
          simp
        rw [integral_add (integrable_const _) (hind.const_mul (2 * M)), h1]
        simp

/-- The semigroup is additive on bounded observables. -/
theorem walkOp_sub (rates : BoundedRates S) (t : ℝ≥0) {U G : S → ℝ} {M : ℝ}
    (hU : ∀ y, |U y| ≤ M) (hG : ∀ y, |G y| ≤ M) (x : S) :
    walkOp rates t (fun q => U q - G q) x = walkOp rates t U x - walkOp rates t G x :=
  integral_sub (integrable_of_abs_le _ U hU) (integrable_of_abs_le _ G hG)

end Displacement

section Continuum

variable {d : ℕ}

/-- The heat flow of a Lipschitz datum is Lipschitz with the same constant. -/
theorem abs_continuumHeat_sub_le (hd : 1 ≤ d) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) {L : ℝ} (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) {s : ℝ} (hs : 0 ≤ s)
    (y : Fin d → ℝ) : |continuumHeat F s y - continuumHeat F s 0| ≤ L * radius y := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hdiff : Differentiable ℝ (continuumHeat F s) :=
    (contDiff_continuumHeat hd hF hFc hs).differentiable (by simp)
  have hbound : ∀ x, ‖fderiv ℝ (continuumHeat F s) x‖ ≤ L := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ hL0 fun w => ?_
    rw [fderiv_continuumHeat_apply hd hF hFc hs, Real.norm_eq_abs]
    have hc : Continuous fun y => fderiv ℝ F y w :=
      (hF.continuous_fderiv (by simp)).clm_apply continuous_const
    exact abs_continuumHeat_le hd hc (M := L * ‖w‖) (fun y =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hL y) (norm_nonneg w))) hs x
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := continuumHeat F s)
    (s := Set.univ) (fun x _ => (hdiff x)) (fun x _ => hbound x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ y)
  rw [Real.norm_eq_abs, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_le_radius y) hL0)

/-- The heat flow is Lipschitz in time at every point, with the sup norm of `(2d)⁻¹ Δ F`. -/
theorem abs_continuumHeat_add_sub_le (hd : 1 ≤ d) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) {M₂ : ℝ} (hM₂ : ∀ y, |contOp d F y| ≤ M₂) {s h : ℝ} (hs : 0 < s)
    (hh : 0 ≤ h) (x : Fin d → ℝ) :
    |continuumHeat F (s + h) x - continuumHeat F s x| ≤ M₂ * h := by
  have hcont : ∀ r ∈ Set.Icc s (s + h), ContinuousAt (fun r => continuumHeat F r x) r :=
    fun r hr => (hasDerivAt_continuumHeat hd hF hFc (hs.trans_le hr.1) x).continuousAt
  have h1 := norm_image_sub_le_of_norm_deriv_right_le_segment (a := s) (b := s + h)
    (f := fun r => continuumHeat F r x)
    (f' := fun r => contOp d (continuumHeat F r) x) (C := M₂)
    (fun r hr => (hcont r hr).continuousWithinAt)
    (fun r hr => (hasDerivAt_continuumHeat hd hF hFc (hs.trans_le hr.1) x).hasDerivWithinAt)
    (fun r hr => by
      rw [Real.norm_eq_abs, contOp_continuumHeat hd hF hFc (hs.trans_le hr.1).le]
      exact abs_continuumHeat_le hd (contDiff_contOp hF).continuous hM₂ (hs.trans_le hr.1).le x)
    (s + h) ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs] at h1
  simpa using h1

end Continuum

section Lattice

variable {d : ℕ} {ε lam : ℝ} {a : LongRange.Edge d → ℝ}

/-- The on-diagonal bound for the walk with a fixed realization of the conductances. -/
def OnDiagonalBound (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (C : ℝ) : Prop :=
  ∀ h : ℝ≥0, ε ≤ h →
    (ε ^ d)⁻¹ * ((LongRange.walkRates hd hε hlam a ha).transitionKernel h 0).real {0} ≤
      C / (h : ℝ) ^ ((d : ℝ) / 2)

/-- The displacement bound for the walk with a fixed realization of the conductances. -/
def DisplacementBound (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (C : ℝ) : Prop :=
  ∀ h : ℝ≥0, 0 < h → ∀ R : ℝ, ε ≤ R →
    ((LongRange.walkRates hd hε hlam a ha).transitionKernel h 0).real
        {z | R < radius (physical ε (z - 0))} ≤
      C * h * (1 + Real.log (1 + R)) / R ^ 2

/-- Passing from `ℓ²` to the value at the origin: the difference of the expectations at time `h`
of two bounded observables is controlled by the `ℓ²` distance of the observables and the
on-diagonal bound. -/
theorem abs_walkOp_sub_le_of_onDiagonal (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : OnDiagonalBound hd hε hlam ha C) {h : ℝ≥0} (hεh : ε ≤ h + h)
    {U G : Site d → ℝ} (hmem : MemL2 fun q => U q - G q) :
    |walkOp (LongRange.walkRates hd hε hlam a ha) h (fun q => U q - G q) 0| ≤
      Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) * latticeNorm ε (fun q => U q - G q) := by
  set rates := LongRange.walkRates hd hε hlam a ha with hrates
  have hs := walkRates_q_symm hd hε hlam ha
  refine (abs_walkOp_le_sqrt rates hs h hmem 0).trans ?_
  have hεd : 0 < ε ^ d := pow_pos hε d
  have hQ : (rates.transitionKernel (h + h) 0).real {0} ≤
      ε ^ d * (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) := by
    have := hdiag (h + h) hεh
    rw [inv_mul_le_iff₀ hεd] at this
    exact this
  have hK : 0 ≤ C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2) :=
    div_nonneg hC (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
  have hS : 0 ≤ ∑' q, (U q - G q) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hnorm : latticeNorm ε (fun q => U q - G q) = Real.sqrt (ε ^ d * ∑' q, (U q - G q) ^ 2) :=
    rfl
  rw [hnorm, ← Real.sqrt_mul hK, ← Real.sqrt_mul measureReal_nonneg]
  apply Real.sqrt_le_sqrt
  calc (rates.transitionKernel (h + h) 0).real {0} * ∑' q, (U q - G q) ^ 2
      ≤ (ε ^ d * (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2))) * ∑' q, (U q - G q) ^ 2 :=
        mul_le_mul_of_nonneg_right hQ hS
    _ = _ := by ring

/-- The expectation at time `h` of the heat flow `P̄_s F` differs from its value at the origin by
at most `(L + 4 M C) h^{1/3}`, by the Lipschitz bound and the displacement bound at the radius
`h^{1/3}`. -/
theorem abs_walkOp_continuumHeat_sub_le (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C : ℝ} (hC : 0 ≤ C)
    (hdisp : DisplacementBound hd hε hlam ha C) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) {M L : ℝ} (hM : ∀ y, |F y| ≤ M) (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L)
    {s : ℝ} (hs : 0 ≤ s) {h : ℝ≥0} (hh : 0 < h) (hh1 : h ≤ 1)
    (hεR : ε ≤ (h : ℝ) ^ ((1 : ℝ) / 3)) :
    |walkOp (LongRange.walkRates hd hε hlam a ha) h (restrict ε (continuumHeat F s)) 0 -
        continuumHeat F s 0| ≤ (L + 4 * M * C) * (h : ℝ) ^ ((1 : ℝ) / 3) := by
  set rates := LongRange.walkRates hd hε hlam a ha with hrates
  set R : ℝ := (h : ℝ) ^ ((1 : ℝ) / 3) with hRdef
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hR0 : 0 < R := Real.rpow_pos_of_pos hh0 _
  have hR1 : R ≤ 1 := Real.rpow_le_one hh0.le (by exact_mod_cast hh1) (by norm_num)
  have hR3 : (h : ℝ) = R ^ 3 := by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
    norm_num
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hG : ∀ q : Site d, |restrict ε (continuumHeat F s) q| ≤ M := fun q =>
    abs_continuumHeat_le hd hF.continuous hM hs _
  have hmain := abs_integral_sub_le_of_lipschitz (rates.transitionKernel h 0)
    (restrict ε (continuumHeat F s)) (fun y => radius (physical ε (y - 0)))
    (continuumHeat F s 0) (M := M) (L := L) (R := R) hG
    (abs_continuumHeat_le hd hF.continuous hM hs _) (fun y => by
      have := abs_continuumHeat_sub_le hd hF hFc hL hs (physical ε y)
      simpa [restrict] using this) hL0 hR0.le
  have hdi := hdisp h hh R hεR
  have hlog : Real.log (1 + R) ≤ R := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + R by linarith)
    linarith
  have htail : (rates.transitionKernel h 0).real {z | R < radius (physical ε (z - 0))} ≤
      2 * C * R := by
    refine hdi.trans ?_
    rw [div_le_iff₀ (by positivity), hR3]
    have : C * R ^ 3 * (1 + Real.log (1 + R)) ≤ C * R ^ 3 * 2 := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [this, mul_nonneg hC (pow_nonneg hR0.le 3)]
  calc _ ≤ L * R + 2 * M * (rates.transitionKernel h 0).real
        {z | R < radius (physical ε (z - 0))} := hmain
    _ ≤ L * R + 2 * M * (2 * C * R) := by gcongr
    _ = _ := by ring

/-- **Step 1** of the proof of the finite-dimensional marginals, for a fixed realization of the
conductances: for `F ∈ C_c^∞(ℝ^d)`, times `h < τ` and `ε ≤ min(2h, h^{1/3})`, the value at the
origin of `e^{τ L^ε} F` differs from `P̄_τ F(0)` by at most
`√(C (2h)^{-d/2}) ‖e^{(τ-h) L^ε} F - P̄_{τ-h} F‖_{L²(εℤ^d)} + (L + 4 M C) h^{1/3} + M₂ h`. -/
theorem abs_latticeHeat_sub_continuumHeat_le (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : OnDiagonalBound hd hε hlam ha C) (hdisp : DisplacementBound hd hε hlam ha C)
    {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) {M L M₂ : ℝ}
    (hM : ∀ y, |F y| ≤ M) (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) (hM₂ : ∀ y, |contOp d F y| ≤ M₂)
    {τ h : ℝ≥0} (hh : 0 < h) (hh1 : h ≤ 1) (hhτ : h < τ) (hεh : ε ≤ h + h)
    (hεR : ε ≤ (h : ℝ) ^ ((1 : ℝ) / 3))
    (hmem : MemL2 fun q => latticeHeat ε a F ((τ - h : ℝ≥0) : ℝ) q -
      restrict ε (continuumHeat F ((τ - h : ℝ≥0) : ℝ)) q) :
    |latticeHeat ε a F τ 0 - continuumHeat F τ 0| ≤
      Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) *
        latticeNorm ε (fun q => latticeHeat ε a F ((τ - h : ℝ≥0) : ℝ) q -
          restrict ε (continuumHeat F ((τ - h : ℝ≥0) : ℝ)) q) +
      (L + 4 * M * C) * (h : ℝ) ^ ((1 : ℝ) / 3) + M₂ * h := by
  set rates := LongRange.walkRates hd hε hlam a ha with hrates
  have hτ : τ = h + (τ - h) := (add_tsub_cancel_of_le hhτ.le).symm
  have hspos : (0 : ℝ) < ((τ - h : ℝ≥0) : ℝ) := by exact_mod_cast tsub_pos_of_lt hhτ
  generalize τ - h = s at hτ hmem hspos ⊢
  subst hτ
  have hFq : ∀ q : Site d, |restrict ε F q| ≤ M := fun q => hM _
  have hheat : ∀ (t : ℝ≥0) q, latticeHeat ε a F t q = walkOp rates t (restrict ε F) q :=
    fun t q => latticeHeat_eq_integral hd hε hlam ha hFq t q
  have hG : ∀ q : Site d, |restrict ε (continuumHeat F s) q| ≤ M := fun q =>
    abs_continuumHeat_le hd hF.continuous hM s.coe_nonneg _
  have hU : ∀ q, |walkOp rates s (restrict ε F) q| ≤ M := fun q => abs_walkOp_le rates s hFq q
  have hUeq : (fun q => latticeHeat ε a F (s : ℝ) q - restrict ε (continuumHeat F s) q) =
      fun q => walkOp rates s (restrict ε F) q - restrict ε (continuumHeat F s) q := by
    funext q
    rw [hheat]
  rw [hUeq] at hmem ⊢
  have h1 : latticeHeat ε a F ((h + s : ℝ≥0) : ℝ) 0 =
      walkOp rates h (walkOp rates s (restrict ε F)) 0 := by
    rw [hheat, walkOp_add rates h s hFq]
  have hT1 := abs_walkOp_sub_le_of_onDiagonal hd hε hlam ha hC hdiag hεh hmem
  rw [walkOp_sub rates h hU hG] at hT1
  have hT2 := abs_walkOp_continuumHeat_sub_le hd hε hlam ha hC hdisp hF hFc hM hL s.coe_nonneg hh hh1 hεR
  rw [← hrates] at hT2
  have hT3 := abs_continuumHeat_add_sub_le hd hF hFc hM₂ hspos h.coe_nonneg 0
  have hcoe : (((h + s : ℝ≥0) : ℝ)) = (s : ℝ) + h := by push_cast; ring
  rw [h1, hcoe]
  calc _ = |(walkOp rates h (walkOp rates s (restrict ε F)) 0 - walkOp rates h
          (restrict ε (continuumHeat F s)) 0) +
        (walkOp rates h (restrict ε (continuumHeat F s)) 0 - continuumHeat F s 0) +
        (continuumHeat F s 0 - continuumHeat F (s + h) 0)| := by ring_nf
    _ ≤ |walkOp rates h (walkOp rates s (restrict ε F)) 0 - walkOp rates h
          (restrict ε (continuumHeat F s)) 0| +
        |walkOp rates h (restrict ε (continuumHeat F s)) 0 - continuumHeat F s 0| +
        |continuumHeat F s 0 - continuumHeat F (s + h) 0| := abs_add_three _ _ _
    _ ≤ _ := by
        rw [abs_sub_comm (continuumHeat F s 0)]
        linarith

end Lattice

end

end LongRangeHeat
