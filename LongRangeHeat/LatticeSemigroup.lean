import LongRangeHeat.Defs
import LongRangeHeat.Dirichlet
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-!
# Initial value of the lattice heat series

The exponential series has the prescribed initial value at time zero.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LongRange

/-- The lattice heat series starts from the restriction of the initial data. -/
theorem latticeHeat_zero {d : ℕ} (ε : ℝ) (a : LongRange.Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) : latticeHeat ε a f 0 = restrict ε f := by
  funext q
  unfold latticeHeat
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- A geometric bound on the iterates implies convergence of the lattice heat series. -/
theorem summable_latticeHeat_of_iterate_bound {d : ℕ} (ε : ℝ)
    (a : LongRange.Edge d → ℝ) (f : (Fin d → ℝ) → ℝ) (t : ℝ) (q : LatticeProb.Site d)
    {M K : ℝ} (_hM : 0 ≤ M) (_hK : 0 ≤ K)
    (h : ∀ n : ℕ, |(LongRange.generator ε a)^[n] (restrict ε f) q| ≤ M * K ^ n) :
    Summable (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
      (LongRange.generator ε a)^[n] (restrict ε f) q) := by
  apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial (|t| * K)).mul_left M)
  intro n
  have hf : |(n.factorial : ℝ)| = n.factorial := abs_of_nonneg (Nat.cast_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, hf]
  have hfac : 0 ≤ |t| ^ n / (n.factorial : ℝ) := by positivity
  calc
    |t| ^ n / (n.factorial : ℝ) * |(LongRange.generator ε a)^[n] (restrict ε f) q|
        ≤ |t| ^ n / (n.factorial : ℝ) * (M * K ^ n) := mul_le_mul_of_nonneg_left (h n) hfac
    _ = M * ((|t| * K) ^ n / (n.factorial : ℝ)) := by rw [mul_pow]; ring


noncomputable section

variable {d : ℕ}

/-- The generator is bounded uniformly in the lattice site on bounded functions. -/
theorem abs_generator_le {d : ℕ} (hd : 1 ≤ d) {ε lam M : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {v : LatticeProb.Site d → ℝ}
    (hM : 0 ≤ M) (hv : ∀ q, |v q| ≤ M) (q : LatticeProb.Site d) :
    |LongRange.generator ε a v q| ≤
      (2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
        ∑' w : LatticeProb.Site d, LongRange.jumpKernel (physical ε w)) * M := by
  let J := fun w : LatticeProb.Site d => LongRange.jumpKernel (physical ε w)
  have ht := (summable_jumpKernel hd hε).mul_left (lam⁻¹ * (2 * M))
  have hj : ∀ w, 0 ≤ J w := fun w => jumpKernel_nonneg _
  have hbound : ∀ w : LatticeProb.Site d,
      |if hw : w = 0 then 0 else
        a (LongRange.edgeAdd q w hw) * (v (q + w) - v q) * J w| ≤
      (lam⁻¹ * (2 * M)) * J w := by
    intro w
    by_cases hw : w = 0
    · subst w
      simp only [↓reduceDIte, abs_zero]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le) (by positivity)) (hj 0)
    · simp only [hw, ↓reduceDIte, abs_mul,
        abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg (hj w)]
      apply mul_le_mul_of_nonneg_right _ (hj w)
      apply mul_le_mul (ha _).2 _ (abs_nonneg _) (inv_nonneg.mpr hlam.le)
      exact (abs_sub _ _).trans (by linarith [hv (q + w), hv q])
  have hs : Summable (fun w : LatticeProb.Site d => if hw : w = 0 then 0 else
      a (LongRange.edgeAdd q w hw) * (v (q + w) - v q) * J w) := by
    apply ht.of_norm_bounded
    intro w
    simpa only [Real.norm_eq_abs] using hbound w
  unfold LongRange.generator
  rw [abs_mul]
  calc
    _ ≤ |ε ^ d / LongRange.kappa d ε| *
        (∑' w : LatticeProb.Site d, (lam⁻¹ * (2 * M)) * J w) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum hbound ht)
    _ = _ := by rw [tsum_mul_left]; ring

/-- Iterates of the generator have a uniform geometric bound. -/
theorem abs_generator_iterate_le {d : ℕ} (hd : 1 ≤ d) {ε lam M : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {v : LatticeProb.Site d → ℝ}
    (hM : 0 ≤ M) (hv : ∀ q, |v q| ≤ M) (n : ℕ) (q : LatticeProb.Site d) :
    |(LongRange.generator ε a)^[n] v q| ≤ M *
      (2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
        ∑' w : LatticeProb.Site d, LongRange.jumpKernel (physical ε w)) ^ n := by
  let K : ℝ := 2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
    ∑' w : LatticeProb.Site d, LongRange.jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg (fun w => jumpKernel_nonneg _))
  induction n generalizing q with
  | zero => simpa using hv q
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ K * (M * K ^ n) :=
        abs_generator_le hd hε hlam ha (mul_nonneg hM (pow_nonneg hK _)) ih q
      _ = M * K ^ (n + 1) := by rw [pow_succ]; ring


/-- The lattice heat series converges for bounded initial data. -/
theorem summable_latticeHeat_of_bounded {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : (Fin d → ℝ) → ℝ}
    (hf : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M) (t : ℝ) (q : Site d) :
    Summable (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
      (LongRange.generator ε a)^[n] (restrict ε f) q) := by
  obtain ⟨M, hM, hf⟩ := hf
  let K : ℝ := 2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
    ∑' w : Site d, LongRange.jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg (fun w => jumpKernel_nonneg _))
  apply summable_latticeHeat_of_iterate_bound ε a f t q hM hK
  intro n
  exact abs_generator_iterate_le hd hε hlam ha hM (fun q => hf (physical ε q)) n q

/-- The lattice heat series converges for continuous compactly supported initial data. -/
theorem summable_latticeHeat {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfcompact : HasCompactSupport f) (t : ℝ) (q : Site d) :
    Summable (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
      (LongRange.generator ε a)^[n] (restrict ε f) q) := by
  let F := ofCompactSupport f hf hfcompact
  apply summable_latticeHeat_of_bounded hd hε hlam ha
    ⟨‖F‖, norm_nonneg _, ?_⟩ t q
  intro x
  simpa [F, ofCompactSupport, Real.norm_eq_abs] using
    BoundedContinuousFunction.norm_coe_le_norm F x


/-- The lattice heat series has an exponential bound, uniform in the lattice site. -/
theorem abs_latticeHeat_le {d : ℕ} (hd : 1 ≤ d) {ε lam M : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : (Fin d → ℝ) → ℝ}
    (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M) (t : ℝ) (q : Site d) :
    |latticeHeat ε a f t q| ≤ M * Real.exp (|t| *
      (2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
        ∑' w : Site d, LongRange.jumpKernel (physical ε w))) := by
  let K : ℝ := 2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
    ∑' w : Site d, LongRange.jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg (fun w => jumpKernel_nonneg _))
  have hs := summable_latticeHeat_of_bounded hd hε hlam ha ⟨M, hM, hf⟩ t q
  have ht := (Real.summable_pow_div_factorial (|t| * K)).mul_left M
  unfold latticeHeat
  calc
    _ ≤ ∑' n : ℕ, |t ^ n / (n.factorial : ℝ) *
        (LongRange.generator ε a)^[n] (restrict ε f) q| := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, M * ((|t| * K) ^ n / (n.factorial : ℝ)) := by
      apply hs.norm.tsum_le_tsum _ ht
      intro n
      simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _)]
      calc
        _ ≤ |t| ^ n / (n.factorial : ℝ) * (M * K ^ n) :=
          mul_le_mul_of_nonneg_left
            (abs_generator_iterate_le hd hε hlam ha hM (fun q => hf (physical ε q)) n q)
            (by positivity)
        _ = M * ((|t| * K) ^ n / (n.factorial : ℝ)) := by
          rw [mul_pow]
          ring
    _ = _ := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ]
      congr 1
      exact (NormedSpace.expSeries_div_hasSum_exp (|t| * K)).tsum_eq


/-- The lattice heat series is uniformly bounded on bounded positive time intervals. -/
theorem latticeHeat_bounded_on_interval {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfcompact : HasCompactSupport f) (T : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ q : Site d, |latticeHeat ε a f t q| ≤ C := by
  let F := ofCompactSupport f hf hfcompact
  let K : ℝ := 2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
    ∑' w : Site d, LongRange.jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg (fun w => jumpKernel_nonneg _))
  have hF : ∀ x, |f x| ≤ ‖F‖ := by
    intro x
    simpa [F, ofCompactSupport, Real.norm_eq_abs] using
      BoundedContinuousFunction.norm_coe_le_norm F x
  refine ⟨‖F‖ * Real.exp (T * K), fun t ht q => ?_⟩
  calc
    _ ≤ ‖F‖ * Real.exp (|t| * K) := abs_latticeHeat_le hd hε hlam ha (norm_nonneg _) hF t q
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by simpa [abs_of_nonneg ht.1] using ht.2) hK))
      (norm_nonneg _)

end

end LongRangeHeat
