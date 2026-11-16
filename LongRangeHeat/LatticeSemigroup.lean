import LongRangeHeat.Defs
import LongRangeHeat.Dirichlet
import LongRange.Appendix.LatticeCount
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lattice heat series

Bounds on the lattice generator and the exponential series for the heat equation.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LongRange Set

/-- The lattice heat series starts from the restriction of the initial data. -/
theorem latticeHeat_zero {d : ℕ} (ε : ℝ) (a : LongRange.Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) : latticeHeat ε a f 0 = restrict ε f := by
  funext q
  unfold latticeHeat
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- A compactly supported function restricts to a square-summable lattice function. -/
theorem memL2_restrict {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : (Fin d → ℝ) → ℝ} (hf : HasCompactSupport f) : MemL2 (restrict ε f) := by
  classical
  let S := latticeSet ε (tsupport f)
  have hS : S.Finite := latticeSet_finite hε hf.isCompact.isBounded
  unfold MemL2
  apply summable_of_ne_finset_zero (s := hS.toFinset)
  intro q hq
  have hnot : physical ε q ∉ tsupport f := by
    simpa [S, latticeSet] using hq
  have hfq : f (physical ε q) = 0 := by
    by_contra h
    exact hnot (subset_tsupport f h)
  simp [restrict, hfq]

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

/-- Every generator iterate of square-summable data is square summable. -/
theorem memL2_generator_iterate {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {v : Site d → ℝ}
    (hv : MemL2 v) (n : ℕ) : MemL2 ((generator ε a)^[n] v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact memL2_generator hd hε hlam ha ih

/-- The generator is bounded uniformly in the lattice site on bounded functions. -/
theorem abs_generator_le {d : ℕ} (hd : 1 ≤ d) {ε lam M : ℝ}
    (hε : 0 < ε) (hlam : 0 < lam) {a : LongRange.Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {v : LatticeProb.Site d → ℝ}
    (hM : 0 ≤ M) (hv : ∀ q, |v q| ≤ M) (q : LatticeProb.Site d) :
    |LongRange.generator ε a v q| ≤
      (2 * |ε ^ d / LongRange.kappa d ε| * lam⁻¹ *
        ∑' w : LatticeProb.Site d, LongRange.jumpKernel (physical ε w)) * M := by
  let J := fun w : LatticeProb.Site d => LongRange.jumpKernel (physical ε w)
  have ht := (summable_jumpKernel_of_one_le hd hε).mul_left (lam⁻¹ * (2 * M))
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

/-- The generator obeys an ℓ² bound with the total jump rate. -/
theorem tsum_sq_generator_le (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : Site d → ℝ}
    (hf : MemL2 f) :
    (∑' q, generator ε a f q ^ 2) ≤
      (2 * |ε ^ d / kappa d ε| * lam⁻¹ *
        ∑' w : Site d, jumpKernel (physical ε w)) ^ 2 * ∑' q, f q ^ 2 := by
  set S := ∑' w : Site d, jumpKernel (physical ε w)
  have hE := summable_jumpKernel_mul_increment_sq hd hε hf
  have hJs := summable_jumpKernel_of_one_le hd hε
  have hI : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  have hbound : ∀ q, generator ε a f q ^ 2 ≤ (ε ^ d / kappa d ε) ^ 2 *
      (lam⁻¹ ^ 2 * S * ∑' w, jumpKernel (physical ε w) * (f (q + w) - f q) ^ 2) := by
    intro q
    obtain ⟨hs1, hcs⟩ := summable_mul_abs_and_sq_tsum_le (fun w => jumpKernel_nonneg _) hJs
      (hE.prod_factor q)
    have hF : ∀ w : Site d, ‖(if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (f (q + w) - f q) * jumpKernel (physical ε w))‖ ≤
        lam⁻¹ * (jumpKernel (physical ε w) * |f (q + w) - f q|) := by
      intro w
      have hJ := jumpKernel_nonneg (physical ε w)
      split_ifs with hw
      · rw [norm_zero]
        exact mul_nonneg hI (mul_nonneg hJ (abs_nonneg _))
      · have ha0 : 0 ≤ a (edgeAdd q w hw) := hlam.le.trans (ha _).1
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hJ]
        have := mul_le_mul_of_nonneg_right (ha (edgeAdd q w hw)).2
          (mul_nonneg (abs_nonneg (f (q + w) - f q)) hJ)
        linarith
    have habs := tsum_of_norm_bounded (hs1.mul_left lam⁻¹).hasSum hF
    rw [tsum_mul_left, Real.norm_eq_abs] at habs
    have hT : (∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (f (q + w) - f q) * jumpKernel (physical ε w)) ^ 2 ≤
        lam⁻¹ ^ 2 * S * ∑' w, jumpKernel (physical ε w) * (f (q + w) - f q) ^ 2 := by
      rw [← sq_abs]
      calc _ ≤ (lam⁻¹ * ∑' w, jumpKernel (physical ε w) * |f (q + w) - f q|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = lam⁻¹ ^ 2 * (∑' w, jumpKernel (physical ε w) * |f (q + w) - f q|) ^ 2 := by
            ring
        _ ≤ lam⁻¹ ^ 2 * (S * ∑' w, jumpKernel (physical ε w) * (f (q + w) - f q) ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
        _ = _ := by ring
    unfold generator
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hT (sq_nonneg _)
  have hpos : 0 ≤ (ε ^ d / kappa d ε) ^ 2 * (lam⁻¹ ^ 2 * S) := by
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (tsum_nonneg fun w => jumpKernel_nonneg _))
  have hgen := memL2_generator hd hε hlam ha hf
  have hbase := summable_jumpKernel_mul_sq hd hε hf
  have hshift := summable_jumpKernel_mul_sq_add hd hε hf
  have hshift_eq : (∑' p : Site d × Site d,
      jumpKernel (physical ε p.2) * f (p.1 + p.2) ^ 2) =
      ∑' p : Site d × Site d, jumpKernel (physical ε p.2) * f p.1 ^ 2 := by
    exact (shiftPair d).tsum_eq (fun p : Site d × Site d =>
      jumpKernel (physical ε p.2) * f p.1 ^ 2)
  have hcompare : ∀ p : Site d × Site d,
      jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) ^ 2 ≤
      2 * (jumpKernel (physical ε p.2) * f (p.1 + p.2) ^ 2 +
        jumpKernel (physical ε p.2) * f p.1 ^ 2) := by
    intro p
    have hh : (f (p.1 + p.2) - f p.1) ^ 2 ≤
        2 * (f (p.1 + p.2) ^ 2 + f p.1 ^ 2) := by
      nlinarith [sq_nonneg (f (p.1 + p.2) + f p.1)]
    nlinarith [mul_le_mul_of_nonneg_left hh (jumpKernel_nonneg (physical ε p.2))]
  have hsum : (∑' p : Site d × Site d,
      jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) ^ 2) ≤
      4 * S * ∑' q, f q ^ 2 := by
    calc
      _ ≤ ∑' p : Site d × Site d, 2 * (jumpKernel (physical ε p.2) *
          f (p.1 + p.2) ^ 2 + jumpKernel (physical ε p.2) * f p.1 ^ 2) :=
        hE.tsum_le_tsum hcompare ((hshift.add hbase).mul_left 2)
      _ = 2 * ((∑' p : Site d × Site d, jumpKernel (physical ε p.2) *
          f (p.1 + p.2) ^ 2) + ∑' p : Site d × Site d,
          jumpKernel (physical ε p.2) * f p.1 ^ 2) := by
        rw [tsum_mul_left, hshift.tsum_add hbase]
      _ = 4 * S * ∑' q, f q ^ 2 := by
        rw [hshift_eq, hbase.tsum_prod]
        simp only [tsum_mul_right, tsum_mul_left]
        dsimp [S]
        ring
  calc
    _ ≤ ∑' q, (ε ^ d / kappa d ε) ^ 2 *
        (lam⁻¹ ^ 2 * S * ∑' w, jumpKernel (physical ε w) *
          (f (q + w) - f q) ^ 2) :=
      hgen.tsum_le_tsum hbound ((hE.prod.mul_left _).mul_left _)
    _ = ((ε ^ d / kappa d ε) ^ 2 * (lam⁻¹ ^ 2 * S)) *
        ∑' p : Site d × Site d, jumpKernel (physical ε p.2) *
          (f (p.1 + p.2) - f p.1) ^ 2 := by
      simp only [tsum_mul_left]
      rw [hE.tsum_prod]
      ring
    _ ≤ ((ε ^ d / kappa d ε) ^ 2 * (lam⁻¹ ^ 2 * S)) *
        (4 * S * ∑' q, f q ^ 2) := mul_le_mul_of_nonneg_left hsum hpos
    _ = _ := by dsimp [S]; rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring

/-- The generator is bounded on the rescaled lattice `L²` space. -/
theorem latticeNorm_generator_le (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : Site d → ℝ} (hf : MemL2 f) :
    latticeNorm ε (generator ε a f) ≤
      (2 * |ε ^ d / kappa d ε| * lam⁻¹ *
        ∑' w : Site d, jumpKernel (physical ε w)) * latticeNorm ε f := by
  let K := 2 * |ε ^ d / kappa d ε| * lam⁻¹ *
    ∑' w : Site d, jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg fun w => jumpKernel_nonneg _)
  have hsq : latticeNormSq ε (generator ε a f) ≤ K ^ 2 * latticeNormSq ε f := by
    unfold latticeNormSq
    calc
      _ ≤ ε ^ d * (K ^ 2 * ∑' q, f q ^ 2) :=
        mul_le_mul_of_nonneg_left (tsum_sq_generator_le hd hε hlam ha hf) (pow_nonneg hε.le _)
      _ = _ := by ring
  calc
    latticeNorm ε (generator ε a f) ≤ Real.sqrt (K ^ 2 * latticeNormSq ε f) :=
      Real.sqrt_le_sqrt hsq
    _ = K * latticeNorm ε f := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
      rfl

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

private theorem memℓp_of_memL2 {d : ℕ} {f : Site d → ℝ} (hf : MemL2 f) : Memℓp f 2 := by
  apply memℓp_gen
  simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using hf

private theorem memL2_of_memℓp {d : ℕ} {f : Site d → ℝ} (hf : Memℓp f 2) : MemL2 f := by
  have h := hf.summable (by norm_num)
  simpa [MemL2, Real.norm_eq_abs, Real.rpow_two] using h

private theorem lp_norm_sq_eq {d : ℕ} (f : lp (fun _ : Site d => ℝ) 2) :
    ‖f‖ ^ 2 = ∑' q, f q ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
  simpa [Real.norm_eq_abs, Real.rpow_two] using h

private theorem summable_generator_of_bounded {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {v : Site d → ℝ} {M : ℝ} (hM : 0 ≤ M) (hv : ∀ q, |v q| ≤ M) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (v (q + w) - v q) * jumpKernel (physical ε w)) := by
  apply ((summable_jumpKernel_of_one_le hd hε).mul_left (lam⁻¹ * (2 * M))).of_norm_bounded
  intro w
  have hj := jumpKernel_nonneg (physical ε w)
  by_cases hw : w = 0
  · subst w
    simp only [↓reduceDIte, norm_zero]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hlam.le) (by positivity)) hj
  · simp only [hw, ↓reduceDIte, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hlam.le.trans (ha _).1), abs_of_nonneg hj]
    apply mul_le_mul_of_nonneg_right _ hj
    apply mul_le_mul (ha _).2 _ (abs_nonneg _) (inv_nonneg.mpr hlam.le)
    exact (abs_sub _ _).trans (by linarith [hv (q + w), hv q])

private theorem generator_add_of_summable {d : ℕ} (ε : ℝ) (a : Edge d → ℝ) {g h : Site d → ℝ} (q : Site d)
    (hg : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (g (q + w) - g q) * jumpKernel (physical ε w)))
    (hh : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w))) :
    generator ε a (fun x => g x + h x) q = generator ε a g q + generator ε a h q := by
  unfold generator
  rw [← mul_add, ← hg.tsum_add hh]
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte, add_zero]
  · simp only [hw, ↓reduceDIte]
    ring

private theorem generator_const_mul {d : ℕ} (ε : ℝ) (a : Edge d → ℝ) (c : ℝ)
    (h : Site d → ℝ) (q : Site d) :
    generator ε a (fun x => c * h x) q = c * generator ε a h q := by
  unfold generator
  have heq : (∑' w : Site d, if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (c * h (q + w) - c * h q) * jumpKernel (physical ε w)) =
      c * ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hw : w = 0
    · simp only [hw, ↓reduceDIte, mul_zero]
    · simp only [hw, ↓reduceDIte]
      ring
  rw [heq]
  ring

/-- The lattice generator as a bounded operator on `ℓ²`. -/
noncomputable def generatorL2 {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    lp (fun _ : Site d => ℝ) 2 →L[ℝ] lp (fun _ : Site d => ℝ) 2 := by
  let K : ℝ := 2 * |ε ^ d / kappa d ε| * lam⁻¹ *
    ∑' w : Site d, jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg fun w => jumpKernel_nonneg _)
  let L : lp (fun _ : Site d => ℝ) 2 →ₗ[ℝ] lp (fun _ : Site d => ℝ) 2 :=
    { toFun := fun v => ⟨generator ε a v,
        memℓp_of_memL2 (memL2_generator hd hε hlam ha (memL2_of_memℓp (lp.memℓp v)))⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        funext q
        exact generator_add_of_summable ε a q
          (summable_generator_of_bounded hd hε hlam ha (norm_nonneg v) (fun q => by
            simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num) v q) q)
          (summable_generator_of_bounded hd hε hlam ha (norm_nonneg w) (fun q => by
            simpa only [Real.norm_eq_abs] using lp.norm_apply_le_norm (by norm_num) w q) q)
      map_smul' := by
        intro c v
        apply Subtype.ext
        funext q
        exact generator_const_mul ε a c v q }
  apply L.mkContinuous K
  intro v
  have hsq : ‖L v‖ ^ 2 ≤ (K * ‖v‖) ^ 2 := by
    rw [lp_norm_sq_eq, mul_pow, lp_norm_sq_eq]
    exact tsum_sq_generator_le hd hε hlam ha (memL2_of_memℓp (lp.memℓp v))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp hsq

/-- Evaluation of the bounded `ℓ²` generator gives the lattice generator. -/
theorem generatorL2_apply {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (v : lp (fun _ : Site d => ℝ) 2) (q : Site d) :
    generatorL2 hd hε hlam ha v q = generator ε a v q := by
  rfl

/-- The lattice heat series is square summable for compactly supported initial data. -/
theorem memL2_latticeHeat {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : HasCompactSupport f) (t : ℝ) :
    MemL2 (latticeHeat ε a f t) := by
  let K : ℝ := 2 * |ε ^ d / kappa d ε| * lam⁻¹ *
    ∑' w : Site d, jumpKernel (physical ε w)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg fun w => jumpKernel_nonneg _)
  let V (n : ℕ) : lp (fun _ : Site d => ℝ) 2 :=
    ⟨(generator ε a)^[n] (restrict ε f),
      memℓp_of_memL2 (memL2_generator_iterate hd hε hlam ha (memL2_restrict hε hf) n)⟩
  have hV : ∀ n, ‖V n‖ ≤ ‖V 0‖ * K ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs : ‖V (n + 1)‖ ^ 2 ≤ (K * ‖V n‖) ^ 2 := by
        rw [lp_norm_sq_eq, mul_pow, lp_norm_sq_eq]
        simpa [V, K, Function.iterate_succ_apply'] using
          tsum_sq_generator_le hd hε hlam ha
            (memL2_generator_iterate hd hε hlam ha (memL2_restrict hε hf) n)
      have hb : ‖V (n + 1)‖ ≤ K * ‖V n‖ :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp hs
      calc
        _ ≤ K * ‖V n‖ := hb
        _ ≤ K * (‖V 0‖ * K ^ n) := mul_le_mul_of_nonneg_left ih hK
        _ = _ := by rw [pow_succ]; ring
  let H (n : ℕ) : lp (fun _ : Site d => ℝ) 2 := (t ^ n / (n.factorial : ℝ)) • V n
  have hH : Summable H := by
    apply Summable.of_norm_bounded ((Real.summable_pow_div_factorial (|t| * K)).mul_left ‖V 0‖)
    intro n
    change ‖(t ^ n / (n.factorial : ℝ)) • V n‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _)]
    calc
      _ ≤ (|t| ^ n / (n.factorial : ℝ)) * (‖V 0‖ * K ^ n) :=
        mul_le_mul_of_nonneg_left (hV n) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  let v := ∑' n, H n
  have hv : (v : Site d → ℝ) = latticeHeat ε a f t := by
    funext q
    have h := (lp.evalCLM ℝ (fun _ : Site d => ℝ) 2 q).hasSum hH.hasSum
    have hh : HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
        (generator ε a)^[n] (restrict ε f) q) (v q) := by
      change HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ) *
        (generator ε a)^[n] (restrict ε f) q) (v q) at h
      exact h
    exact hh.tsum_eq.symm
  rw [← hv]
  exact memL2_of_memℓp (lp.memℓp v)

/-- The lattice heat series solves the lattice heat equation at every site. -/
theorem hasDerivAt_latticeHeat {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : HasCompactSupport f) (t : ℝ) (q : Site d) :
    HasDerivAt (fun s => latticeHeat ε a f s q)
      (generator ε a (latticeHeat ε a f t) q) t := by
  let V : lp (fun _ : Site d => ℝ) 2 := ⟨restrict ε f, memℓp_of_memL2 (memL2_restrict hε hf)⟩
  let A := generatorL2 hd hε hlam ha
  have hpow : ∀ n : ℕ, ⇑((A ^ n) V) = (generator ε a)^[n] (restrict ε f) := by
    intro n
    induction n with
    | zero => simp [V]
    | succ n ih =>
      funext x
      rw [pow_succ', mul_apply_eq_comp, Function.iterate_succ_apply']
      change generator ε a ((A ^ n) V) x = _
      rw [ih]
  have hscaled (s : ℝ) : ∀ n : ℕ, (s • A) ^ n = s ^ n • A ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ih, pow_succ', pow_succ']
      ext y
      simp only [mul_apply_eq_comp, smul_apply, map_smul, mul_smul]
      simp only [smul_smul, mul_comm]
  have hseries (s : ℝ) (x : Site d) :
      latticeHeat ε a f s x = (NormedSpace.exp (s • A) V) x := by
    have h0 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • A)
    have h1 := (ContinuousLinearMap.apply ℝ (lp (fun _ : Site d => ℝ) 2) V).hasSum h0
    have h2 := (lp.evalCLM ℝ (fun _ : Site d => ℝ) 2 x).hasSum h1
    have h3 : HasSum (fun n : ℕ => s ^ n / (n.factorial : ℝ) *
        (generator ε a)^[n] (restrict ε f) x) ((NormedSpace.exp (s • A) V) x) := by
      convert h2 using 1
      · funext n
        change s ^ n / (n.factorial : ℝ) *
          (generator ε a)^[n] (restrict ε f) x =
          (((n.factorial : ℝ)⁻¹ • ((s • A) ^ n)) V) x
        rw [hscaled]
        simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        rw [hpow]
        ring
      · rfl
    exact h3.tsum_eq
  have hd' := (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t V)
  have hd'' := (lp.evalCLM ℝ (fun _ : Site d => ℝ) 2 q).hasFDerivAt.comp_hasDerivAt t hd'
  convert hd'' using 1
  · funext s
    exact hseries s q
  · simp only [map_zero, add_zero, mul_apply_eq_comp]
    change generator ε a (latticeHeat ε a f t) q =
      (A ((NormedSpace.exp (t • A)) V)) q
    rw [generatorL2_apply]
    congr 1
    funext x
    exact hseries t x

private theorem eq_zero_on_small_interval {ι : Type*} [Nonempty ι] (w g : ℝ → ι → ℝ) {a b K : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hsmall : K * (b - a) < 1)
    (hz : ∀ q, w a q = 0)
    (hb : ∃ M : ℝ, ∀ t ∈ Icc a b, ∀ q, |w t q| ≤ M)
    (hc : ∀ q, ContinuousOn (fun s => w s q) (Icc a b))
    (hd : ∀ t ∈ Ioo a b, ∀ q, HasDerivAt (fun s => w s q) (g t q) t)
    (hG : ∀ M : ℝ, 0 ≤ M → (∀ t ∈ Icc a b, ∀ q, |w t q| ≤ M) →
      ∀ t ∈ Icc a b, ∀ q, |g t q| ≤ K * M) :
    ∀ t ∈ Icc a b, ∀ q, w t q = 0 := by
  let S := (fun p : ℝ × ι => |w p.1 p.2|) '' (Icc a b ×ˢ univ)
  let B := sSup S
  obtain ⟨M, hM⟩ := hb
  have hS : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro _ ⟨⟨t, q⟩, ht, rfl⟩
    exact hM t ht.1 q
  have hne : S.Nonempty := by
    obtain ⟨q⟩ := ‹Nonempty ι›
    exact ⟨|w a q|, ⟨(a, q), ⟨⟨le_rfl, hab⟩, trivial⟩, rfl⟩⟩
  have hB : 0 ≤ B := by
    obtain ⟨q⟩ := ‹Nonempty ι›
    exact (abs_nonneg (w a q)).trans (le_csSup hS ⟨(a, q), ⟨⟨le_rfl, hab⟩, trivial⟩, rfl⟩)
  have hw : ∀ t ∈ Icc a b, ∀ q, |w t q| ≤ B := by
    intro t ht q
    exact le_csSup hS ⟨(t, q), ⟨ht, trivial⟩, rfl⟩
  have hcontract : B ≤ K * B * (b - a) := by
    apply csSup_le hne
    rintro _ ⟨⟨t, q⟩, ht, rfl⟩
    have hle : |w t q| ≤ K * B * (t - a) := by
      by_cases heq : t = a
      · simp [heq, hz q]
      · have hat : a < t := lt_of_le_of_ne ht.1.1 (Ne.symm heq)
        have hcont : ContinuousOn (fun s => w s q) (Icc a t) :=
          (hc q).mono (fun _ hs => ⟨hs.1, hs.2.trans ht.1.2⟩)
        have hdiff : ∀ s ∈ Ioo a t, HasDerivAt (fun r => w r q) (g s q) s :=
          fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.1.2⟩ q
        obtain ⟨c, hc', hder⟩ := exists_hasDerivAt_eq_slope
          (fun s => w s q) (fun s => g s q) hat hcont hdiff
        have hgc := hG B hB hw c ⟨hc'.1.le, hc'.2.le.trans ht.1.2⟩ q
        rw [hder, abs_div, abs_of_pos (sub_pos.mpr hat)] at hgc
        have hm := (div_le_iff₀ (sub_pos.mpr hat)).mp hgc
        simpa only [hz q, sub_zero] using hm
    exact hle.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.1.2 a)
      (mul_nonneg hK hB))
  have hBzero : B = 0 := by
    by_contra h
    have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm h)
    have hlt : K * (b - a) * B < 1 * B := mul_lt_mul_of_pos_right hsmall hBpos
    nlinarith
  intro t ht q
  have := hw t ht q
  rw [hBzero] at this
  have h := abs_le.mp this
  linarith

private theorem eq_zero_of_derivative_bound {ι : Type*} [Nonempty ι] (w g : ℝ → ι → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hz : ∀ q, w 0 q = 0)
    (hb : ∀ T : ℝ, 0 ≤ T → ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ q, |w t q| ≤ M)
    (hc : ∀ q, ContinuousOn (fun s => w s q) (Ici 0))
    (hd : ∀ t ∈ Ioi (0 : ℝ), ∀ q, HasDerivAt (fun s => w s q) (g t q) t)
    (hG : ∀ t ∈ Ici (0 : ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ q, |w t q| ≤ M) → ∀ q, |g t q| ≤ K * M) :
    ∀ t ∈ Ici (0 : ℝ), ∀ q, w t q = 0 := by
  let δ := (K + 1)⁻¹ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : K * δ < 1 := by
    dsimp [δ]
    have hk1 : 0 < K + 1 := by positivity
    have h := inv_mul_cancel₀ (ne_of_gt hk1)
    have hi : 0 < (K + 1)⁻¹ := inv_pos.mpr hk1
    nlinarith
  have hgrid : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n * δ), ∀ q, w t q = 0 := by
    intro n
    induction n with
    | zero =>
      intro t ht q
      have : t = 0 := by simpa using ht
      simpa [this] using hz q
    | succ n ih =>
      intro t ht q
      by_cases ht' : t ≤ (n : ℝ) * δ
      · exact ih t ⟨ht.1, ht'⟩ q
      · let a : ℝ := n * δ
        let b : ℝ := (n + 1) * δ
        have ha : 0 ≤ a := by dsimp [a]; positivity
        have hab : a ≤ b := by dsimp [a, b]; nlinarith
        have hwidth : b - a = δ := by dsimp [a, b]; ring
        have hstart : ∀ q, w a q = 0 := fun q => ih a ⟨ha, le_rfl⟩ q
        have hbd : ∃ M, ∀ s ∈ Icc a b, ∀ q, |w s q| ≤ M := by
          obtain ⟨M, hM⟩ := hb b (ha.trans hab)
          exact ⟨M, fun s hs => hM s ⟨ha.trans hs.1, hs.2⟩⟩
        have hcont : ∀ q, ContinuousOn (fun s => w s q) (Icc a b) :=
          fun q => (hc q).mono (fun _ hs => ha.trans hs.1)
        have hdiff : ∀ s ∈ Ioo a b, ∀ q, HasDerivAt (fun r => w r q) (g s q) s := by
          intro s hs q
          exact hd s (lt_of_le_of_lt ha hs.1) q
        have hbound : ∀ M : ℝ, 0 ≤ M → (∀ s ∈ Icc a b, ∀ q, |w s q| ≤ M) →
            ∀ s ∈ Icc a b, ∀ q, |g s q| ≤ K * M := by
          intro M hM hw s hs q
          exact hG s (ha.trans hs.1) M hM (hw s hs) q
        have htinterval : t ∈ Icc a b := by
          constructor
          · exact le_of_lt (lt_of_not_ge ht')
          · simpa [b, Nat.cast_succ] using ht.2
        exact eq_zero_on_small_interval w g hab hK (hwidth ▸ hsmall) hstart hbd hcont hdiff hbound t htinterval q
  intro t ht q
  obtain ⟨n, hn⟩ := exists_nat_gt (t / δ)
  have htn : t ≤ (n : ℝ) * δ := le_of_lt ((div_lt_iff₀ hδ).mp hn)
  exact hgrid n t ⟨ht, htn⟩ q

private theorem generator_sub_of_summable {d : ℕ} (ε : ℝ) (a : Edge d → ℝ) {g h : Site d → ℝ} (q : Site d)
    (hg : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (g (q + w) - g q) * jumpKernel (physical ε w)))
    (hh : Summable (fun w : Site d => if hw : w = 0 then 0 else
      a (edgeAdd q w hw) * (h (q + w) - h q) * jumpKernel (physical ε w))) :
    generator ε a (fun x => g x - h x) q = generator ε a g q - generator ε a h q := by
  unfold generator
  rw [← mul_sub, ← hg.tsum_sub hh]
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : w = 0
  · simp only [hw, ↓reduceDIte, sub_zero]
  · simp only [hw, ↓reduceDIte]
    ring

/-- Bounded classical solutions with the same initial data agree. -/
theorem eq_of_bounded_lattice_solutions {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (u v : ℝ → Site d → ℝ)
    (h0 : ∀ q, u 0 q = v 0 q)
    (huB : ∀ T : ℝ, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ q, |u t q| ≤ M)
    (hvB : ∀ T : ℝ, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ q, |v t q| ≤ M)
    (huC : ∀ q, ContinuousOn (fun t => u t q) (Ici 0))
    (hvC : ∀ q, ContinuousOn (fun t => v t q) (Ici 0))
    (huD : ∀ t ∈ Ioi (0 : ℝ), ∀ q,
      HasDerivAt (fun s => u s q) (generator ε a (u t) q) t)
    (hvD : ∀ t ∈ Ioi (0 : ℝ), ∀ q,
      HasDerivAt (fun s => v s q) (generator ε a (v t) q) t) :
    ∀ t ∈ Ici (0 : ℝ), ∀ q, u t q = v t q := by
  let w := fun t q => u t q - v t q
  let g := fun t q => generator ε a (u t) q - generator ε a (v t) q
  let K : ℝ := 2 * |ε ^ d / kappa d ε| * lam⁻¹ *
    ∑' z : Site d, jumpKernel (physical ε z)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (inv_nonneg.mpr hlam.le)) (tsum_nonneg fun z => jumpKernel_nonneg _)
  have hw0 : ∀ q, w 0 q = 0 := fun q => sub_eq_zero.mpr (h0 q)
  have hwB : ∀ T : ℝ, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ q, |w t q| ≤ M := by
    intro T hT
    obtain ⟨U, hU⟩ := huB T hT
    obtain ⟨V, hV⟩ := hvB T hT
    refine ⟨U + V, fun t ht q => ?_⟩
    exact (abs_sub _ _).trans (add_le_add (hU t ht q) (hV t ht q))
  have hwC : ∀ q, ContinuousOn (fun t => w t q) (Ici 0) :=
    fun q => (huC q).sub (hvC q)
  have hwD : ∀ t ∈ Ioi (0 : ℝ), ∀ q, HasDerivAt (fun s => w s q) (g t q) t :=
    fun t ht q => (huD t ht q).sub (hvD t ht q)
  have hg : ∀ t ∈ Ici (0 : ℝ), ∀ M : ℝ, 0 ≤ M →
      (∀ q, |w t q| ≤ M) → ∀ q, |g t q| ≤ K * M := by
    intro t ht M hM hw q
    obtain ⟨U, hU⟩ := huB t ht
    obtain ⟨V, hV⟩ := hvB t ht
    have hUt : ∀ q, |u t q| ≤ U := hU t ⟨ht, le_rfl⟩
    have hVt : ∀ q, |v t q| ≤ V := hV t ⟨ht, le_rfl⟩
    have hU0 : 0 ≤ U := (abs_nonneg (u t 0)).trans (hUt 0)
    have hV0 : 0 ≤ V := (abs_nonneg (v t 0)).trans (hVt 0)
    have heq := generator_sub_of_summable ε a q (summable_generator_of_bounded hd hε hlam ha hU0 hUt q)
      (summable_generator_of_bounded hd hε hlam ha hV0 hVt q)
    change |generator ε a (u t) q - generator ε a (v t) q| ≤ K * M
    rw [← heq]
    exact abs_generator_le hd hε hlam ha hM hw q
  have hzero := eq_zero_of_derivative_bound w g hK hw0 hwB hwC hwD hg
  intro t ht q
  exact sub_eq_zero.mp (hzero t ht q)

/-- The lattice heat series is the unique bounded classical solution. -/
theorem latticeHeat_unique {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (u : ℝ → Site d → ℝ) (hu0 : ∀ q, u 0 q = restrict ε f q)
    (huB : ∀ T : ℝ, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ q, |u t q| ≤ M)
    (huC : ∀ q, ContinuousOn (fun t => u t q) (Ici 0))
    (huD : ∀ t ∈ Ioi (0 : ℝ), ∀ q,
      HasDerivAt (fun s => u s q) (generator ε a (u t) q) t) :
    ∀ t ∈ Ici (0 : ℝ), ∀ q, u t q = latticeHeat ε a f t q := by
  apply eq_of_bounded_lattice_solutions hd hε hlam ha u (latticeHeat ε a f)
  · intro q
    rw [latticeHeat_zero]
    exact hu0 q
  · exact huB
  · intro T _
    exact latticeHeat_bounded_on_interval hd hε hlam ha hf hfc T
  · exact huC
  · intro q t ht
    exact (hasDerivAt_latticeHeat hd hε hlam ha hfc t q).continuousAt.continuousWithinAt
  · exact huD
  · intro t ht q
    exact hasDerivAt_latticeHeat hd hε hlam ha hfc t q

end

end LongRangeHeat
