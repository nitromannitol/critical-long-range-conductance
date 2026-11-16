import LongRangeHeat.Defs
import LongRangeHeat.Dirichlet
import LongRange.Appendix.LatticeCount
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Lattice heat series

Bounds on the lattice generator and the exponential series for the heat equation.
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

/-- The generator obeys an ℓ² bound with the total jump rate. -/
theorem tsum_sq_generator_le (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : Site d → ℝ}
    (hf : MemL2 f) :
    (∑' q, generator ε a f q ^ 2) ≤
      (2 * |ε ^ d / kappa d ε| * lam⁻¹ *
        ∑' w : Site d, jumpKernel (physical ε w)) ^ 2 * ∑' q, f q ^ 2 := by
  set S := ∑' w : Site d, jumpKernel (physical ε w)
  have hE := summable_jumpKernel_mul_increment_sq hd hε hf
  have hJs := summable_jumpKernel hd hε
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
  apply ((summable_jumpKernel hd hε).mul_left (lam⁻¹ * (2 * M))).of_norm_bounded
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

end

end LongRangeHeat
