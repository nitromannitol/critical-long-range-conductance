import LongRangeHeat.Sampling
import LongRangeHeat.SecondMoment

/-!
# Consistency of the mean operator

Lemma 3.1 (`lem:mean`): for `f ∈ C_c^∞(ℝ^d)`, `‖∂_s ū_s - L̄ ū_s‖_{L²(εℤ^d)} ≤ C / κ_ε`, where
`∂_s ū_s` is the right time derivative of `ū` and `L̄ = meanGenerator ε` is (3.1).

Following the paper, the sum (3.1) is split into the short jumps `0 < |z| ≤ 1` and the long jumps
`|z| > 1`. On the short jumps `ū_s(· + z) - ū_s` is expanded to second order: the linear terms
cancel (`sum_first_moment_eq_zero`) and, by (2.1), the quadratic terms give `(2d)⁻¹ Δ ū_s = ∂_s ū_s`
(`quadratic_moment`). This leaves the identity `meanGenerator_eq` for `∂_s ū_s - L̄ ū_s` as a
series over the jumps of the Taylor remainders (short jumps) and the increments (long jumps). Their
norms are bounded by (2.7) and (2.6), and the series is bounded in `L²(εℤ^d)` by the sum of the
norms (`sum_sq_tsum_le`, from the Cauchy–Schwarz inequality `sq_tsum_mul_le`). The resulting sums
`ε^d ∑ |z|^{1-d}` and `ε^d ∑ |z|^{-d-2}` are bounded by `exists_short_sum_le` and
`exists_long_sum_le`.
-/

namespace LongRangeHeat

open MeasureTheory Filter Topology Set LongRange LatticeProb LatticeProb.Heat
  LatticeProb.WhiteNoise LatticeProb.Euclidean.Lattice
open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-! ### The Cauchy–Schwarz inequality for series -/

/-- `(∑ cᵢ gᵢ)² ≤ (∑ cᵢ) (∑ cᵢ gᵢ²)` for nonnegative weights `cᵢ`. -/
theorem sq_tsum_mul_le {ι : Type*} {c g : ι → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc : Summable c)
    (hcg : Summable fun i => c i * g i) (hcg2 : Summable fun i => c i * g i ^ 2) :
    (∑' i, c i * g i) ^ 2 ≤ (∑' i, c i) * ∑' i, c i * g i ^ 2 := by
  set A := ∑' i, c i with hAdef
  set B := ∑' i, c i * g i with hBdef
  set D := ∑' i, c i * g i ^ 2 with hDdef
  have hA : 0 ≤ A := tsum_nonneg hc0
  rcases hA.eq_or_lt with hA0 | hApos
  · have hci : ∀ i, c i = 0 := fun i =>
      le_antisymm (by rw [hA0]; exact hc.le_tsum i fun j _ => hc0 j) (hc0 i)
    have hB : B = 0 := by simp [hBdef, hci]
    rw [hB, ← hA0]
    simp
  · have heq : (fun i => c i * (A * g i - B) ^ 2) = fun i =>
        A ^ 2 * (c i * g i ^ 2) - 2 * A * B * (c i * g i) + B ^ 2 * c i := by
      funext i
      ring
    have hexp : ∑' i, c i * (A * g i - B) ^ 2 = A ^ 2 * D - 2 * A * B * B + B ^ 2 * A := by
      rw [heq, Summable.tsum_add ((hcg2.mul_left _).sub (hcg.mul_left _)) (hc.mul_left _),
        Summable.tsum_sub (hcg2.mul_left _) (hcg.mul_left _), tsum_mul_left, tsum_mul_left,
        tsum_mul_left]
    have hnn : 0 ≤ ∑' i, c i * (A * g i - B) ^ 2 :=
      tsum_nonneg fun i => mul_nonneg (hc0 i) (sq_nonneg _)
    have h1 : 0 ≤ A * (A * D - B ^ 2) := by nlinarith [hnn, hexp]
    have := (mul_nonneg_iff_of_pos_left hApos).1 h1
    nlinarith

/-- A series `∑ᵢ cᵢ Gᵢ` of lattice functions with `‖Gᵢ‖_{L²(εℤ^d)} ≤ 1` has norm at most
`∑ᵢ cᵢ`. -/
theorem sum_sq_tsum_le {ι : Type*} {ε : ℝ} (hε : 0 < ε) {c : ι → ℝ} (hc0 : ∀ i, 0 ≤ c i)
    (hc : Summable c) {G : ι → Site d → ℝ}
    (hG : ∀ i (T : Finset (Site d)), ε ^ d * ∑ q ∈ T, G i q ^ 2 ≤ 1) (T : Finset (Site d)) :
    ε ^ d * ∑ q ∈ T, (∑' i, c i * G i q) ^ 2 ≤ (∑' i, c i) ^ 2 := by
  have hεd : 0 < ε ^ d := pow_pos hε d
  have hpt : ∀ i q, G i q ^ 2 ≤ 1 / ε ^ d := fun i q => by
    have := hG i {q}
    rw [Finset.sum_singleton] at this
    rw [le_div_iff₀ hεd]
    linarith [mul_comm (ε ^ d) (G i q ^ 2)]
  have hs2 : ∀ q, Summable fun i => c i * G i q ^ 2 := fun q =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hc0 i) (sq_nonneg _))
      (fun i => mul_le_mul_of_nonneg_left (hpt i q) (hc0 i)) (hc.mul_right (1 / ε ^ d))
  have hs1 : ∀ q, Summable fun i => c i * G i q := fun q =>
    Summable.of_norm_bounded (g := fun i => c i * (1 + 1 / ε ^ d)) (hc.mul_right _) fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc0 i)]
      refine mul_le_mul_of_nonneg_left ?_ (hc0 i)
      nlinarith [hpt i q, abs_nonneg (G i q), sq_abs (G i q)]
  have hle : ∀ i, c i * (ε ^ d * ∑ q ∈ T, G i q ^ 2) ≤ c i := fun i =>
    mul_le_of_le_one_right (hc0 i) (hG i T)
  have hs3 : Summable fun i => c i * (ε ^ d * ∑ q ∈ T, G i q ^ 2) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hc0 i)
      (mul_nonneg hεd.le (Finset.sum_nonneg fun q _ => sq_nonneg _))) hle hc
  calc ε ^ d * ∑ q ∈ T, (∑' i, c i * G i q) ^ 2
      ≤ ε ^ d * ∑ q ∈ T, (∑' i, c i) * ∑' i, c i * G i q ^ 2 := by
        gcongr with q hq
        exact sq_tsum_mul_le hc0 hc (hs1 q) (hs2 q)
    _ = (∑' i, c i) * ∑' i, c i * (ε ^ d * ∑ q ∈ T, G i q ^ 2) := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun q _ => hs2 q]
        have : ∑' i, c i * (ε ^ d * ∑ q ∈ T, G i q ^ 2) =
            ε ^ d * ∑' i, ∑ q ∈ T, c i * G i q ^ 2 := by
          rw [← tsum_mul_left]
          congr 1
          funext i
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          ring
        rw [this]
        ring
    _ ≤ (∑' i, c i) * ∑' i, c i :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hle hs3 hc) (tsum_nonneg hc0)
    _ = (∑' i, c i) ^ 2 := by ring

/-- A lattice function with norm at most `a`, divided by `a`, has norm at most one. -/
theorem sum_sq_neg_div_le_one {v : Site d → ℝ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hv : MemL2 v) (hb : latticeNorm ε v ≤ a) (T : Finset (Site d)) :
    ε ^ d * ∑ q ∈ T, (-(v q / a)) ^ 2 ≤ 1 := by
  have hεd : 0 < ε ^ d := pow_pos hε d
  have h1 : ∑ q ∈ T, v q ^ 2 ≤ ∑' q, v q ^ 2 :=
    Summable.sum_le_tsum T (fun q _ => sq_nonneg _) hv
  have hnn : 0 ≤ latticeNormSq ε v := mul_nonneg hεd.le (tsum_nonneg fun q => sq_nonneg _)
  have h2 : ε ^ d * ∑' q, v q ^ 2 ≤ a ^ 2 := by
    have : latticeNormSq ε v = latticeNorm ε v ^ 2 := (Real.sq_sqrt hnn).symm
    calc ε ^ d * ∑' q, v q ^ 2 = latticeNorm ε v ^ 2 := this
      _ ≤ a ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  simp_rw [neg_sq, div_pow, ← Finset.sum_div]
  rw [mul_div_assoc', div_le_one (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hεd.le]

/-! ### The jump sums -/

theorem physical_zero (ε : ℝ) : physical ε (0 : Site d) = 0 := by
  funext k
  simp [physical]

/-- `L̄ v(x) = (ε^d / κ_ε) ∑_z J(z) (v(x + z) - v(x))` for the restriction of `u`. -/
theorem meanGenerator_restrict (ε : ℝ) (u : (Fin d → ℝ) → ℝ) (q : Site d) :
    meanGenerator ε (restrict ε u) q = ε ^ d / kappa d ε * ∑' w : Site d,
      jumpKernel (physical ε w) * (u (physical ε q + physical ε w) - u (physical ε q)) := by
  unfold meanGenerator generator restrict
  congr 1
  refine tsum_congr fun w => ?_
  split_ifs with hw
  · simp [hw, physical_zero, jumpKernel_zero]
  · rw [physical_add]
    beta_reduce
    ring

/-- Off the short jumps, the kernel is the long-jump term `|z|^{-d-2} 1_{|z| > 1}`. -/
theorem jumpKernel_eq_of_notMem {ε : ℝ} (hε : 0 < ε) {w : Site d}
    (hw : w ∉ unitBallIndices d ε) :
    jumpKernel (physical ε w) =
      if 1 < radius (physical ε w) then 1 / radius (physical ε w) ^ (d + 2) else 0 := by
  rw [mem_unitBallIndices hε, not_and_or, not_not, not_le] at hw
  have hr0 : radius (0 : Fin d → ℝ) = 0 := by simp [radius]
  rcases hw with rfl | hw
  · rw [physical_zero, jumpKernel_zero, hr0]
    norm_num
  · have hw0 : physical ε w ≠ 0 := by
      intro h
      rw [h, hr0] at hw
      linarith
    rw [jumpKernel_of_ne_zero hw0]
    simp only [hw, ↓reduceIte, one_div]

theorem summable_jumpKernel {ε : ℝ} (hε : 0 < ε)
    (hlong : Summable fun w : Site d =>
      if 1 < radius (physical ε w) then 1 / radius (physical ε w) ^ (d + 2) else 0) :
    Summable fun w : Site d => jumpKernel (physical ε w) := by
  classical
  have hsplit : (fun w : Site d => jumpKernel (physical ε w)) = fun w =>
      (if w ∈ unitBallIndices d ε then jumpKernel (physical ε w) else 0) +
        if w ∈ unitBallIndices d ε then 0 else
          (if 1 < radius (physical ε w) then 1 / radius (physical ε w) ^ (d + 2) else 0) := by
    funext w
    split_ifs with h1 <;> simp_all [jumpKernel_eq_of_notMem hε]
  rw [hsplit]
  refine (summable_of_ne_finset_zero (s := unitBallIndices d ε) fun w hw => ?_).add
    (Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_) hlong)
  · simp [hw]
  · split_ifs <;> first | exact le_rfl | positivity
  · split_ifs <;> first | exact le_rfl | positivity

/-- A bilinear map on `ℝ^d` in coordinates. -/
theorem bilin_apply_eq_sum (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (z : Fin d → ℝ) :
    B z z = ∑ i, ∑ j, z i * z j * B (Pi.single i 1) (Pi.single j 1) := by
  have hz : z = ∑ i, z i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic terms of the short jumps: by (2.1),
`(ε^d / κ_ε) ∑_{0<|z|≤1} J(z) ½ B(z, z) = (2d)⁻¹ ∑_i B(e_i, e_i)`. -/
theorem quadratic_moment (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) :
    ε ^ d / kappa d ε * ∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * (1 / 2 * B (physical ε q) (physical ε q)) =
      (∑ i, B (Pi.single i 1) (Pi.single i 1)) / (2 * d) := by
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hrw : ∀ q : Site d, jumpKernel (physical ε q) * (1 / 2 * B (physical ε q) (physical ε q)) =
      1 / 2 * ∑ i, ∑ j, B (Pi.single i 1) (Pi.single j 1) *
        (jumpKernel (physical ε q) * physical ε q i * physical ε q j) := by
    intro q
    rw [bilin_apply_eq_sum B]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hrw]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := unitBallIndices d ε), ← Finset.mul_sum]
  have h2 : ∀ i j : Fin d, ε ^ d / kappa d ε * (B (Pi.single i 1) (Pi.single j 1) *
      ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i * physical ε q j) =
      B (Pi.single i 1) (Pi.single j 1) * if i = j then 1 / (d : ℝ) else 0 := by
    intro i j
    rw [← second_moment_normalized hd hε i j]
    ring
  calc ε ^ d / kappa d ε * (1 / 2 * ∑ i, ∑ j, B (Pi.single i 1) (Pi.single j 1) *
        ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i * physical ε q j)
      = 1 / 2 * ∑ i, ∑ j, ε ^ d / kappa d ε * (B (Pi.single i 1) (Pi.single j 1) *
        ∑ q ∈ unitBallIndices d ε,
          jumpKernel (physical ε q) * physical ε q i * physical ε q j) := by
        rw [← mul_assoc, mul_comm (ε ^ d / kappa d ε) (1 / 2), mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = (∑ i, B (Pi.single i 1) (Pi.single i 1)) / (2 * d) := by
        simp_rw [h2, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
          Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp

/-- The operator `(2d)⁻¹ Δ` through the second derivative on the basis vectors. -/
theorem contOp_eq_sum_fderiv_fderiv {u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (x : Fin d → ℝ) :
    contOp d u x = (∑ i, fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1)) / (2 * d) := by
  rw [contOp, lap_eq_sum_coordDeriv hu]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_fderiv_apply_eq (hu.of_le (by simp)) x _ _

theorem jumpKernel_nonneg (v : Fin d → ℝ) : 0 ≤ jumpKernel v := by
  unfold jumpKernel
  split_ifs
  · exact le_rfl
  · have := radius_nonneg v
    positivity

/-- The error of the jump `z = εw` at `x = εq` in the expansion of `L̄ u(x)`: the second-order
Taylor remainder of `u` for a short jump `0 < |z| ≤ 1`, the increment for a long jump. -/
def jumpError (ε : ℝ) (u : (Fin d → ℝ) → ℝ) (w q : Site d) : ℝ :=
  if w ∈ unitBallIndices d ε then
    u (physical ε q + physical ε w) - u (physical ε q) -
      fderiv ℝ u (physical ε q) (physical ε w) -
      1 / 2 * fderiv ℝ (fderiv ℝ u) (physical ε q) (physical ε w) (physical ε w)
  else u (physical ε q + physical ε w) - u (physical ε q)

/-- The expansion of the mean operator: `L̄ u(x) = (2d)⁻¹ Δ u(x) + (ε^d / κ_ε) ∑_z J(z) E_z(x)`
with the jump errors `E_z = jumpError`. -/
theorem meanGenerator_eq (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    {u : (Fin d → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) {M : ℝ} (hM : ∀ x, |u x| ≤ M)
    (hJ : Summable fun w : Site d => jumpKernel (physical ε w)) (q : Site d) :
    meanGenerator ε (restrict ε u) q = contOp d u (physical ε q) +
      ε ^ d / kappa d ε * ∑' w : Site d, jumpKernel (physical ε w) * jumpError ε u w q := by
  classical
  set x := physical ε q with hx
  set S := unitBallIndices d ε with hS
  set I : Site d → ℝ := fun w => u (x + physical ε w) - u x with hI
  set P : Site d → ℝ := fun w => fderiv ℝ u x (physical ε w) +
    1 / 2 * fderiv ℝ (fderiv ℝ u) x (physical ε w) (physical ε w) with hP
  have hsplit : ∀ w, jumpKernel (physical ε w) * I w = jumpKernel (physical ε w) *
      jumpError ε u w q + (if w ∈ S then jumpKernel (physical ε w) * P w else 0) := by
    intro w
    simp only [jumpError, hI, hP, ← hx, ← hS]
    split_ifs <;> ring
  have hIs : Summable fun w => jumpKernel (physical ε w) * I w :=
    Summable.of_norm_bounded (g := fun w => jumpKernel (physical ε w) * (2 * M)) (hJ.mul_right _)
      fun w => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (jumpKernel_nonneg _)
        calc |I w| ≤ |u (x + physical ε w)| + |u x| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hM (x + physical ε w), hM x]
  have hfin : Summable fun w => if w ∈ S then jumpKernel (physical ε w) * P w else 0 :=
    summable_of_ne_finset_zero (s := S) fun w hw => by simp [hw]
  have hEs : Summable fun w => jumpKernel (physical ε w) * jumpError ε u w q :=
    (hIs.sub hfin).congr fun w => by rw [hsplit w]; ring
  have hmg : meanGenerator ε (restrict ε u) q =
      ε ^ d / kappa d ε * ∑' w : Site d, jumpKernel (physical ε w) * I w :=
    meanGenerator_restrict ε u q
  have hfin_eq : (∑' w, if w ∈ S then jumpKernel (physical ε w) * P w else 0) =
      ∑ w ∈ S, jumpKernel (physical ε w) * P w := by
    rw [tsum_eq_sum (s := S) fun w hw => by simp [hw]]
    exact Finset.sum_congr rfl fun w hw => by simp [hw]
  rw [hmg, tsum_congr hsplit, Summable.tsum_add hEs hfin, hfin_eq]
  have hP1 : ∑ w ∈ S, jumpKernel (physical ε w) * P w =
      ∑ w ∈ S, jumpKernel (physical ε w) * fderiv ℝ u x (physical ε w) +
        ∑ w ∈ S, jumpKernel (physical ε w) *
          (1 / 2 * fderiv ℝ (fderiv ℝ u) x (physical ε w) (physical ε w)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [hP]; ring
  rw [hP1, sum_first_moment_eq_zero hε.1, zero_add]
  have hQ := quadratic_moment hd hε (fderiv ℝ (fderiv ℝ u) x)
  rw [← contOp_eq_sum_fderiv_fderiv hu] at hQ
  linear_combination hQ

/-- The right time derivative of the continuum solution is `(2d)⁻¹ Δ ū_s`. -/
theorem derivWithin_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {s : ℝ} (hs : 0 ≤ s) (x : Fin d → ℝ) :
    derivWithin (fun r => continuumHeat f r x) (Ici s) s = contOp d (continuumHeat f s) x :=
  (hasDerivWithinAt_continuumHeat hd hf hfc hs x).derivWithin (uniqueDiffWithinAt_Ici s)

/-- The heat flow does not increase the supremum norm. -/
theorem abs_continuumHeat_le (hd : 1 ≤ d) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) {s : ℝ} (hs : 0 ≤ s) (x : Fin d → ℝ) : |continuumHeat g s x| ≤ M := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [continuumHeat_zero]
    exact hM x
  have hc : Continuous fun w => g (x - w) := hg.comp (continuous_const.sub continuous_id)
  rw [continuumHeat_eq_integral g hs]
  calc |∫ w, heatKernel d s w * g (x - w)| ≤ ∫ w, |heatKernel d s w * g (x - w)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, heatKernel d s w * M :=
        integral_mono (integrable_heatKernel_mul_bdd hd hs hc fun w => hM _).abs
          ((integrable_heatKernel hd hs).mul_const M) fun w => by
            rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hd _ _)]
            exact mul_le_mul_of_nonneg_left (hM _) (heatKernel_nonneg hd _ _)
    _ = M := by rw [integral_mul_const, integral_heatKernel hd hs, one_mul]

/-- **Lemma 3.1** (`lem:mean`): `‖∂_s ū_s - L̄ ū_s‖_{L²(εℤ^d)} ≤ C / κ_ε`. -/
theorem mean_operator_consistency (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s →
      MemL2 (fun q : Site d => derivWithin (fun r => continuumHeat f r (physical ε q)) (Ici s) s -
        meanGenerator ε (restrict ε (continuumHeat f s)) q) ∧
      latticeNorm ε (fun q : Site d =>
        derivWithin (fun r => continuumHeat f r (physical ε q)) (Ici s) s -
          meanGenerator ε (restrict ε (continuumHeat f s)) q) ≤ C / kappa d ε := by
  classical
  obtain ⟨CT, hCT⟩ := taylor_bound hd hf hfc
  obtain ⟨CI, hCI⟩ := increment_bound hd hf hfc
  obtain ⟨C1, hC1⟩ := exists_short_sum_le hd
  obtain ⟨C2, hC2⟩ := exists_long_sum_le d
  obtain ⟨M0, hM0⟩ := hfc.exists_bound_of_continuous hf.continuous
  have hM0' : ∀ x, |f x| ≤ M0 := fun x => by simpa [Real.norm_eq_abs] using hM0 x
  set AT := max CT 1 with hAT
  set AI := max CI 1 with hAI
  have hAT0 : 0 < AT := lt_max_of_lt_right one_pos
  have hAI0 : 0 < AI := lt_max_of_lt_right one_pos
  refine ⟨AT * C1 + AI * C2, fun ε hε s hs => ?_⟩
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, by linarith [hε.2]⟩
  have hκ := kappa_pos hd hε1
  have hεd : 0 < ε ^ d := pow_pos hε.1 d
  have hu : ContDiff ℝ ∞ (continuumHeat f s) := contDiff_continuumHeat hd hf hfc hs
  have huM : ∀ x, |continuumHeat f s x| ≤ M0 := abs_continuumHeat_le hd hf.continuous hM0' hs
  obtain ⟨hlong, hlong_le⟩ := hC2 ε hε
  have hJ := summable_jumpKernel hε.1 hlong
  set S := unitBallIndices d ε with hS
  have hr : ∀ w ∈ S, 0 < radius (physical ε w) := fun w hw =>
    radius_pos (unitBallIndices_physical_ne_zero hε.1 hw)
  set D : Site d → ℝ := fun w => if w ∈ S then AT * radius (physical ε w) ^ 3 else AI with hD
  have hD0 : ∀ w, 0 < D w := fun w => by
    simp only [hD]
    split_ifs with hw
    · exact mul_pos hAT0 (pow_pos (hr w hw) 3)
    · exact hAI0
  set c : Site d → ℝ := fun w => ε ^ d / kappa d ε * (jumpKernel (physical ε w) * D w) with hc
  set G : Site d → Site d → ℝ := fun w q => -(jumpError ε (continuumHeat f s) w q / D w)
    with hG
  have hc0 : ∀ w, 0 ≤ c w := fun w =>
    mul_nonneg (div_nonneg hεd.le hκ.le) (mul_nonneg (jumpKernel_nonneg _) (hD0 w).le)
  -- the identity `∂_s ū_s - L̄ ū_s = ∑_z c_z G_z`
  have hE : ∀ q : Site d, derivWithin (fun r => continuumHeat f r (physical ε q)) (Ici s) s -
      meanGenerator ε (restrict ε (continuumHeat f s)) q = ∑' w, c w * G w q := by
    intro q
    rw [derivWithin_continuumHeat hd hf hfc hs, meanGenerator_eq hd hε1 hu huM hJ q]
    have hcg : ∀ w, c w * G w q = -(ε ^ d / kappa d ε) *
        (jumpKernel (physical ε w) * jumpError ε (continuumHeat f s) w q) := fun w => by
      simp only [hc, hG]
      field_simp [(hD0 w).ne']
    rw [tsum_congr hcg, tsum_mul_left]
    ring
  -- each `G_z` has norm at most one
  have hGn : ∀ w (T : Finset (Site d)), ε ^ d * ∑ q ∈ T, G w q ^ 2 ≤ 1 := by
    intro w T
    by_cases hw : w ∈ S
    · obtain ⟨hm, hn⟩ := hCT ε hε s hs (physical ε w)
      have hfun : (fun q => jumpError ε (continuumHeat f s) w q) = fun q : Site d =>
          continuumHeat f s (physical ε q + physical ε w) - continuumHeat f s (physical ε q) -
            fderiv ℝ (continuumHeat f s) (physical ε q) (physical ε w) -
            1 / 2 * fderiv ℝ (fderiv ℝ (continuumHeat f s)) (physical ε q) (physical ε w)
              (physical ε w) := funext fun q => by simp [jumpError, ← hS, hw]
      have hDw : D w = AT * radius (physical ε w) ^ 3 := by simp [hD, hw]
      have hm' : MemL2 (fun q => jumpError ε (continuumHeat f s) w q) := by rw [hfun]; exact hm
      have hn' : latticeNorm ε (fun q => jumpError ε (continuumHeat f s) w q) ≤ D w := by
        rw [hfun, hDw]
        exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (radius_nonneg _) 3))
      exact sum_sq_neg_div_le_one hε.1 (hD0 w) hm' hn' T
    · obtain ⟨hm, hn⟩ := hCI ε hε s hs (physical ε w)
      have hfun : (fun q => jumpError ε (continuumHeat f s) w q) = fun q : Site d =>
          continuumHeat f s (physical ε q + physical ε w) - continuumHeat f s (physical ε q) :=
        funext fun q => by simp [jumpError, ← hS, hw]
      have hDw : D w = AI := by simp [hD, hw]
      have hm' : MemL2 (fun q => jumpError ε (continuumHeat f s) w q) := by rw [hfun]; exact hm
      have hn' : latticeNorm ε (fun q => jumpError ε (continuumHeat f s) w q) ≤ D w := by
        rw [hfun, hDw]
        refine hn.trans ?_
        have h1 : 0 ≤ min (radius (physical ε w)) 1 := le_min (radius_nonneg _) zero_le_one
        have h2 : min (radius (physical ε w)) 1 ≤ 1 := min_le_right _ _
        rcases le_total CI 0 with hci | hci
        · nlinarith [le_max_right CI 1]
        · nlinarith [le_max_left CI 1]
      exact sum_sq_neg_div_le_one hε.1 (hD0 w) hm' hn' T
  -- the weights: `∑_z c_z ≤ C / κ_ε`
  have hcsplit : ∀ w, jumpKernel (physical ε w) * D w =
      (if w ∈ S then AT * (1 / radius (physical ε w) ^ (d - 1)) else 0) +
        AI * (if 1 < radius (physical ε w) then 1 / radius (physical ε w) ^ (d + 2) else 0) := by
    intro w
    by_cases hw : w ∈ S
    · have hrw := hr w hw
      have hle : ¬ 1 < radius (physical ε w) := not_lt.2 ((mem_unitBallIndices hε.1 w).1 hw).2
      rw [jumpKernel_of_ne_zero (unitBallIndices_physical_ne_zero hε.1 hw)]
      simp only [hD, hw, hle, ↓reduceIte, mul_zero, add_zero]
      have hpow : radius (physical ε w) ^ (d + 2) =
          radius (physical ε w) ^ (d - 1) * radius (physical ε w) ^ 3 := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
    · simp only [hD, hw, ↓reduceIte, zero_add, jumpKernel_eq_of_notMem hε.1 hw]
      ring
  have hfin : Summable fun w : Site d =>
      if w ∈ S then AT * (1 / radius (physical ε w) ^ (d - 1)) else 0 :=
    summable_of_ne_finset_zero (s := S) fun w hw => by simp [hw]
  have hJD : Summable fun w => jumpKernel (physical ε w) * D w := by
    rw [funext hcsplit]
    exact hfin.add (hlong.mul_left AI)
  have hcs : Summable c := hJD.mul_left _
  have hsum_c : ∑' w, c w ≤ (AT * C1 + AI * C2) / kappa d ε := by
    have h1 : ∑' w, c w = (AT * (ε ^ d * ∑ w ∈ S, 1 / radius (physical ε w) ^ (d - 1)) +
        AI * (ε ^ d * ∑' w : Site d, if 1 < radius (physical ε w) then
          1 / radius (physical ε w) ^ (d + 2) else 0)) / kappa d ε := by
      have e1 : ∑' w, c w = ε ^ d / kappa d ε * ∑' w, jumpKernel (physical ε w) * D w := by
        simp only [hc]
        exact tsum_mul_left
      have e2 : ∑' w, jumpKernel (physical ε w) * D w =
          AT * ∑ w ∈ S, 1 / radius (physical ε w) ^ (d - 1) +
            AI * ∑' w : Site d, if 1 < radius (physical ε w) then
              1 / radius (physical ε w) ^ (d + 2) else 0 := by
        rw [tsum_congr hcsplit, Summable.tsum_add hfin (hlong.mul_left AI), tsum_mul_left]
        congr 1
        rw [tsum_eq_sum (s := S) fun w hw => by simp [hw], Finset.mul_sum]
        exact Finset.sum_congr rfl fun w hw => by simp [hw]
      rw [e1, e2]
      ring
    rw [h1]
    gcongr
    · exact hC1 ε hε
  have hbound := memL2_and_latticeNorm_le hε.1 (tsum_nonneg hc0)
    (v := fun q => ∑' w, c w * G w q) fun T => sum_sq_tsum_le hε.1 hc0 hcs hGn T
  rw [show (fun q : Site d => derivWithin (fun r => continuumHeat f r (physical ε q)) (Ici s) s -
      meanGenerator ε (restrict ε (continuumHeat f s)) q) = fun q => ∑' w, c w * G w q
    from funext hE]
  exact ⟨hbound.1, hbound.2.trans hsum_c⟩

end

end LongRangeHeat
