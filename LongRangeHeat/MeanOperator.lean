import LongRangeHeat.Sampling
import LongRangeHeat.SecondMoment

/-!
# Consistency of the mean operator

Lemma 3.1 (`lem:mean`): for `f ∈ C_c^∞(ℝ^d)`, `‖∂_s ū_s - L̄ ū_s‖_{L²(εℤ^d)} ≤ C / κ_ε`, where
`∂_s ū_s` is the right time derivative of `ū` and `L̄ = meanGenerator ε` is (3.1).

Following the paper, the sum (3.1) is split into the short jumps `0 < |z| ≤ 1` and the long jumps
`|z| > 1`. On the short jumps `ū_s(· + z) - ū_s` is expanded to second order: the linear terms
cancel (`sum_first_moment_eq_zero`) and, by (2.3), the quadratic terms give `(2d)⁻¹ Δ ū_s = ∂_s ū_s`
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

/-- The quadratic terms of the short jumps: by (2.3),
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

end

end LongRangeHeat
