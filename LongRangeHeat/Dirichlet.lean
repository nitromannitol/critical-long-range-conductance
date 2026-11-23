import LongRangeHeat.Defs
import LatticeProb.Euclidean.Summability

/-!
# The Dirichlet form on `L²(εℤ^d)`

This file proves the two properties of the Dirichlet form `B_a` of (2.2) stated in Lemma 2.1
(`lem:Dirichlet`) of the heat-kernel version, for conductances with values in `[λ, λ⁻¹]`.

* Integration by parts: for square-summable `v₁, v₂`, the function `L^ε v₁` is square summable,
  the double series defining `B_a(v₁, v₂)` converges absolutely, and
  `⟨L^ε v₁, v₂⟩ = -B_a(v₁, v₂)`. The change of variables `(x, z) ↦ (x + z, -z)` shows that the
  double series of `⟨L^ε v₁, v₂⟩` is unchanged when `v₂(x)` is replaced by `-v₂(x + z)`.
* Coercivity: keeping only the jumps `z = ε e_i` gives `B_a(v, v) ≥ (λ / 2κ_ε) ‖D v‖²`.

The absolute convergence comes from the summability of the kernel `J(εw)` over `w ≠ 0` and the
weighted Cauchy–Schwarz inequality `(∑ J |x|)² ≤ (∑ J) (∑ J x²)`.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (generator kappa jumpKernel bilinForm Edge edgeAdd jumpKernel_zero
  jumpKernel_of_ne_zero)

noncomputable section

variable {d : ℕ}

/-! ### The jump kernel -/

/-- The jump kernel is nonnegative. -/
theorem jumpKernel_nonneg (z : Fin d → ℝ) : 0 ≤ jumpKernel z := by
  unfold jumpKernel
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)

/-- The jump kernel is even. -/
theorem jumpKernel_neg (z : Fin d → ℝ) : jumpKernel (-z) = jumpKernel z := by
  simp only [jumpKernel, neg_eq_zero, radius, Pi.neg_apply, neg_sq]

/-- Physical scaling commutes with reversing an increment. -/
theorem physical_neg (ε : ℝ) (w : Site d) : physical ε (-w) = -physical ε w := by
  ext i
  simp only [physical, Pi.neg_apply, Int.cast_neg, mul_neg]

/-- The normalization `κ_ε` is nonnegative. -/
theorem kappa_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ kappa d ε :=
  mul_nonneg (pow_nonneg hε _)
    (Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))

/-- The scaled jump kernel `w ↦ J(εw)` is summable over the integer sites. -/
theorem summable_jumpKernel_of_one_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable fun w : Site d => jumpKernel (physical ε w) := by
  have herr := (LatticeProb.Euclidean.Summability.euclidean_radial_error_summable d
    hd).mul_left (ε ^ (d + 2))⁻¹
  refine herr.of_nonneg_of_le (fun w => jumpKernel_nonneg _) (fun w => ?_)
  by_cases hw : w = 0
  · subst hw
    rw [(physical_eq_zero_iff hε 0).mpr rfl, jumpKernel_zero]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (zpow_nonneg (radius_nonneg _) _)
  · have hr := lattice_radius_ge_one hw
    rw [jumpKernel_of_ne_zero (fun h => hw ((physical_eq_zero_iff hε w).mp h)),
      radius_physical_eq_mul hε.le, mul_pow, mul_inv, zpow_neg, zpow_natCast]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos (by linarith) _)
      (pow_le_pow_right₀ hr (by omega))) (inv_nonneg.mpr (pow_nonneg hε.le _))

/-- The unit vector `e_i` of the integer lattice is nonzero. -/
theorem single_ne_zero (i : Fin d) : (Pi.single i 1 : Site d) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

/-- At a nearest-neighbor jump `ε e_i` the kernel is `ε^{-(d+2)}`. -/
theorem jumpKernel_physical_single {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    jumpKernel (physical ε (Pi.single i 1 : Site d)) = (ε ^ (d + 2))⁻¹ := by
  rw [jumpKernel_of_ne_zero (fun h => single_ne_zero i ((physical_eq_zero_iff hε _).mp h))]
  have hsum : ∑ k, physical ε (Pi.single i 1 : Site d) k ^ 2 = ε ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp [physical]
    · intro k _ hk
      simp [physical, hk]
    · simp
  rw [radius, hsum, Real.sqrt_sq hε.le]

/-! ### Weighted Cauchy–Schwarz and square-summable functions -/

/-- The weighted Cauchy–Schwarz inequality `(∑ J |x|)² ≤ (∑ J) (∑ J x²)` for series. -/
theorem summable_mul_abs_and_sq_tsum_le {ι : Type*} {J x : ι → ℝ} (hJ : ∀ i, 0 ≤ J i)
    (hJs : Summable J) (hx : Summable fun i => J i * x i ^ 2) :
    Summable (fun i => J i * |x i|) ∧
      (∑' i, J i * |x i|) ^ 2 ≤ (∑' i, J i) * ∑' i, J i * x i ^ 2 := by
  have hf2 : ∀ i, (Real.sqrt (J i) * |x i|) ^ (2 : ℝ) = J i * x i ^ 2 := by
    intro i
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hJ i), sq_abs]
  have hg2 : ∀ i, Real.sqrt (J i) ^ (2 : ℝ) = J i := by
    intro i
    rw [Real.rpow_two, Real.sq_sqrt (hJ i)]
  have hfg : ∀ i, Real.sqrt (J i) * |x i| * Real.sqrt (J i) = J i * |x i| := by
    intro i
    rw [mul_right_comm, Real.mul_self_sqrt (hJ i)]
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (f := fun i => Real.sqrt (J i) * |x i|)
    (g := fun i => Real.sqrt (J i)) (fun i => by positivity) (fun i => Real.sqrt_nonneg _)
    (by simpa only [hf2] using hx) (by simpa only [hg2] using hJs)
  simp only [hf2, hg2, hfg] at hs hle
  refine ⟨hs, ?_⟩
  have hT : 0 ≤ ∑' i, J i * x i ^ 2 := tsum_nonneg fun i => mul_nonneg (hJ i) (sq_nonneg _)
  have hS : 0 ≤ ∑' i, J i := tsum_nonneg hJ
  have h0 : 0 ≤ ∑' i, J i * |x i| := tsum_nonneg fun i => mul_nonneg (hJ i) (abs_nonneg _)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hle
  calc (∑' i, J i * |x i|) ^ 2
      ≤ (Real.sqrt (∑' i, J i * x i ^ 2) * Real.sqrt (∑' i, J i)) ^ 2 :=
        pow_le_pow_left₀ h0 hle 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hT, Real.sq_sqrt hS, mul_comm]

/-- The product of two square-summable functions is summable. -/
theorem summable_mul_of_memL2 {f g : Site d → ℝ} (hf : MemL2 f) (hg : MemL2 g) :
    Summable fun q => f q * g q := by
  refine (hf.add hg).of_norm_bounded (fun q => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f q| - |g q|), sq_abs (f q), sq_abs (g q), abs_nonneg (f q),
    abs_nonneg (g q)]

/-- The increments `x ↦ v(x + εu) - v(x)` of a square-summable function are square summable. -/
theorem summable_sq_sub_shift {v : Site d → ℝ} (hv : MemL2 v) (u : Site d) :
    Summable fun q => (v (q + u) - v q) ^ 2 := by
  have hsh : Summable fun q => v (q + u) ^ 2 :=
    (Equiv.summable_iff (f := fun q => v q ^ 2) (Equiv.addRight u)).mpr hv
  refine ((hsh.add hv).mul_left 2).of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
  nlinarith [sq_nonneg (v (q + u) + v q)]

/-- The discrete derivatives of a square-summable function are square summable. -/
theorem memL2_discreteDeriv {v : Site d → ℝ} (hv : MemL2 v) (ε : ℝ) (i : Fin d) :
    MemL2 (discreteDeriv ε i v) := by
  have h := (summable_sq_sub_shift hv (Pi.single i 1)).div_const (ε ^ 2)
  refine h.congr (fun q => ?_)
  rw [discreteDeriv, div_pow]

/-! ### Absolute convergence over pairs of sites -/

/-- The shift `(q, w) ↦ (q + w, w)` of pairs of sites. -/
def shiftPair (d : ℕ) : Site d × Site d ≃ Site d × Site d where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv _ := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv _ := Prod.ext (sub_add_cancel _ _) rfl

/-- The reversal `(q, w) ↦ (q + w, -w)` of a directed increment. -/
def edgeReverse (d : ℕ) : Site d × Site d ≃ Site d × Site d where
  toFun p := (p.1 + p.2, -p.2)
  invFun p := (p.1 + p.2, -p.2)
  left_inv _ := Prod.ext (add_neg_cancel_right _ _) (neg_neg _)
  right_inv _ := Prod.ext (add_neg_cancel_right _ _) (neg_neg _)

/-- Reversing a directed increment does not change the unordered edge. -/
theorem edgeAdd_reverse (q w : Site d) (hw : w ≠ 0) :
    edgeAdd (q + w) (-w) (neg_ne_zero.mpr hw) = edgeAdd q w hw := by
  apply Subtype.ext
  change s(q + w, q + w + -w) = s(q, q + w)
  rw [add_neg_cancel_right]
  exact Sym2.eq_swap

/-- The series `∑_{q, w} J(εw) f(q)²` converges for square-summable `f`. -/
theorem summable_jumpKernel_mul_sq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {f : Site d → ℝ}
    (hf : MemL2 f) :
    Summable fun p : Site d × Site d => jumpKernel (physical ε p.2) * f p.1 ^ 2 :=
  (hf.mul_of_nonneg (summable_jumpKernel_of_one_le hd hε) (fun q => sq_nonneg (f q))
    (fun _ => jumpKernel_nonneg _)).congr fun _ => mul_comm _ _

/-- The series `∑_{q, w} J(εw) f(q + w)²` converges for square-summable `f`. -/
theorem summable_jumpKernel_mul_sq_add (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {f : Site d → ℝ}
    (hf : MemL2 f) :
    Summable fun p : Site d × Site d => jumpKernel (physical ε p.2) * f (p.1 + p.2) ^ 2 :=
  (Equiv.summable_iff (f := fun p : Site d × Site d => jumpKernel (physical ε p.2) * f p.1 ^ 2)
    (shiftPair d)).mpr (summable_jumpKernel_mul_sq hd hε hf)

/-- The increment energy `∑_{q, w} J(εw) (f(q + w) - f(q))²` of a square-summable function
converges. -/
theorem summable_jumpKernel_mul_increment_sq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {f : Site d → ℝ} (hf : MemL2 f) :
    Summable fun p : Site d × Site d =>
      jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) ^ 2 := by
  refine (((summable_jumpKernel_mul_sq_add hd hε hf).add
    (summable_jumpKernel_mul_sq hd hε hf)).mul_left 2).of_nonneg_of_le
    (fun p => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)) (fun p => ?_)
  have hJ := jumpKernel_nonneg (physical ε p.2)
  have h : (f (p.1 + p.2) - f p.1) ^ 2 ≤ 2 * (f (p.1 + p.2) ^ 2 + f p.1 ^ 2) := by
    nlinarith [sq_nonneg (f (p.1 + p.2) + f p.1)]
  linarith [mul_le_mul_of_nonneg_left h hJ]

/-! ### Integration by parts -/

/-- The directed summand `a_{q,w} J(εw) (f(q + w) - f(q)) η(q)` of `⟨L^ε f, η⟩`. -/
def generatorPair (ε : ℝ) (a : Edge d → ℝ) (f η : Site d → ℝ) (p : Site d × Site d) : ℝ :=
  if hw : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hw) *
    jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) * η p.1

/-- The summand of `B_a(f, η)` is the sum of the two oppositely oriented summands of
`-⟨L^ε f, η⟩`. -/
theorem bilinForm_summand_eq (ε : ℝ) (a : Edge d → ℝ) (f η : Site d → ℝ)
    (p : Site d × Site d) :
    (if hw : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hw) *
      jumpKernel (physical ε p.2) * (f (p.1 + p.2) - f p.1) *
        (η (p.1 + p.2) - η p.1)) =
      -generatorPair ε a f η (edgeReverse d p) - generatorPair ε a f η p := by
  rcases p with ⟨q, w⟩
  by_cases hw : w = 0
  · simp only [hw, edgeReverse, generatorPair, Equiv.coe_fn_mk, neg_zero, ↓reduceDIte,
      sub_zero]
  · simp only [hw, edgeReverse, generatorPair, Equiv.coe_fn_mk, neg_eq_zero,
      ↓reduceDIte, add_neg_cancel_right, physical_neg, jumpKernel_neg]
    rw [edgeAdd_reverse q w hw]
    ring

/-- For square-summable `f, η` the directed double series of `⟨L^ε f, η⟩` converges
absolutely. -/
theorem summable_generatorPair (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hf : MemL2 f) (hη : MemL2 η) : Summable (generatorPair ε a f η) := by
  refine (((summable_jumpKernel_mul_increment_sq hd hε hf).add
    (summable_jumpKernel_mul_sq hd hε hη)).mul_left lam⁻¹).of_norm_bounded (fun p => ?_)
  have hJ := jumpKernel_nonneg (physical ε p.2)
  have hI : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  unfold generatorPair
  split_ifs with hw
  · rw [norm_zero]
    exact mul_nonneg hI (add_nonneg (mul_nonneg hJ (sq_nonneg _)) (mul_nonneg hJ (sq_nonneg _)))
  · have ha0 : 0 ≤ a (edgeAdd p.1 p.2 hw) := hlam.le.trans (ha _).1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hJ]
    set D := f (p.1 + p.2) - f p.1
    set e := η p.1
    have h1 : |D| * |e| ≤ D ^ 2 + e ^ 2 := by
      nlinarith [sq_nonneg (|D| - |e|), sq_abs D, sq_abs e, abs_nonneg D, abs_nonneg e]
    have h2 := mul_le_mul (mul_le_mul_of_nonneg_right (ha (edgeAdd p.1 p.2 hw)).2 hJ) h1
      (mul_nonneg (abs_nonneg D) (abs_nonneg e)) (mul_nonneg hI hJ)
    linarith

/-- The double series of `B_a(f, η)` converges absolutely for square-summable `f, η`. -/
theorem summable_bilinForm_summand (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f η : Site d → ℝ}
    (hf : MemL2 f) (hη : MemL2 η) :
    Summable fun p : Site d × Site d => if hw : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        (f (p.1 + p.2) - f p.1) * (η (p.1 + p.2) - η p.1) := by
  have hs := summable_generatorPair hd hε hlam ha hf hη
  have hr : Summable fun p => generatorPair ε a f η (edgeReverse d p) :=
    (Equiv.summable_iff (f := generatorPair ε a f η) (edgeReverse d)).mpr hs
  exact (hr.neg.sub hs).congr fun p => (bilinForm_summand_eq ε a f η p).symm

/-- Integration by parts `⟨L^ε f, η⟩ = -B_a(f, η)` whenever the directed double series of
`⟨L^ε f, η⟩` converges absolutely. -/
theorem latticeInner_generator_eq_neg_bilinForm {ε : ℝ} {a : Edge d → ℝ} {f η : Site d → ℝ}
    (hs : Summable (generatorPair ε a f η)) :
    latticeInner ε (generator ε a f) η = -bilinForm ε a f η := by
  have hr : Summable fun p => generatorPair ε a f η (edgeReverse d p) :=
    (Equiv.summable_iff (f := generatorPair ε a f η) (edgeReverse d)).mpr hs
  have hsum : (∑' p, generatorPair ε a f η (edgeReverse d p)) =
      ∑' p, generatorPair ε a f η p := (edgeReverse d).tsum_eq _
  have hpair : (∑' p, generatorPair ε a f η p) =
      ∑' q, (∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (f (q + w) - f q) * jumpKernel (physical ε w)) * η q := by
    rw [hs.tsum_prod]
    refine tsum_congr fun q => ?_
    rw [← tsum_mul_right]
    refine tsum_congr fun w => ?_
    unfold generatorPair
    by_cases hw : w = 0 <;> simp only [hw, ↓reduceDIte] <;> ring
  have hgen : (∑' q, generator ε a f q * η q) =
      ε ^ d / kappa d ε * ∑' p, generatorPair ε a f η p := by
    rw [hpair, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    unfold generator
    ring
  unfold latticeInner bilinForm
  simp_rw [bilinForm_summand_eq]
  rw [Summable.tsum_sub hr.neg hs, tsum_neg, hsum, hgen]
  have he : ε ^ (2 * d) = ε ^ d * ε ^ d := by rw [two_mul, pow_add]
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The operator `L^ε` maps square-summable functions to square-summable functions. -/
theorem memL2_generator (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {f : Site d → ℝ} (hf : MemL2 f) :
    MemL2 (generator ε a f) := by
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
  exact ((hE.prod.mul_left (lam⁻¹ ^ 2 * S)).mul_left ((ε ^ d / kappa d ε) ^ 2)).of_nonneg_of_le
    (fun q => sq_nonneg _) hbound

/-! ### Coercivity -/

/-- Keeping only the nearest-neighbor jumps: `B_a(v, v) ≥ (λ / 2κ_ε) ‖D v‖²`. -/
theorem bilinForm_self_ge (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {v : Site d → ℝ} (hv : MemL2 v) :
    lam / 2 / kappa d ε * gradNormSq ε v ≤ bilinForm ε a v v := by
  set b : Site d × Site d → ℝ := fun p => if hw : p.2 = 0 then 0 else
      a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        (v (p.1 + p.2) - v p.1) * (v (p.1 + p.2) - v p.1) with hb
  have hbs : Summable b := summable_bilinForm_summand hd hε hlam ha hv hv
  have hb0 : ∀ p, 0 ≤ b p := by
    intro p
    simp only [hb]
    split_ifs with hw
    · exact le_rfl
    · rw [mul_assoc]
      exact mul_nonneg (mul_nonneg (hlam.le.trans (ha _).1) (jumpKernel_nonneg _))
        (mul_self_nonneg _)
  set g : Fin d × Site d → Site d × Site d := fun p => (p.2, Pi.single p.1 1)
  have hg : Function.Injective g := by
    rintro ⟨i, q⟩ ⟨j, r⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨hqr, hij⟩ := h
    have hij' : i = j := by
      by_contra hne
      have := congrFun hij i
      simp [hne] at this
    rw [hqr, hij']
  have hle := tsum_comp_le_tsum_of_inj hbs hb0 hg
  have hsc : Summable (b ∘ g) := hbs.comp_injective hg
  have hsplit : ∑' p, (b ∘ g) p = ∑ i, ∑' q, b (q, Pi.single i 1) := by
    rw [hsc.tsum_prod, tsum_fintype]
    rfl
  set Q : Fin d → ℝ := fun i => ∑' q, (v (q + Pi.single i 1) - v q) ^ 2 with hQ
  have hlow : ∀ i q, lam * (ε ^ (d + 2))⁻¹ * (v (q + Pi.single i 1) - v q) ^ 2 ≤
      b (q, Pi.single i 1) := by
    intro i q
    simp only [hb, single_ne_zero i, ↓reduceDIte, jumpKernel_physical_single hε]
    have h1 := (ha (edgeAdd q (Pi.single i 1) (single_ne_zero i))).1
    have hc : 0 ≤ (ε ^ (d + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hε.le _)
    nlinarith [mul_nonneg (sub_nonneg.mpr h1)
      (mul_nonneg hc (sq_nonneg (v (q + Pi.single i 1) - v q)))]
  have key : ∑ i, lam * (ε ^ (d + 2))⁻¹ * Q i ≤ ∑' p, b p := by
    refine le_trans ?_ (hsplit ▸ hle)
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hQ, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (hlow i) ((summable_sq_sub_shift hv _).mul_left _)
      (hsc.prod_factor i)
  have hgrad : gradNormSq ε v = ∑ i, ε ^ d * (Q i / ε ^ 2) := by
    unfold gradNormSq latticeNormSq discreteDeriv
    simp_rw [div_pow, tsum_div_const]
    rfl
  have hterm : ∀ i, lam / 2 / kappa d ε * (ε ^ d * (Q i / ε ^ 2)) =
      ε ^ (2 * d) / (2 * kappa d ε) * (lam * (ε ^ (d + 2))⁻¹ * Q i) := by
    intro i
    have hp : ε ^ (2 * d) * (ε ^ (d + 2))⁻¹ = ε ^ d / ε ^ 2 := by
      rw [two_mul, pow_add, pow_add, mul_inv]
      field_simp
    calc _ = lam / 2 / kappa d ε * (ε ^ d / ε ^ 2) * Q i := by ring
      _ = lam / 2 / kappa d ε * (ε ^ (2 * d) * (ε ^ (d + 2))⁻¹) * Q i := by rw [hp]
      _ = _ := by ring
  rw [hgrad, Finset.mul_sum, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left key
    (div_nonneg (pow_nonneg hε.le _) (mul_nonneg zero_le_two (kappa_nonneg hε.le)))

end

end LongRangeHeat
