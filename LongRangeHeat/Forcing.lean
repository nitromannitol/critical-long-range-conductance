import LongRangeHeat.Dirichlet
import LongRangeHeat.CanonicalPath
import LatticeProb.Euclidean.Estimates

/-!
# The random term and the vector field `G`

This file proves Proposition 3.2 (`prop:forcing`) of the heat-kernel version for a general
square-summable function `g` on `εℤ^d` in place of the sampled solution `ū_s`.

The two integrations by parts of Lemma 2.1, for `L^ε` and for the mean operator `L̄`, give
(3.4): `⟨(L̄ - L^ε) g, v⟩ = (ε^{2d} / 2κ_ε) ∑_{x, z} (a_{x,z} - 1) J(z) (g(x+z) - g(x))
(v(x+z) - v(x))`. On the short jumps `0 < |z| ≤ 1` the telescoping identity (3.2) along the
canonical paths and an exchange of the order of summation turn this sum into
`κ_ε⁻¹ ⟨G, D v⟩`, where `G = forcingField ε a g` is the vector field (3.3). On the long jumps
the Cauchy–Schwarz inequality and an increment bound `‖g(· + w) - g‖ ≤ K min(|εw|, 1)` give a
contribution at most `C K κ_ε⁻¹ ‖v‖`, with `C` depending only on `d` and `λ`.
-/

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (generator kappa jumpKernel bilinForm Edge edgeAdd jumpKernel_of_ne_zero)

noncomputable section

variable {d : ℕ}

/-! ### Square-summable functions -/

/-- Square-summable functions form a vector space: sums. -/
theorem memL2_add {f g : Site d → ℝ} (hf : MemL2 f) (hg : MemL2 g) :
    MemL2 fun q => f q + g q :=
  ((Summable.add hf hg).mul_left 2).of_nonneg_of_le (fun q => sq_nonneg _) fun q => by
    nlinarith [sq_nonneg (f q - g q)]

/-- Square-summable functions form a vector space: differences. -/
theorem memL2_sub {f g : Site d → ℝ} (hf : MemL2 f) (hg : MemL2 g) :
    MemL2 fun q => f q - g q :=
  ((Summable.add hf hg).mul_left 2).of_nonneg_of_le (fun q => sq_nonneg _) fun q => by
    nlinarith [sq_nonneg (f q + g q)]

/-- Square-summable functions form a vector space: scalar multiples. -/
theorem memL2_const_mul {f : Site d → ℝ} (hf : MemL2 f) (c : ℝ) : MemL2 fun q => c * f q :=
  (Summable.mul_left (c ^ 2) hf).congr fun q => by ring

/-- Translates of square-summable functions are square summable. -/
theorem memL2_comp_add_right {f : Site d → ℝ} (hf : MemL2 f) (u : Site d) :
    MemL2 fun q => f (q + u) :=
  (Equiv.summable_iff (f := fun q => f q ^ 2) (Equiv.addRight u)).mpr hf

/-- Finite sums of square-summable functions are square summable. -/
theorem memL2_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Site d → ℝ}
    (hf : ∀ i ∈ s, MemL2 (f i)) : MemL2 fun q => ∑ i ∈ s, f i q :=
  ((summable_sum (f := fun i q => f i q ^ 2) hf).mul_left (s.card : ℝ)).of_nonneg_of_le
    (fun _ => sq_nonneg _) fun _ => sq_sum_le_card_mul_sum_sq

/-- A bounded function times a square-summable function is square summable. -/
theorem memL2_mul_of_abs_le {b f : Site d → ℝ} {M : ℝ} (hb : ∀ q, |b q| ≤ M) (hf : MemL2 f) :
    MemL2 fun q => b q * f q :=
  (Summable.mul_left (M ^ 2) hf).of_nonneg_of_le (fun q => sq_nonneg _) fun q => by
    rw [mul_pow]
    have h : b q ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb q) 2
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- The Cauchy–Schwarz inequality `∑ |f g| ≤ (∑ f²)^{1/2} (∑ g²)^{1/2}`. -/
theorem tsum_abs_mul_le {f g : Site d → ℝ} (hf : MemL2 f) (hg : MemL2 g) :
    ∑' q, |f q| * |g q| ≤ Real.sqrt (∑' q, f q ^ 2) * Real.sqrt (∑' q, g q ^ 2) := by
  have h2 : ∀ (h : Site d → ℝ) q, |h q| ^ (2 : ℝ) = h q ^ 2 := fun h q => by
    rw [Real.rpow_two, sq_abs]
  have := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun q => |f q|) (g := fun q => |g q|) (fun q => abs_nonneg _) (fun q => abs_nonneg _)
    (by simp only [h2]; exact hf) (by simp only [h2]; exact hg)
  simp only [h2] at this
  rwa [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at this

/-- The rescaled Cauchy–Schwarz inequality `ε^d ∑ |f g| ≤ ‖f‖ ‖g‖`. -/
theorem pow_mul_tsum_abs_mul_le {ε : ℝ} (hε : 0 ≤ ε) {f g : Site d → ℝ} (hf : MemL2 f)
    (hg : MemL2 g) : ε ^ d * ∑' q, |f q| * |g q| ≤ latticeNorm ε f * latticeNorm ε g := by
  have he : 0 ≤ ε ^ d := pow_nonneg hε d
  rw [latticeNorm, latticeNorm, latticeNormSq, latticeNormSq, Real.sqrt_mul he, Real.sqrt_mul he]
  set s := Real.sqrt (ε ^ d) with hs
  have hss : s * s = ε ^ d := Real.mul_self_sqrt he
  rw [← hss]
  calc s * s * ∑' q, |f q| * |g q|
      ≤ s * s * (Real.sqrt (∑' q, f q ^ 2) * Real.sqrt (∑' q, g q ^ 2)) :=
        mul_le_mul_of_nonneg_left (tsum_abs_mul_le hf hg) (mul_self_nonneg s)
    _ = _ := by ring

/-- The increments of a square-summable function: `‖v(· + w) - v‖ ≤ 2 ‖v‖`. -/
theorem latticeNorm_sub_shift_le {ε : ℝ} (hε : 0 ≤ ε) {v : Site d → ℝ} (hv : MemL2 v)
    (w : Site d) : latticeNorm ε (fun q => v (q + w) - v q) ≤ 2 * latticeNorm ε v := by
  have hsh := memL2_comp_add_right hv w
  have hshift : ∑' q, v (q + w) ^ 2 = ∑' q, v q ^ 2 :=
    (Equiv.addRight w).tsum_eq (fun q => v q ^ 2)
  have hle : latticeNormSq ε (fun q => v (q + w) - v q) ≤ 4 * latticeNormSq ε v := by
    unfold latticeNormSq
    have h1 : ∑' q, (v (q + w) - v q) ^ 2 ≤ ∑' q, 2 * (v (q + w) ^ 2 + v q ^ 2) :=
      Summable.tsum_le_tsum (fun q => by nlinarith [sq_nonneg (v (q + w) + v q)])
        (memL2_sub hsh hv) ((Summable.add hsh hv).mul_left 2)
    rw [tsum_mul_left, Summable.tsum_add hsh hv, hshift] at h1
    nlinarith [pow_nonneg hε d]
  rw [latticeNorm, latticeNorm, show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two],
    ← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt hle

/-! ### The vector field `G` -/

/-- The radius of a nearest-neighbor jump `ε e_i` is `ε`. -/
theorem radius_physical_single {ε : ℝ} (hε : 0 ≤ ε) (i : Fin d) :
    radius (physical ε (Pi.single i 1 : Site d)) = ε := by
  have hsum : ∑ k, physical ε (Pi.single i 1 : Site d) k ^ 2 = ε ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp [physical]
    · intro k _ hk
      simp [physical, hk]
    · simp
  rw [radius, hsum, Real.sqrt_sq hε]

/-- For `ε ∈ (0, 1]` the normalization `κ_ε` is positive. -/
theorem kappa_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 < kappa d ε := by
  have hi : (Pi.single ⟨0, hd⟩ 1 : Site d) ∈ unitBallIndices d ε :=
    (mem_unitBallIndices hε _).mpr ⟨single_ne_zero _, by
      rw [radius_physical_single hε.le]; exact hε1⟩
  refine mul_pos (pow_pos hε d) (Finset.sum_pos' (fun _ _ =>
    inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)) ⟨_, hi, inv_pos.mpr (pow_pos ?_ _)⟩)
  rw [radius_physical_single hε.le]
  exact hε

/-- For conductances in `[λ, λ⁻¹]` with `λ ≤ 1`, `|a - 1| ≤ λ⁻¹`. -/
theorem abs_sub_one_le {lam b : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1)
    (hb : lam ≤ b ∧ b ≤ lam⁻¹) : |b - 1| ≤ lam⁻¹ := by
  have h1 : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam.1).mpr hlam.2
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2, hlam.1]

/-- The centered conductance times the increment, `(a_{x,w} - 1)(g(x + w) - g(x))`, set to `0`
for `w = 0`. -/
def centeredIncrement (a : Edge d → ℝ) (g : Site d → ℝ) (x w : Site d) : ℝ :=
  if hw : w = 0 then 0 else (a (edgeAdd x w hw) - 1) * (g (x + w) - g x)

/-- For a square-summable `g`, the centered increments in a fixed direction are square
summable. -/
theorem memL2_centeredIncrement {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {g : Site d → ℝ} (hg : MemL2 g) (w : Site d) :
    MemL2 fun x => centeredIncrement a g x w := by
  by_cases hw : w = 0
  · subst hw
    refine (summable_zero (α := ℝ)).congr fun x => ?_
    simp [centeredIncrement]
  · simp only [centeredIncrement, hw, ↓reduceDIte]
    exact memL2_mul_of_abs_le (fun x => abs_sub_one_le hlam (ha _))
      (memL2_sub (memL2_comp_add_right hg w) hg)

/-- The vector field `G` of (3.3) for a function `g` on `εℤ^d` in place of `ū_s`:
`G_i(y) = (ε^{d+1} / 2) ∑_{0 < |z| ≤ 1} J(z) sgn(z_i) ∑_{x : (y,i) ∈ γ_{x,z}}
(a_{x,z} - 1)(g(x + z) - g(x))`. -/
def forcingField (ε : ℝ) (a : Edge d → ℝ) (g : Site d → ℝ) (i : Fin d) (y : Site d) : ℝ :=
  ε ^ (d + 1) / 2 * ∑ w ∈ unitBallIndices d ε,
    jumpKernel (physical ε w) * (Int.sign (w i) : ℝ) *
      ∑ x ∈ crossingSet w y i, centeredIncrement a g x w

/-- The field `G` written with the parameters of the crossed edges. -/
theorem forcingField_eq (ε : ℝ) (a : Edge d → ℝ) (g : Site d → ℝ) (i : Fin d) (y : Site d) :
    forcingField ε a g i y = ε ^ (d + 1) / 2 * ∑ w ∈ unitBallIndices d ε,
      jumpKernel (physical ε w) * (Int.sign (w i) : ℝ) *
        ∑ t ∈ pathRange w i, centeredIncrement a g (y - pathPoint w i t) w := by
  simp only [forcingField, sum_crossingSet]

/-- Each component of `G` is square summable. -/
theorem memL2_forcingField {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {g : Site d → ℝ} (hg : MemL2 g) (ε : ℝ) (i : Fin d) :
    MemL2 (forcingField ε a g i) := by
  rw [show forcingField ε a g i = _ from funext (forcingField_eq ε a g i)]
  refine memL2_const_mul (memL2_finsetSum _ fun w _ =>
    memL2_const_mul (memL2_finsetSum _ fun t _ => ?_) _) _
  have := memL2_comp_add_right (memL2_centeredIncrement hlam ha hg w) (-pathPoint w i t)
  simpa only [sub_eq_add_neg] using this

/-! ### The identity (3.4) -/

/-- The summand of (3.4). -/
def forcingSummand (ε : ℝ) (a : Edge d → ℝ) (g v : Site d → ℝ) (p : Site d × Site d) : ℝ :=
  if hw : p.2 = 0 then 0 else (a (edgeAdd p.1 p.2 hw) - 1) * jumpKernel (physical ε p.2) *
    (g (p.1 + p.2) - g p.1) * (v (p.1 + p.2) - v p.1)

/-- The identity (3.4): two integrations by parts write `⟨(L̄ - L^ε) g, v⟩` as an absolutely
convergent double series. -/
theorem forcing_sum (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : lam ∈ Set.Ioc (0 : ℝ) 1)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {g v : Site d → ℝ} (hg : MemL2 g)
    (hv : MemL2 v) :
    MemL2 (fun q => meanGenerator ε g q - generator ε a g q) ∧
      Summable (forcingSummand ε a g v) ∧
      latticeInner ε (fun q => meanGenerator ε g q - generator ε a g q) v =
        ε ^ (2 * d) / (2 * kappa d ε) * ∑' p, forcingSummand ε a g v p := by
  have h1 : ∀ e : Edge d, lam ≤ (fun _ => (1 : ℝ)) e ∧ (fun _ => (1 : ℝ)) e ≤ lam⁻¹ :=
    fun _ => ⟨hlam.2, (one_le_inv₀ hlam.1).mpr hlam.2⟩
  have hm := memL2_generator hd hε hlam.1 h1 hg
  have hl := memL2_generator hd hε hlam.1 ha hg
  have hsm := summable_bilinForm_summand hd hε hlam.1 h1 hg hv
  have hsl := summable_bilinForm_summand hd hε hlam.1 ha hg hv
  have hdiff : ∀ p : Site d × Site d, forcingSummand ε a g v p =
      (if hw : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
        (g (p.1 + p.2) - g p.1) * (v (p.1 + p.2) - v p.1)) -
      (if hw : p.2 = 0 then 0 else (fun _ => (1 : ℝ)) (edgeAdd p.1 p.2 hw) *
        jumpKernel (physical ε p.2) * (g (p.1 + p.2) - g p.1) * (v (p.1 + p.2) - v p.1)) := by
    intro p
    unfold forcingSummand
    split_ifs <;> ring
  refine ⟨memL2_sub hm hl, (hsl.sub hsm).congr fun p => (hdiff p).symm, ?_⟩
  have ibp_m := latticeInner_generator_eq_neg_bilinForm
    (summable_generatorPair hd hε hlam.1 h1 hg hv)
  have ibp_l := latticeInner_generator_eq_neg_bilinForm
    (summable_generatorPair hd hε hlam.1 ha hg hv)
  have hsub : latticeInner ε (fun q => meanGenerator ε g q - generator ε a g q) v =
      latticeInner ε (generator ε (fun _ => 1) g) v - latticeInner ε (generator ε a g) v := by
    unfold latticeInner meanGenerator
    simp_rw [sub_mul]
    rw [Summable.tsum_sub (summable_mul_of_memL2 hm hv) (summable_mul_of_memL2 hl hv), mul_sub]
  rw [hsub, ibp_m, ibp_l]
  unfold bilinForm
  rw [tsum_congr hdiff, Summable.tsum_sub hsl hsm]
  ring

/-! ### The short jumps -/

/-- On the short jumps, the series (3.4) is `κ_ε⁻¹ ⟨G, D v⟩`. -/
theorem forcing_short (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε) (hlam : lam ∈ Set.Ioc (0 : ℝ) 1)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {g v : Site d → ℝ} (hg : MemL2 g)
    (hv : MemL2 v) :
    ε ^ (2 * d) / (2 * kappa d ε) * ∑' p : Site d × Site d,
        (if p.2 ∈ unitBallIndices d ε then forcingSummand ε a g v p else 0) =
      (kappa d ε)⁻¹ * ∑ i, latticeInner ε (forcingField ε a g i) (discreteDeriv ε i v) := by
  set S := unitBallIndices d ε with hSdef
  set H : Site d → Site d → ℝ := fun w x => jumpKernel (physical ε w) * centeredIncrement a g x w
    with hH
  set T : Site d → Fin d → ℤ → ℝ :=
    fun w i t => ∑' y, H w (y - pathPoint w i t) * discreteDeriv ε i v y with hT
  have hHm : ∀ w, MemL2 (H w) := fun w =>
    memL2_const_mul (memL2_centeredIncrement hlam ha hg w) _
  have hDv : ∀ i, MemL2 (discreteDeriv ε i v) := fun i => memL2_discreteDeriv hv ε i
  have hsumT : ∀ w i t, Summable fun y => H w (y - pathPoint w i t) * discreteDeriv ε i v y :=
    fun w i t => summable_mul_of_memL2 (by
      simpa only [sub_eq_add_neg] using memL2_comp_add_right (hHm w) (-pathPoint w i t)) (hDv i)
  have hsF : Summable (forcingSummand ε a g v) := (forcing_sum hd hε hlam ha hg hv).2.1
  have hS1 : ∑' p : Site d × Site d, (if p.2 ∈ S then forcingSummand ε a g v p else 0) =
      ∑ w ∈ S, ∑' x, forcingSummand ε a g v (x, w) := by
    have hsumm : Summable fun p : Site d × Site d =>
        if p.2 ∈ S then forcingSummand ε a g v p else 0 :=
      (hsF.indicator {p | p.2 ∈ S}).congr fun p => by simp [Set.indicator_apply]
    have hsc : Summable fun c : Site d × Site d =>
        if (Equiv.prodComm (Site d) (Site d) c).2 ∈ S then
          forcingSummand ε a g v (Equiv.prodComm (Site d) (Site d) c) else 0 :=
      (Equiv.summable_iff (f := fun p : Site d × Site d =>
        if p.2 ∈ S then forcingSummand ε a g v p else 0) (Equiv.prodComm _ _)).mpr hsumm
    rw [← (Equiv.prodComm (Site d) (Site d)).tsum_eq, hsc.tsum_prod]
    rw [tsum_eq_sum (s := S) fun w hw => by simp [hw]]
    refine Finset.sum_congr rfl fun w hw => tsum_congr fun x => ?_
    simp [hw]
  have hS2 : ∀ w ∈ S, ∑' x, forcingSummand ε a g v (x, w) =
      ε * ∑ i, ∑ t ∈ pathRange w i, (Int.sign (w i) : ℝ) * T w i t := by
    intro w hw
    have hw0 : w ≠ 0 := ((mem_unitBallIndices hε w).mp hw).1
    have hpt : ∀ x, forcingSummand ε a g v (x, w) = ε * ∑ i, ∑ t ∈ pathRange w i,
        (Int.sign (w i) : ℝ) * (H w x * discreteDeriv ε i v (x + pathPoint w i t)) := by
      intro x
      have htel := telescoping_pathRange hε.ne' v x w
      simp only [forcingSummand, hw0, ↓reduceDIte]
      rw [htel]
      simp only [hH, centeredIncrement, hw0, ↓reduceDIte, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
      ring
    have hsx : ∀ i (t : ℤ), Summable fun x =>
        (Int.sign (w i) : ℝ) * (H w x * discreteDeriv ε i v (x + pathPoint w i t)) :=
      fun i t => (summable_mul_of_memL2 (hHm w)
        (memL2_comp_add_right (hDv i) (pathPoint w i t))).mul_left _
    rw [tsum_congr hpt, tsum_mul_left,
      Summable.tsum_finsetSum fun i _ => summable_sum fun t _ => hsx i t]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun t _ => hsx i t]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [tsum_mul_left, hT]
    congr 1
    beta_reduce
    rw [← (Equiv.addRight (pathPoint w i t)).tsum_eq
      (fun y => H w (y - pathPoint w i t) * discreteDeriv ε i v y)]
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have hG : ∀ i, latticeInner ε (forcingField ε a g i) (discreteDeriv ε i v) =
      ε ^ d * (ε ^ (d + 1) / 2 * ∑ w ∈ S, ∑ t ∈ pathRange w i, (Int.sign (w i) : ℝ) * T w i t) := by
    intro i
    unfold latticeInner
    congr 1
    have hpt : ∀ y, forcingField ε a g i y * discreteDeriv ε i v y =
        ε ^ (d + 1) / 2 * ∑ w ∈ S, ∑ t ∈ pathRange w i,
          (Int.sign (w i) : ℝ) * (H w (y - pathPoint w i t) * discreteDeriv ε i v y) := by
      intro y
      rw [forcingField_eq]
      simp only [hH, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [tsum_congr hpt, tsum_mul_left, Summable.tsum_finsetSum fun w _ =>
      summable_sum fun t _ => (hsumT w i t).mul_left _]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Summable.tsum_finsetSum fun t _ => (hsumT w i t).mul_left _]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [tsum_mul_left]
  rw [hS1, Finset.sum_congr rfl hS2]
  simp_rw [hG]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-! ### The long jumps -/

/-- On the long jumps, the series (3.4) is at most `λ⁻¹ C K κ_ε⁻¹ ‖v‖` in absolute value, where
`C` bounds `ε^d ∑_{|εw| ≥ 1} |εw|^{-(d+2)}`. -/
theorem abs_forcing_long_le (hd : 1 ≤ d) {ε lam K Cext : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {g v : Site d → ℝ} (hg : MemL2 g) (hv : MemL2 v) (hK : 0 ≤ K)
    (hgK : ∀ w : Site d,
      latticeNorm ε (fun q => g (q + w) - g q) ≤ K * min (radius (physical ε w)) 1)
    (hCs : Summable fun w : Site d => if 1 ≤ radius (physical ε w) then
      radius (physical ε w) ^ (-((d : ℝ) + 2)) else 0)
    (hC : ε ^ d * ∑' w : Site d, (if 1 ≤ radius (physical ε w) then
      radius (physical ε w) ^ (-((d : ℝ) + 2)) else 0) ≤ Cext) :
    |ε ^ (2 * d) / (2 * kappa d ε) * ∑' p : Site d × Site d,
        (if p.2 ∈ unitBallIndices d ε then 0 else forcingSummand ε a g v p)| ≤
      lam⁻¹ * Cext * K / kappa d ε * latticeNorm ε v := by
  set S := unitBallIndices d ε with hSdef
  set E : Site d → ℝ := fun w => if w ∈ S ∨ w = 0 then 0 else jumpKernel (physical ε w)
    with hE
  have hκ := kappa_pos hd hε hε1
  have hI : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.1.le
  have hE0 : ∀ w, 0 ≤ E w := fun w => by
    simp only [hE]
    split_ifs
    · exact le_rfl
    · exact jumpKernel_nonneg _
  have hEJ : ∀ w, E w ≤ jumpKernel (physical ε w) := fun w => by
    simp only [hE]
    split_ifs
    · exact jumpKernel_nonneg _
    · exact le_rfl
  have hEs : Summable E :=
    (summable_jumpKernel_of_one_le hd hε).of_nonneg_of_le hE0 hEJ
  have hEC : ∀ w, E w ≤ (if 1 ≤ radius (physical ε w) then
      radius (physical ε w) ^ (-((d : ℝ) + 2)) else 0) := by
    intro w
    simp only [hE]
    by_cases h : w ∈ S ∨ w = 0
    · simp only [h, ↓reduceIte]
      split_ifs
      · exact Real.rpow_nonneg (radius_nonneg _) _
      · exact le_rfl
    · simp only [h, ↓reduceIte]
      have h' := not_or.mp h
      have hr : 1 < radius (physical ε w) := lt_of_not_ge fun hr =>
        h'.1 ((mem_unitBallIndices hε w).mpr ⟨h'.2, hr⟩)
      simp only [hr.le, ↓reduceIte]
      rw [jumpKernel_of_ne_zero (fun h'' => h'.2 ((physical_eq_zero_iff hε w).mp h'')),
        Real.rpow_neg (radius_nonneg _),
        show ((d : ℝ) + 2) = ((d + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  set B : Site d × Site d → ℝ := fun p => lam⁻¹ * E p.2 *
    (|g (p.1 + p.2) - g p.1| * |v (p.1 + p.2) - v p.1|) with hB
  have hB0 : ∀ p, 0 ≤ B p := fun p =>
    mul_nonneg (mul_nonneg hI (hE0 _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hLB : ∀ p : Site d × Site d,
      ‖(if p.2 ∈ S then 0 else forcingSummand ε a g v p)‖ ≤ B p := by
    rintro ⟨x, w⟩
    rw [Real.norm_eq_abs]
    by_cases hwS : w ∈ S
    · simp only [hwS, ↓reduceIte, abs_zero]
      exact hB0 _
    by_cases hw0 : w = 0
    · subst hw0
      simp only [hwS, ↓reduceIte, forcingSummand, ↓reduceDIte, abs_zero]
      exact hB0 _
    have hEw : E w = jumpKernel (physical ε w) := by
      simp only [hE, hwS, hw0, or_self, ↓reduceIte]
    simp only [hwS, ↓reduceIte, forcingSummand, hw0, ↓reduceDIte, hB, hEw]
    have hJ := jumpKernel_nonneg (physical ε w)
    have hα := abs_sub_one_le hlam (ha (edgeAdd x w hw0))
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hJ]
    calc |a (edgeAdd x w hw0) - 1| * jumpKernel (physical ε w) * |g (x + w) - g x| *
          |v (x + w) - v x|
        = |a (edgeAdd x w hw0) - 1| * (jumpKernel (physical ε w) *
          (|g (x + w) - g x| * |v (x + w) - v x|)) := by ring
      _ ≤ lam⁻¹ * (jumpKernel (physical ε w) * (|g (x + w) - g x| * |v (x + w) - v x|)) :=
          mul_le_mul_of_nonneg_right hα
            (mul_nonneg hJ (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = _ := by ring
  have hBs : Summable B := by
    refine (((summable_jumpKernel_mul_increment_sq hd hε hg).add
      (summable_jumpKernel_mul_increment_sq hd hε hv)).mul_left lam⁻¹).of_nonneg_of_le hB0
      fun p => ?_
    have hJ := jumpKernel_nonneg (physical ε p.2)
    have hab : |g (p.1 + p.2) - g p.1| * |v (p.1 + p.2) - v p.1| ≤
        (g (p.1 + p.2) - g p.1) ^ 2 + (v (p.1 + p.2) - v p.1) ^ 2 := by
      nlinarith [sq_nonneg (|g (p.1 + p.2) - g p.1| - |v (p.1 + p.2) - v p.1|),
        sq_abs (g (p.1 + p.2) - g p.1), sq_abs (v (p.1 + p.2) - v p.1)]
    calc B p ≤ lam⁻¹ * jumpKernel (physical ε p.2) *
          ((g (p.1 + p.2) - g p.1) ^ 2 + (v (p.1 + p.2) - v p.1) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hEJ _) hI) hab
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hI hJ)
      _ = _ := by ring
  have h1 := tsum_of_norm_bounded hBs.hasSum hLB
  rw [Real.norm_eq_abs] at h1
  have hBc : Summable fun p : Site d × Site d => B (Equiv.prodComm _ _ p) :=
    (Equiv.summable_iff (f := B) (Equiv.prodComm _ _)).mpr hBs
  have h2 : ∑' p, B p = ∑' w, lam⁻¹ * E w *
      ∑' x, |g (x + w) - g x| * |v (x + w) - v x| := by
    rw [← (Equiv.prodComm (Site d) (Site d)).tsum_eq, hBc.tsum_prod]
    refine tsum_congr fun w => ?_
    rw [← tsum_mul_left]
    rfl
  have h3 : ∀ w, ∑' x, |g (x + w) - g x| * |v (x + w) - v x| ≤
      2 * K * latticeNorm ε v / ε ^ d := by
    intro w
    rw [le_div_iff₀ (pow_pos hε d), mul_comm]
    calc ε ^ d * ∑' x, |g (x + w) - g x| * |v (x + w) - v x|
        ≤ latticeNorm ε (fun x => g (x + w) - g x) * latticeNorm ε (fun x => v (x + w) - v x) :=
          pow_mul_tsum_abs_mul_le hε.le (memL2_sub (memL2_comp_add_right hg w) hg)
            (memL2_sub (memL2_comp_add_right hv w) hv)
      _ ≤ (K * 1) * (2 * latticeNorm ε v) :=
          mul_le_mul ((hgK w).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK))
            (latticeNorm_sub_shift_le hε.le hv w) (Real.sqrt_nonneg _)
            (by rw [mul_one]; exact hK)
      _ = 2 * K * latticeNorm ε v := by ring
  have hc0 : 0 ≤ 2 * K * latticeNorm ε v / ε ^ d :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two hK) (Real.sqrt_nonneg _))
      (pow_nonneg hε.le d)
  have h4 : ∑' w, lam⁻¹ * E w * ∑' x, |g (x + w) - g x| * |v (x + w) - v x| ≤
      lam⁻¹ * (2 * K * latticeNorm ε v / ε ^ d) * ∑' w, E w := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun w => ?_) ?_ (hEs.mul_left _)
    · calc lam⁻¹ * E w * ∑' x, |g (x + w) - g x| * |v (x + w) - v x|
          ≤ lam⁻¹ * E w * (2 * K * latticeNorm ε v / ε ^ d) :=
            mul_le_mul_of_nonneg_left (h3 w) (mul_nonneg hI (hE0 w))
        _ = _ := by ring
    · refine hBc.prod.congr fun w => ?_
      rw [← tsum_mul_left]
      rfl
  have h5 : ∑' w, E w ≤ Cext / ε ^ d := by
    rw [le_div_iff₀ (pow_pos hε d), mul_comm]
    exact (mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hEC hEs hCs)
      (pow_nonneg hε.le d)).trans hC
  have hX : |∑' p : Site d × Site d, (if p.2 ∈ S then 0 else forcingSummand ε a g v p)| ≤
      lam⁻¹ * (2 * K * latticeNorm ε v / ε ^ d) * (Cext / ε ^ d) :=
    h1.trans (h2 ▸ h4.trans (mul_le_mul_of_nonneg_left h5 (mul_nonneg hI hc0)))
  rw [abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg hε.le _) (by positivity))]
  calc ε ^ (2 * d) / (2 * kappa d ε) *
        |∑' p : Site d × Site d, (if p.2 ∈ S then 0 else forcingSummand ε a g v p)|
      ≤ ε ^ (2 * d) / (2 * kappa d ε) *
        (lam⁻¹ * (2 * K * latticeNorm ε v / ε ^ d) * (Cext / ε ^ d)) :=
        mul_le_mul_of_nonneg_left hX (div_nonneg (pow_nonneg hε.le _) (by positivity))
    _ = lam⁻¹ * Cext * K / kappa d ε * latticeNorm ε v := by
        have hεd : ε ^ d ≠ 0 := pow_ne_zero _ hε.ne'
        rw [show ε ^ (2 * d) = ε ^ d * ε ^ d by ring]
        field_simp

/-! ### Proposition 3.2 for a general function -/

/-- **Proposition 3.2** (`prop:forcing`) for a square-summable function `g` with the increment
bound `‖g(· + w) - g‖ ≤ K min(|εw|, 1)`: there is `C > 0`, depending only on `d` and `λ`, such
that `|⟨(L̄ - L^ε) g, v⟩ - κ_ε⁻¹ ⟨G, D v⟩| ≤ C K κ_ε⁻¹ ‖v‖` for every `v ∈ L²(εℤ^d)`, where `G` is
the vector field (3.3) built from `g`. -/
theorem forcing_representation_of_increment (hd : 1 ≤ d) {lam : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (K : ℝ) (g : Site d → ℝ), MemL2 g →
      (∀ w : Site d,
        latticeNorm ε (fun q => g (q + w) - g q) ≤ K * min (radius (physical ε w)) 1) →
      MemL2 (fun q => meanGenerator ε g q - generator ε a g q) ∧
      (∀ i, MemL2 (forcingField ε a g i)) ∧
      ∀ v : Site d → ℝ, MemL2 v →
        |latticeInner ε (fun q => meanGenerator ε g q - generator ε a g q) v -
          (kappa d ε)⁻¹ * ∑ i, latticeInner ε (forcingField ε a g i) (discreteDeriv ε i v)| ≤
          C * K / kappa d ε * latticeNorm ε v := by
  obtain ⟨Cext, hCpos, hext⟩ :=
    LatticeProb.Euclidean.Estimates.exterior_rpow_sum_bound d hd ((d : ℝ) + 2) (by linarith)
  refine ⟨lam⁻¹ * Cext, mul_pos (inv_pos.mpr hlam.1) hCpos, fun ε hε a ha K g hg hgK => ?_⟩
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := by linarith [hε.2]
  obtain ⟨hCs, hC⟩ := hext ε ⟨hε0, by linarith [hε.2]⟩
  have hK : 0 ≤ K := by
    have h := hgK (Pi.single ⟨0, hd⟩ 1)
    rw [radius_physical_single hε0.le, min_eq_left hε1] at h
    refine le_of_not_gt fun hK => ?_
    have : K * ε < 0 := mul_neg_of_neg_of_pos hK hε0
    linarith [Real.sqrt_nonneg (latticeNormSq ε
      (fun q => g (q + Pi.single ⟨0, hd⟩ 1) - g q)), show latticeNorm ε
      (fun q => g (q + Pi.single ⟨0, hd⟩ 1) - g q) = Real.sqrt (latticeNormSq ε
      (fun q => g (q + Pi.single ⟨0, hd⟩ 1) - g q)) from rfl]
  refine ⟨(forcing_sum hd hε0 hlam ha hg hg).1, fun i => memL2_forcingField hlam ha hg ε i,
    fun v hv => ?_⟩
  obtain ⟨-, hsF, hsum⟩ := forcing_sum hd hε0 hlam ha hg hv
  have hsplit : ∑' p, forcingSummand ε a g v p =
      ∑' p : Site d × Site d, (if p.2 ∈ unitBallIndices d ε then forcingSummand ε a g v p
        else 0) +
      ∑' p : Site d × Site d, (if p.2 ∈ unitBallIndices d ε then 0
        else forcingSummand ε a g v p) := by
    rw [← Summable.tsum_add]
    · refine tsum_congr fun p => ?_
      split_ifs <;> simp
    · exact (hsF.indicator {p | p.2 ∈ unitBallIndices d ε}).congr fun p => by
        simp [Set.indicator_apply]
    · exact (hsF.indicator {p | p.2 ∈ unitBallIndices d ε}ᶜ).congr fun p => by
        by_cases h : p.2 ∈ unitBallIndices d ε <;> simp [h]
  rw [hsum, hsplit, mul_add, forcing_short hd hε0 hlam ha hg hv, add_sub_cancel_left]
  calc _ ≤ lam⁻¹ * Cext * K / kappa d ε * latticeNorm ε v :=
        abs_forcing_long_le hd hε0 hε1 hlam ha hg hv hK hgK hCs hC
    _ = _ := by ring

end

end LongRangeHeat
