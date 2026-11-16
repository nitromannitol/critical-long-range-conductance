import LongRangeHeat.Continuum

/-!
# Regularity of the continuum solution on the lattice

Lemma 2.2 (`lem:sampling`) and the bounds (2.6) and (2.7). For `f ∈ C_c^∞(ℝ^d)`, the rescaled
square sums of `∂^β ū(s, ·)` over every translate of `εℤ^d` are bounded uniformly in
`ε ∈ (0, 1/2)`, `s ≥ 0` and the translation (`sampling_bound`).

As in the paper, a bounded function vanishing outside a ball has bounded rescaled square sums,
because a ball of radius `R` contains at most `C (R / ε)^d` points of a translate of `εℤ^d`
(`sum_sq_le_of_bound`). Jensen's inequality for the probability density `Φ_s` transfers such a
bound, uniform over the translates, from a function `g` to `Φ_s * g` (`sum_sq_continuumHeat_le`).

For (2.6) and (2.7), the increment `ū_s(· + z) - ū_s` and the second-order Taylor remainder of `ū_s`
are the heat flow of the increment and of the Taylor remainder of `f`. These are bounded pointwise
by `C min(|z|, 1)` and `C |z|³` (Taylor's formula) and vanish outside two translates of the
support of `f`, so the same two steps give `increment_bound` and `taylor_bound`. Here `|z|` is the
Euclidean norm `radius z`.
-/

namespace LongRangeHeat

open MeasureTheory Filter Topology Set LatticeProb LatticeProb.Heat LatticeProb.Euclidean.Lattice
open scoped ContDiff

noncomputable section

variable {d : ℕ}

/-! ### Counting lattice points -/

theorem natCast_toNat_le {m : ℤ} {X : ℝ} (h : (m : ℝ) ≤ X) (hX : 0 ≤ X) :
    (m.toNat : ℝ) ≤ X := by
  rcases le_or_gt 0 m with hm | hm
  · have : ((m.toNat : ℤ) : ℝ) = m := by rw [Int.toNat_of_nonneg hm]
    rw [← this] at h
    exact_mod_cast h
  · rw [Int.toNat_of_nonpos hm.le]
    simpa using hX

/-- A sup-norm ball of radius `R` contains at most `((2R + 1) / ε)^d` points of a translate of
`εℤ^d` when `ε ≤ 1`. -/
theorem card_filter_norm_sub_le {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (y c : Fin d → ℝ) (T : Finset (Site d)) :
    ((T.filter fun q => ‖physical ε q + y - c‖ ≤ R).card : ℝ) ≤ ((2 * R + 1) / ε) ^ d := by
  classical
  set box : Finset (Site d) := Fintype.piFinset fun i =>
    Finset.Icc ⌈(c i - y i - R) / ε⌉ ⌊(c i - y i + R) / ε⌋ with hbox
  have hsub : T.filter (fun q => ‖physical ε q + y - c‖ ≤ R) ⊆ box := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [hbox, Fintype.mem_piFinset]
    intro i
    have hi : |ε * q i + y i - c i| ≤ R := by
      have h := norm_le_pi_norm (physical ε q + y - c) i
      simp only [Pi.sub_apply, Pi.add_apply, physical, Real.norm_eq_abs] at h
      exact h.trans hq.2
    rw [abs_le] at hi
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hε, le_div_iff₀ hε]
    constructor <;> linarith [mul_comm ε (q i : ℝ)]
  have hcard : ∀ i : Fin d,
      ((Finset.Icc ⌈(c i - y i - R) / ε⌉ ⌊(c i - y i + R) / ε⌋).card : ℝ) ≤ (2 * R + 1) / ε := by
    intro i
    rw [Int.card_Icc]
    apply natCast_toNat_le _ (by positivity)
    have h1 := Int.floor_le ((c i - y i + R) / ε)
    have h2 := Int.le_ceil ((c i - y i - R) / ε)
    have h3 : (c i - y i + R) / ε - (c i - y i - R) / ε = 2 * R / ε := by
      field_simp
      ring
    have h4 : 2 * R / ε + 1 ≤ (2 * R + 1) / ε := by
      rw [add_div]
      have : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
      linarith
    push_cast
    linarith
  calc ((T.filter fun q => ‖physical ε q + y - c‖ ≤ R).card : ℝ) ≤ box.card := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ∏ i, ((Finset.Icc ⌈(c i - y i - R) / ε⌉ ⌊(c i - y i + R) / ε⌋).card : ℝ) := by
        rw [hbox, Fintype.card_piFinset]
        push_cast
        rfl
    _ ≤ ∏ _i : Fin d, (2 * R + 1) / ε := by
        gcongr with i
        exact hcard i
    _ = ((2 * R + 1) / ε) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A function bounded by `M` that vanishes outside two sup-norm balls of radius `R` has rescaled
square sums at most `2 M² (2R + 1)^d` over every translate of `εℤ^d`, for `ε ≤ 1`. -/
theorem sum_sq_le_of_bound {h : (Fin d → ℝ) → ℝ} {M R ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R) (hM : ∀ x, |h x| ≤ M) (c₁ c₂ : Fin d → ℝ)
    (hsupp : ∀ x, h x ≠ 0 → ‖x - c₁‖ ≤ R ∨ ‖x - c₂‖ ≤ R) (y : Fin d → ℝ)
    (T : Finset (Site d)) :
    ε ^ d * ∑ q ∈ T, h (physical ε q + y) ^ 2 ≤ 2 * M ^ 2 * (2 * R + 1) ^ d := by
  classical
  have hpt : ∀ x, h x ^ 2 ≤
      (if ‖x - c₁‖ ≤ R then M ^ 2 else 0) + (if ‖x - c₂‖ ≤ R then M ^ 2 else 0) := by
    intro x
    have hsq : h x ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
    by_cases hx : h x = 0
    · rw [hx]
      split_ifs <;> nlinarith [sq_nonneg M]
    · rcases hsupp x hx with h1 | h1
      · have e : (if ‖x - c₁‖ ≤ R then M ^ 2 else 0) = M ^ 2 := by simp [h1]
        rw [e]
        split_ifs <;> nlinarith [sq_nonneg M]
      · have e : (if ‖x - c₂‖ ≤ R then M ^ 2 else 0) = M ^ 2 := by simp [h1]
        rw [e]
        split_ifs <;> nlinarith [sq_nonneg M]
  have hsum : ∑ q ∈ T, h (physical ε q + y) ^ 2 ≤
      M ^ 2 * (T.filter fun q => ‖physical ε q + y - c₁‖ ≤ R).card +
        M ^ 2 * (T.filter fun q => ‖physical ε q + y - c₂‖ ≤ R).card := by
    refine (Finset.sum_le_sum fun q _ => hpt _).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib]
    congr 1 <;>
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_comm]
  have hc1 := card_filter_norm_sub_le hε hε1 hR y c₁ T
  have hc2 := card_filter_norm_sub_le hε hε1 hR y c₂ T
  have hεd : 0 < ε ^ d := pow_pos hε d
  calc ε ^ d * ∑ q ∈ T, h (physical ε q + y) ^ 2
      ≤ ε ^ d * (M ^ 2 * ((2 * R + 1) / ε) ^ d + M ^ 2 * ((2 * R + 1) / ε) ^ d) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans ?_) hεd.le
        gcongr
    _ = 2 * M ^ 2 * (2 * R + 1) ^ d := by
        rw [div_pow]
        field_simp
        ring

/-- Uniform bounds on the finite partial sums give summability and the bound on the series. -/
theorem summable_and_tsum_le_of_sum_le {v : Site d → ℝ} {ε B : ℝ} (hε : 0 < ε)
    (h : ∀ T : Finset (Site d), ε ^ d * ∑ q ∈ T, v q ^ 2 ≤ B) :
    Summable (fun q => v q ^ 2) ∧ ε ^ d * ∑' q, v q ^ 2 ≤ B := by
  have hεd : 0 < ε ^ d := pow_pos hε d
  have h' : ∀ T : Finset (Site d), ∑ q ∈ T, v q ^ 2 ≤ B / ε ^ d := fun T => by
    rw [le_div_iff₀ hεd, mul_comm]
    exact h T
  have hnn : 0 ≤ fun q => v q ^ 2 := fun q => sq_nonneg _
  refine ⟨summable_of_sum_le hnn h', ?_⟩
  have := Real.tsum_le_of_sum_le hnn h'
  rw [le_div_iff₀ hεd] at this
  linarith [mul_comm (ε ^ d) (∑' q, v q ^ 2)]

/-- Uniform bounds on the finite partial sums give membership in `L²(εℤ^d)` and a norm bound. -/
theorem memL2_and_latticeNorm_le {v : Site d → ℝ} {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (h : ∀ T : Finset (Site d), ε ^ d * ∑ q ∈ T, v q ^ 2 ≤ A ^ 2) :
    MemL2 v ∧ latticeNorm ε v ≤ A := by
  obtain ⟨h1, h2⟩ := summable_and_tsum_le_of_sum_le hε h
  exact ⟨h1, Real.sqrt_le_iff.2 ⟨hA, h2⟩⟩

/-! ### Jensen's inequality for the heat kernel -/

theorem integrable_heatKernel_mul_bdd (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s)
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) :
    Integrable (fun w => heatKernel d s w * g w) :=
  (integrable_heatKernel hd hs).mul_bdd hg.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hM x)

/-- Jensen's inequality: `|Φ_s * g(x)|² ≤ Φ_s * |g|²(x)`, since `Φ_s` is a probability
density. -/
theorem sq_continuumHeat_le (hd : 1 ≤ d) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) {s : ℝ} (hs : 0 < s) (x : Fin d → ℝ) :
    continuumHeat g s x ^ 2 ≤ ∫ w, heatKernel d s w * g (x - w) ^ 2 := by
  rw [continuumHeat_eq_integral g hs]
  set m := ∫ w, heatKernel d s w * g (x - w)
  have hc1 : Continuous fun w => g (x - w) := hg.comp (continuous_const.sub continuous_id)
  have hb1 : ∀ w, |g (x - w)| ≤ M := fun w => hM _
  have hb2 : ∀ w, |g (x - w) ^ 2| ≤ M ^ 2 := fun w => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb1 w) 2
  have i0 := integrable_heatKernel hd hs
  have i1 : Integrable (fun w => heatKernel d s w * g (x - w)) :=
    integrable_heatKernel_mul_bdd hd hs hc1 hb1
  have i2 : Integrable (fun w => heatKernel d s w * g (x - w) ^ 2) :=
    integrable_heatKernel_mul_bdd hd hs (g := fun w => g (x - w) ^ 2) (hc1.pow 2) hb2
  have hexp : ∫ w, heatKernel d s w * (g (x - w) - m) ^ 2 =
      (∫ w, heatKernel d s w * g (x - w) ^ 2) - 2 * m * m + m ^ 2 * 1 := by
    have : (fun w => heatKernel d s w * (g (x - w) - m) ^ 2) = fun w =>
        (heatKernel d s w * g (x - w) ^ 2 - (2 * m) * (heatKernel d s w * g (x - w))) +
          m ^ 2 * heatKernel d s w := by
      funext w
      ring
    have iA : Integrable (fun w => heatKernel d s w * g (x - w) ^ 2 -
        (2 * m) * (heatKernel d s w * g (x - w))) := i2.sub (i1.const_mul _)
    have iB : Integrable (fun w => (2 * m) * (heatKernel d s w * g (x - w))) := i1.const_mul _
    have iC : Integrable (fun w => m ^ 2 * heatKernel d s w) := i0.const_mul _
    rw [this, integral_add iA iC, integral_sub i2 iB, integral_const_mul, integral_const_mul,
      integral_heatKernel hd hs]
  have hnn : 0 ≤ ∫ w, heatKernel d s w * (g (x - w) - m) ^ 2 :=
    integral_nonneg fun w => mul_nonneg (heatKernel_nonneg hd _ _) (sq_nonneg _)
  nlinarith [hexp, hnn]

/-- A bound on the rescaled square sums of `g`, uniform over the translates of `εℤ^d`, holds for
`ū = Φ_s * g` at every time `s ≥ 0`. -/
theorem sum_sq_continuumHeat_le (hd : 1 ≤ d) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) {ε B : ℝ}
    (hB : ∀ (y : Fin d → ℝ) (T : Finset (Site d)),
      ε ^ d * ∑ q ∈ T, g (physical ε q + y) ^ 2 ≤ B)
    (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) (y : Fin d → ℝ) (T : Finset (Site d)) :
    ε ^ d * ∑ q ∈ T, continuumHeat g s (physical ε q + y) ^ 2 ≤ B := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa [continuumHeat_zero] using hB y T
  have hεd : 0 < ε ^ d := pow_pos hε d
  have hc : ∀ q : Site d, Continuous fun w => g (physical ε q + y - w) := fun q =>
    hg.comp (continuous_const.sub continuous_id)
  have hb : ∀ (q : Site d) (w : Fin d → ℝ), |g (physical ε q + y - w) ^ 2| ≤ M ^ 2 :=
    fun q w => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM _) 2
  have hint : ∀ q : Site d,
      Integrable fun w => heatKernel d s w * g (physical ε q + y - w) ^ 2 := fun q =>
    integrable_heatKernel_mul_bdd hd hs ((hc q).pow 2) (hb q)
  set G : (Fin d → ℝ) → ℝ := fun w => ε ^ d * ∑ q ∈ T, g (physical ε q + (y - w)) ^ 2
  have hGc : Continuous G := continuous_const.mul (continuous_finsetSum _ fun q _ =>
    (hg.comp (continuous_const.add (continuous_const.sub continuous_id))).pow 2)
  have hGb : ∀ w, |G w| ≤ B := fun w => by
    rw [abs_of_nonneg (mul_nonneg hεd.le (Finset.sum_nonneg fun q _ => sq_nonneg _))]
    exact hB _ T
  calc ε ^ d * ∑ q ∈ T, continuumHeat g s (physical ε q + y) ^ 2
      ≤ ε ^ d * ∑ q ∈ T, ∫ w, heatKernel d s w * g (physical ε q + y - w) ^ 2 := by
        gcongr with q hq
        exact sq_continuumHeat_le hd hg hM hs _
    _ = ∫ w, heatKernel d s w * G w := by
        rw [← integral_finsetSum T fun q _ => hint q, ← integral_const_mul]
        congr 1
        funext w
        simp only [G, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [show physical ε q + y - w = physical ε q + (y - w) by abel]
        ring
    _ ≤ ∫ w, heatKernel d s w * B :=
        integral_mono (integrable_heatKernel_mul_bdd hd hs hGc hGb)
          ((integrable_heatKernel hd hs).mul_const B) fun w =>
          mul_le_mul_of_nonneg_left (le_of_abs_le (hGb w)) (heatKernel_nonneg hd _ _)
    _ = B := by rw [integral_mul_const, integral_heatKernel hd hs, one_mul]

/-- The rescaled square sums of `Φ_s * g` over the translates of `εℤ^d` are bounded uniformly,
for a continuous compactly supported `g`. -/
theorem exists_sum_sq_continuumHeat_le (hd : 1 ≤ d) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℝ, 0 ≤ s → ∀ y : Fin d → ℝ,
      Summable (fun q : Site d => continuumHeat g s (physical ε q + y) ^ 2) ∧
      ε ^ d * ∑' q : Site d, continuumHeat g s (physical ε q + y) ^ 2 ≤ C := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hM' : ∀ x, |g x| ≤ M := fun x => by simpa [Real.norm_eq_abs] using hM x
  refine ⟨2 * M ^ 2 * (2 * max R 0 + 1) ^ d, fun ε hε hε1 s hs y =>
    summable_and_tsum_le_of_sum_le hε fun T => ?_⟩
  refine sum_sq_continuumHeat_le hd hg hM' (fun y T => ?_) hε hs y T
  refine sum_sq_le_of_bound hε hε1 (le_max_right _ _) hM' 0 0 (fun x hx => Or.inl ?_) y T
  have := hR (subset_tsupport _ hx)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  rw [sub_zero]
  exact this.trans (le_max_left _ _)

/-- **Lemma 2.2** (`lem:sampling`, (2.5)). -/
theorem sampling_bound (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (β : Fin d → ℕ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s → ∀ y : Fin d → ℝ,
      Summable (fun q : Site d => |multiDeriv β (continuumHeat f s) (physical ε q + y)| ^ 2) ∧
      ε ^ d * ∑' q : Site d, |multiDeriv β (continuumHeat f s) (physical ε q + y)| ^ 2 ≤ C := by
  obtain ⟨hβ, hβc⟩ := contDiff_multiDeriv hf hfc β
  obtain ⟨C, hC⟩ := exists_sum_sq_continuumHeat_le hd hβ.continuous hβc
  refine ⟨C, fun ε hε s hs y => ?_⟩
  simp_rw [sq_abs, multiDeriv_continuumHeat hd hf hfc hs β]
  exact hC ε hε.1 (by linarith [hε.2]) s hs y

/-! ### Increments and Taylor remainders -/

theorem integrable_heatKernel_sub_mul {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (t : ℝ) (x : Fin d → ℝ) :
    Integrable (fun y => heatKernel d t (x - y) * g y) := by
  have hk : Continuous (fun y => heatKernel d t (x - y)) := by
    rcases le_or_gt t 0 with ht | ht
    · simp only [heatKernel_of_nonpos ht]
      exact continuous_const
    · exact (continuous_heatKernel ht).comp (continuous_const.sub continuous_id)
  exact (hk.mul hg).integrable_of_hasCompactSupport hgc.mul_left

theorem continuumHeat_sub {g₁ g₂ : (Fin d → ℝ) → ℝ} (h₁ : Continuous g₁)
    (h₁c : HasCompactSupport g₁) (h₂ : Continuous g₂) (h₂c : HasCompactSupport g₂) (t : ℝ)
    (x : Fin d → ℝ) :
    continuumHeat (fun y => g₁ y - g₂ y) t x = continuumHeat g₁ t x - continuumHeat g₂ t x := by
  unfold continuumHeat
  split_ifs
  · rfl
  · simp_rw [mul_sub]
    exact integral_sub (integrable_heatKernel_sub_mul h₁ h₁c t x)
      (integrable_heatKernel_sub_mul h₂ h₂c t x)

theorem continuumHeat_add_right (g : (Fin d → ℝ) → ℝ) (t : ℝ) (x z : Fin d → ℝ) :
    continuumHeat g t (x + z) = continuumHeat (fun y => g (y + z)) t x := by
  unfold continuumHeat
  split_ifs
  · rfl
  · rw [← integral_add_right_eq_self _ z]
    congr 1
    funext y
    rw [show x + z - (y + z) = x - y by abel]

/-- The sup norm is at most the Euclidean norm. -/
theorem norm_le_radius (z : Fin d → ℝ) : ‖z‖ ≤ radius z :=
  (pi_norm_le_iff_of_nonneg (radius_nonneg z)).2 fun k => by
    simpa [Real.norm_eq_abs] using abs_coord_le_radius z k

/-- The lattice norm of `ū_s` sampled on `εℤ^d`, for `ū = Φ_s * h` with `|h| ≤ A` and `h`
vanishing outside `K ∪ (K - z)`, where `K` lies in a ball of radius `R`. -/
theorem memL2_and_latticeNorm_continuumHeat_le (hd : 1 ≤ d) {K : Set (Fin d → ℝ)} {R : ℝ}
    (hR : 0 ≤ R) (hK : K ⊆ Metric.closedBall 0 R) {h : (Fin d → ℝ) → ℝ} (hh : Continuous h)
    {A : ℝ} (hA : ∀ x, |h x| ≤ A) (z : Fin d → ℝ) (hsupp : ∀ y, h y ≠ 0 → y + z ∈ K ∨ y ∈ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    MemL2 (fun q : Site d => continuumHeat h s (physical ε q)) ∧
      latticeNorm ε (fun q : Site d => continuumHeat h s (physical ε q)) ≤
        Real.sqrt (2 * (2 * R + 1) ^ d) * A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  refine memL2_and_latticeNorm_le hε (by positivity) fun T => ?_
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsupp' : ∀ x, h x ≠ 0 → ‖x - -z‖ ≤ R ∨ ‖x - 0‖ ≤ R := fun x hx => by
    rcases hsupp x hx with h1 | h1
    · left
      have := hK h1
      rwa [Metric.mem_closedBall, dist_zero_right, ← sub_neg_eq_add] at this
    · right
      have := hK h1
      rwa [Metric.mem_closedBall, dist_zero_right, ← sub_zero x] at this
  have := sum_sq_continuumHeat_le hd hh hA (B := 2 * A ^ 2 * (2 * R + 1) ^ d)
    (fun y T => sum_sq_le_of_bound hε hε1 hR hA (-z) 0 hsupp' y T) hε hs 0 T
  simp only [add_zero] at this
  linarith

theorem exists_tsupport_subset_closedBall {f : (Fin d → ℝ) → ℝ} (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ tsupport f ⊆ Metric.closedBall 0 R := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  exact ⟨max R 0, le_max_right _ _,
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩

theorem hasCompactSupport_comp_add_right {f : (Fin d → ℝ) → ℝ} (hfc : HasCompactSupport f)
    (z : Fin d → ℝ) : HasCompactSupport (fun y => f (y + z)) :=
  hfc.comp_homeomorph (Homeomorph.addRight z)

/-- The increment bound (2.6): `‖ū_s(· + z) - ū_s‖_{L²(εℤ^d)} ≤ C min(|z|, 1)`. -/
theorem increment_bound (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s → ∀ z : Fin d → ℝ,
      MemL2 (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q)) ∧
      latticeNorm ε (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q)) ≤
          C * min (radius z) 1 := by
  obtain ⟨M0, hM0⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨M1, hM1⟩ :=
    (hfc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  obtain ⟨R, hR, hK⟩ := exists_tsupport_subset_closedBall hfc
  have hM00 : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  refine ⟨Real.sqrt (2 * (2 * R + 1) ^ d) * max M1 (2 * M0), fun ε hε s hs z => ?_⟩
  have hcz : Continuous fun y => f (y + z) := hf.continuous.comp (continuous_id.add continuous_const)
  have heq : (fun q : Site d =>
      continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q)) =
      fun q => continuumHeat (fun y => f (y + z) - f y) s (physical ε q) := by
    funext q
    rw [continuumHeat_add_right, continuumHeat_sub hcz (hasCompactSupport_comp_add_right hfc z)
      hf.continuous hfc]
  rw [heq, mul_assoc]
  refine memL2_and_latticeNorm_continuumHeat_le hd hR hK (h := fun y => f (y + z) - f y)
    (hcz.sub hf.continuous) (fun y => ?_) z
    (fun y hy => ?_) hε.1 (by linarith [hε.2]) hs
  · have hlip : |f (y + z) - f y| ≤ M1 * radius z := by
      have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := f)
        (fun x _ => (hf.differentiable (by simp)) x) (fun x _ => hM1 x) (mem_univ y)
        (mem_univ (y + z))
      rw [Real.norm_eq_abs, add_sub_cancel_left] at h
      exact h.trans (mul_le_mul_of_nonneg_left (norm_le_radius z) hM10)
    have hbdd : |f (y + z) - f y| ≤ 2 * M0 := by
      have h1 := hM0 (y + z)
      have h2 := hM0 y
      rw [Real.norm_eq_abs] at h1 h2
      calc |f (y + z) - f y| ≤ |f (y + z)| + |f y| := abs_sub _ _
        _ ≤ 2 * M0 := by linarith
    rcases le_total (radius z) 1 with hz | hz
    · rw [min_eq_left hz]
      exact hlip.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (radius_nonneg z))
    · rw [min_eq_right hz, mul_one]
      exact hbdd.trans (le_max_right _ _)
  · by_contra hcon
    rw [not_or] at hcon
    apply hy
    rw [image_eq_zero_of_notMem_tsupport hcon.1, image_eq_zero_of_notMem_tsupport hcon.2,
      sub_zero]

/-- Taylor's formula of order two with integral remainder gives
`|f(x + z) - f(x) - z · ∇f(x) - ½ z · ∇²f(x) z| ≤ (M / 2) ‖z‖³` when `‖D³f‖ ≤ M`. -/
theorem abs_taylor_two_le {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ M) (x z : Fin d → ℝ) :
    |f (x + z) - f x - fderiv ℝ f x z - 1 / 2 * fderiv ℝ (fderiv ℝ f) x z z| ≤
      M / 2 * ‖z‖ ^ 3 := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := f) (x := x) (y := z)
    fun t _ => hf.contDiffAt.of_le (by simp)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, smul_eq_mul] at h
  have hI : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) f (x + t • z) (fun _ => z)‖
      ≤ M * ‖z‖ ^ 3 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := M * ‖z‖ ^ 3)
      (f := fun t => (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) f (x + t • z) (fun _ => z))
      fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        have h1 : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        have h2 : ‖iteratedFDeriv ℝ (2 + 1) f (x + t • z) (fun _ => z)‖ ≤ M * ‖z‖ ^ 3 := by
          refine ((iteratedFDeriv ℝ (2 + 1) f (x + t • z)).le_opNorm _).trans ?_
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
        rw [norm_smul, Real.norm_eq_abs, abs_pow]
        calc |1 - t| ^ 2 * ‖iteratedFDeriv ℝ (2 + 1) f (x + t • z) (fun _ => z)‖
            ≤ 1 * (M * ‖z‖ ^ 3) := by
              gcongr
              · exact pow_le_one₀ (abs_nonneg _) h1
          _ = M * ‖z‖ ^ 3 := one_mul _
    simpa using this
  have hrem : f (x + z) - f x - fderiv ℝ f x z - 1 / 2 * fderiv ℝ (fderiv ℝ f) x z z =
      (2 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
        (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) f (x + t • z) (fun _ => z) := by
    rw [h]
    simp only [Nat.factorial, Nat.cast_one, inv_one, one_mul]
    norm_num
    ring
  rw [hrem, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), ← Real.norm_eq_abs]
  linarith [hI]

/-- The Taylor bound (2.7): the second-order Taylor remainder of `ū_s` along `z` has
`L²(εℤ^d)` norm at most `C |z|³`. -/
theorem taylor_bound (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s → ∀ z : Fin d → ℝ,
      MemL2 (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q) -
          fderiv ℝ (continuumHeat f s) (physical ε q) z -
          1 / 2 * fderiv ℝ (fderiv ℝ (continuumHeat f s)) (physical ε q) z z) ∧
      latticeNorm ε (fun q : Site d =>
        continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q) -
          fderiv ℝ (continuumHeat f s) (physical ε q) z -
          1 / 2 * fderiv ℝ (fderiv ℝ (continuumHeat f s)) (physical ε q) z z) ≤
        C * radius z ^ 3 := by
  obtain ⟨M3, hM3⟩ := (hfc.iteratedFDeriv 3).exists_bound_of_continuous
    (hf.continuous_iteratedFDeriv (by simp))
  obtain ⟨R, hR, hK⟩ := exists_tsupport_subset_closedBall hfc
  have hM30 : 0 ≤ M3 := (norm_nonneg _).trans (hM3 0)
  refine ⟨Real.sqrt (2 * (2 * R + 1) ^ d) * (M3 / 2), fun ε hε s hs z => ?_⟩
  have hcz : Continuous fun y => f (y + z) :=
    hf.continuous.comp (continuous_id.add continuous_const)
  have hczc := hasCompactSupport_comp_add_right hfc z
  have hD1 : Continuous fun y => fderiv ℝ f y z := (contDiff_fderiv_apply hf z).continuous
  have hD1c : HasCompactSupport fun y => fderiv ℝ f y z := hfc.fderiv_apply (𝕜 := ℝ) z
  have hD2eq : (fun y => fderiv ℝ (fderiv ℝ f) y z z) =
      fun y => fderiv ℝ (fun y' => fderiv ℝ f y' z) y z :=
    funext fun y => (fderiv_fderiv_apply_eq (hf.of_le (by simp)) y z z).symm
  have hD2' : Continuous fun y => fderiv ℝ (fderiv ℝ f) y z z := by
    rw [hD2eq]
    exact (contDiff_fderiv_apply (contDiff_fderiv_apply hf z) z).continuous
  have hD2c' : HasCompactSupport fun y => fderiv ℝ (fderiv ℝ f) y z z := by
    rw [hD2eq]
    exact hD1c.fderiv_apply (𝕜 := ℝ) z
  have hD2 : Continuous fun y => 1 / 2 * fderiv ℝ (fderiv ℝ f) y z z :=
    continuous_const.mul hD2'
  have hD2c : HasCompactSupport fun y => 1 / 2 * fderiv ℝ (fderiv ℝ f) y z z := hD2c'.mul_left
  have hA : Continuous fun y => f (y + z) - f y := hcz.sub hf.continuous
  have hAc : HasCompactSupport fun y => f (y + z) - f y := hczc.sub hfc
  have hB : Continuous fun y => f (y + z) - f y - fderiv ℝ f y z := hA.sub hD1
  have hBc : HasCompactSupport fun y => f (y + z) - f y - fderiv ℝ f y z := hAc.sub hD1c
  have heq : (fun q : Site d =>
      continuumHeat f s (physical ε q + z) - continuumHeat f s (physical ε q) -
        fderiv ℝ (continuumHeat f s) (physical ε q) z -
        1 / 2 * fderiv ℝ (fderiv ℝ (continuumHeat f s)) (physical ε q) z z) =
      fun q => continuumHeat (fun y => f (y + z) - f y - fderiv ℝ f y z -
        1 / 2 * fderiv ℝ (fderiv ℝ f) y z z) s (physical ε q) := by
    funext q
    rw [continuumHeat_add_right, fderiv_continuumHeat_apply hd hf hfc hs,
      fderiv_fderiv_continuumHeat_apply hd hf hfc hs, continuumHeat_sub hB hBc hD2 hD2c,
      continuumHeat_sub hA hAc hD1 hD1c, continuumHeat_sub hcz hczc hf.continuous hfc,
      continuumHeat_const_mul]
  rw [heq, mul_assoc]
  refine memL2_and_latticeNorm_continuumHeat_le hd hR hK
    (h := fun y => f (y + z) - f y - fderiv ℝ f y z - 1 / 2 * fderiv ℝ (fderiv ℝ f) y z z)
    (hB.sub hD2) (fun y => ?_) z (fun y hy => ?_) hε.1 (by linarith [hε.2]) hs
  · exact (abs_taylor_two_le hf hM3 y z).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_le_radius z) 3) (by positivity))
  · by_contra hcon
    rw [not_or] at hcon
    apply hy
    have h1 : f (y + z) = 0 := image_eq_zero_of_notMem_tsupport hcon.1
    have h2 : f y = 0 := image_eq_zero_of_notMem_tsupport hcon.2
    have h3 : fderiv ℝ f y = 0 :=
      Function.notMem_support.1 fun h => hcon.2 (support_fderiv_subset ℝ h)
    have h4 : fderiv ℝ (fderiv ℝ f) y = 0 :=
      Function.notMem_support.1 fun h =>
        hcon.2 (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))
    simp [h1, h2, h3, h4]

end

end LongRangeHeat
