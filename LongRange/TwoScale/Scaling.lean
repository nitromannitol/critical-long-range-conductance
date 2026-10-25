import LongRange.Corrector.Existence

/-!
# Microscopic rescaling on cubes

The integer sites of a physical cube do not depend on the positive lattice spacing.
The Euclidean kernel homogeneity gives the microscopic generator and norm formulas.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The physical open cube of side length `ε * 3 ^ n`. -/
def cube (ε : ℝ) (n : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i| < ε * 3 ^ n / 2}

/-- The integer box underlying a triadic physical cube. -/
def integerBox (d n : ℕ) : Set (Site d) :=
  {q | ∀ i, |(q i : ℝ)| < 3 ^ n / 2}

/-- Positive physical dilation leaves the integer indices of the cube unchanged. -/
theorem latticeSet_cube {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    latticeSet ε (cube ε n) = integerBox d n := by
  ext q
  change (∀ i, |ε * (q i : ℝ)| < ε * 3 ^ n / 2) ↔ _
  simp only [abs_mul, abs_of_pos hε, integerBox, Set.mem_setOf_eq,
    mul_div_assoc, mul_lt_mul_iff_right₀ hε]

/-- Physical cubes are bounded in the coordinate carrier. -/
theorem cube_isBounded (ε : ℝ) (n : ℕ) : Bornology.IsBounded (cube (d := d) ε n) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|ε * 3 ^ n / 2|, ?_⟩
  intro x hx
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
  intro i
  exact (hx i).le.trans (le_abs_self _)

/-- Kernel homogeneity includes the zero increment, where both kernels vanish. -/
theorem jumpKernel_physical_scaling {ε : ℝ} (hε : 0 < ε) (w : Site d) :
    jumpKernel (physical ε w) = (ε ^ (d + 2))⁻¹ * jumpKernel (physical 1 w) := by
  by_cases hw : w = 0
  · subst w
    rw [(physical_eq_zero_iff hε 0).mpr rfl,
      (physical_eq_zero_iff zero_lt_one 0).mpr rfl]
    simp only [jumpKernel_zero, mul_zero]
  · rw [jumpKernel_physical hε hw,
      jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one w).not.mpr hw)]

/-- The affine slope is evaluated at the physical point `εq`. -/
theorem linearFn_scaling (ε : ℝ) (p : Fin d → ℝ) (q : Site d) :
    linearFn ε p q = ε * linearFn 1 p q := by
  simp only [linearFn, physical, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Dividing the generator of `ε f` removes all spacing dependence from its series. -/
theorem generator_microscopic {ε : ℝ} (hε : 0 < ε) (a : Edge d → ℝ)
    (f : Site d → ℝ) (q : Site d) :
    generator ε a (fun x => ε * f x) q = (ε * kappa d ε)⁻¹ *
      ∑' w : Site d, if hw : w = 0 then 0
        else a (edgeAdd q w hw) * (f (q + w) - f q) * jumpKernel (physical 1 w) := by
  have hterm (w : Site d) :
      (if hw : w = 0 then 0 else a (edgeAdd q w hw) *
        (ε * f (q + w) - ε * f q) * jumpKernel (physical ε w)) =
      (ε * (ε ^ (d + 2))⁻¹) *
        (if hw : w = 0 then 0 else a (edgeAdd q w hw) *
          (f (q + w) - f q) * jumpKernel (physical 1 w)) := by
    split
    · simp only [mul_zero]
    · rw [jumpKernel_physical_scaling hε]
      ring
  unfold generator
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hcoeff : ε ^ d / kappa d ε * (ε * (ε ^ (d + 2))⁻¹) =
      (ε * kappa d ε)⁻¹ := by
    rw [pow_add]
    by_cases hk : kappa d ε = 0
    · simp only [hk, div_zero, mul_zero, zero_mul, inv_zero]
    · field_simp [hε.ne', hk]
  rw [← mul_assoc, hcoeff]

/-- The affine corrector equation is equivalent to its spacing-free microscopic equation. -/
theorem generator_affine_microscopic_zero_iff (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (Ψ : Site d → ℝ) (q : Site d) :
    generator ε a (fun x => linearFn ε p x + ε * Ψ x) q = 0 ↔
      (∑' w : Site d, if hw : w = 0 then 0 else a (edgeAdd q w hw) *
        (linearFn 1 p w + Ψ (q + w) - Ψ q) * jumpKernel (physical 1 w)) = 0 := by
  have heq : (fun x => linearFn ε p x + ε * Ψ x) =
      (fun x => ε * (linearFn 1 p x + Ψ x)) := by
    funext x
    rw [linearFn_scaling, mul_add]
  rw [heq, generator_microscopic hε.1,
    mul_eq_zero_iff_left (inv_ne_zero (mul_ne_zero hε.1.ne' (kappa_pos hd hε).ne'))]
  have hinc (w : Site d) :
      (linearFn 1 p (q + w) + Ψ (q + w)) - (linearFn 1 p q + Ψ q) =
        linearFn 1 p w + Ψ (q + w) - Ψ q := by
    rw [linearFn_add]
    ring
  simp_rw [hinc]

/-- Correctors on the same integer cube have identical microscopic rescalings. -/
theorem corrector_cube_rescaling (hd : 1 ≤ d) {ε ε' lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) (n : ℕ)
    {φ ψ : Site d → ℝ}
    (hφ : SupportedIn ε (cube ε n) φ)
    (hφeq : ∀ q ∈ latticeSet ε (cube ε n),
      generator ε a (fun x => linearFn ε p x + φ x) q = 0)
    (hψ : SupportedIn ε' (cube ε' n) ψ)
    (hψeq : ∀ q ∈ latticeSet ε' (cube ε' n),
      generator ε' a (fun x => linearFn ε' p x + ψ x) q = 0) :
    ε'⁻¹ • ψ = ε⁻¹ • φ := by
  let Ψ : Site d → ℝ := fun q => ε'⁻¹ * ψ q
  have hrecover : (fun q => ε' * Ψ q) = ψ := by
    funext q
    dsimp only [Ψ]
    rw [← mul_assoc, mul_inv_cancel₀ hε'.1.ne', one_mul]
  have hs : SupportedIn ε (cube ε n) (fun q => ε * Ψ q) := by
    intro q hq
    have hq' : q ∉ latticeSet ε' (cube ε' n) := by
      rwa [latticeSet_cube hε'.1, ← latticeSet_cube hε.1]
    dsimp only [Ψ]
    rw [hψ q hq', mul_zero, mul_zero]
  have heq : ∀ q ∈ latticeSet ε (cube ε n),
      generator ε a (fun x => linearFn ε p x + ε * Ψ x) q = 0 := by
    intro q hq
    apply (generator_affine_microscopic_zero_iff hd hε a p Ψ q).mpr
    apply (generator_affine_microscopic_zero_iff hd hε' a p Ψ q).mp
    have hq' : q ∈ latticeSet ε' (cube ε' n) := by
      rwa [latticeSet_cube hε'.1, ← latticeSet_cube hε.1]
    simpa only [show (fun x => linearFn ε' p x + ε' * Ψ x) =
      (fun x => linearFn ε' p x + ψ x) from
        congrArg (fun f : Site d → ℝ => fun x => linearFn ε' p x + f x) hrecover]
      using hψeq q hq'
  have hminφ := (isCorrectorMinimizer_iff hd hε (cube_isBounded ε n)
    hlam ha p hφ).mpr hφeq
  have hminΨ := (isCorrectorMinimizer_iff hd hε (cube_isBounded ε n)
    hlam ha p hs).mpr heq
  have hu := existsUnique_correctorMinimizer hd hε (cube_isBounded ε n) hlam ha p
  have hsame : (fun q => ε * Ψ q) = φ := hu.unique ⟨hs, hminΨ⟩ ⟨hφ, hminφ⟩
  funext q
  change Ψ q = ε⁻¹ * φ q
  rw [← congrFun hsame q, ← mul_assoc, inv_mul_cancel₀ hε.1.ne', one_mul]

/-- The discrete squared `L²` norm has the microscopic prefactor `ε^(d+2)`. -/
theorem l2NormSq_cube_scaling {ε : ℝ} (hε : 0 < ε) (n : ℕ) (Ψ : Site d → ℝ) :
    l2NormSq ε (cube ε n) (fun q => ε * Ψ q) =
      ε ^ (d + 2) * ∑' q : integerBox d n, Ψ q ^ 2 := by
  unfold l2NormSq
  rw [latticeSet_cube hε]
  simp_rw [mul_pow]
  rw [tsum_mul_left, ← mul_assoc, ← pow_add]

/-- The squared critical seminorm has the microscopic prefactor `ε^d / κ_ε`. -/
theorem h1CritSq_scaling {ε : ℝ} (hε : 0 < ε) (Ψ : Site d → ℝ) :
    h1CritSq ε (fun q => ε * Ψ q) = ε ^ d / kappa d ε *
      ∑' v : Site d × Site d, jumpKernel (physical 1 v.2) *
        (Ψ (v.1 + v.2) - Ψ v.1) ^ 2 := by
  have hterm (v : Site d × Site d) :
      jumpKernel (physical ε v.2) * (ε * Ψ (v.1 + v.2) - ε * Ψ v.1) ^ 2 =
      ((ε ^ (d + 2))⁻¹ * ε ^ 2) * (jumpKernel (physical 1 v.2) *
        (Ψ (v.1 + v.2) - Ψ v.1) ^ 2) := by
    rw [jumpKernel_physical_scaling hε]
    ring
  unfold h1CritSq
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hcoeff : ε ^ (2 * d) / kappa d ε * ((ε ^ (d + 2))⁻¹ * ε ^ 2) =
      ε ^ d / kappa d ε := by
    rw [pow_add, show 2 * d = d + d by omega, pow_add]
    by_cases hk : kappa d ε = 0
    · simp only [hk, div_zero, zero_mul]
    · field_simp [hε.ne', hk]
  rw [← mul_assoc, hcoeff]

/-- The microscopic sums converge for functions vanishing outside the integer box. -/
theorem microscopic_sums_summable (hd : 1 ≤ d) (n : ℕ) {Ψ : Site d → ℝ}
    (hΨ : ∀ q, q ∉ integerBox d n → Ψ q = 0) :
    Summable (fun q : integerBox d n => Ψ q ^ 2) ∧
      Summable (fun v : Site d × Site d => jumpKernel (physical 1 v.2) *
        (Ψ (v.1 + v.2) - Ψ v.1) ^ 2) := by
  have hf : (integerBox d n).Finite := by
    rw [← latticeSet_cube zero_lt_one]
    exact latticeSet_finite zero_lt_one (cube_isBounded 1 n)
  letI := hf.fintype
  have hs : SupportedIn 1 (cube 1 n) Ψ := by
    intro q hq
    exact hΨ q (by rwa [latticeSet_cube zero_lt_one] at hq)
  exact ⟨(hasSum_fintype _).summable,
    summable_h1CritSq hd zero_lt_one (hs.hasFiniteSupport zero_lt_one (cube_isBounded 1 n))⟩

/-- The microscopic corrector equation is absolutely convergent on box-supported data. -/
theorem summable_microscopic_corrector (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (p : Fin d → ℝ) (n : ℕ) {Ψ : Site d → ℝ}
    (hΨ : ∀ q, q ∉ integerBox d n → Ψ q = 0) (q : Site d) :
    Summable (fun w : Site d => if hw : w = 0 then 0 else a (edgeAdd q w hw) *
      ((linearFn 1 p (q + w) + Ψ (q + w)) - (linearFn 1 p q + Ψ q)) *
        jumpKernel (physical 1 w)) := by
  have hs : SupportedIn 1 (cube 1 n) Ψ := by
    intro x hx
    exact hΨ x (by rwa [latticeSet_cube zero_lt_one] at hx)
  exact summable_generator_affine hd zero_lt_one hlam ha p
    (exists_bound_of_finite_support
      (hs.hasFiniteSupport zero_lt_one (cube_isBounded 1 n))) q

/-- Comparable spacings have comparable normalizations, with a dimension-only multiplier. -/
theorem kappa_ratio_bound (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R → ∀ ε ε' : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 → ε ≤ R * ε' →
        kappa d ε' ≤ K * R * kappa d ε := by
  obtain ⟨C, hC, hupper⟩ := kappa_le d
  obtain ⟨c, hc, hlower⟩ := le_kappa hd
  refine ⟨C / c, div_pos hC hc, ?_⟩
  intro R hR ε ε' hε hε' hscale
  have hratio : ε / ε' ≤ R := (div_le_iff₀ hε'.1).mpr hscale
  have hlog := (Real.log_le_sub_one_of_pos (div_pos hε.1 hε'.1)).trans
    (sub_le_sub_right hratio 1)
  rw [Real.log_div hε.1.ne' hε'.1.ne'] at hlog
  have hlogε := (Real.log_neg hε.1 hε.2).le
  have hlogs : 1 + |Real.log ε'| ≤ R * (1 + |Real.log ε|) := by
    rw [abs_of_neg (Real.log_neg hε'.1 hε'.2), abs_of_nonpos hlogε]
    have hprod := mul_nonneg (sub_nonneg.mpr hR) (neg_nonneg.mpr hlogε)
    nlinarith only [hlog, hprod]
  calc
    kappa d ε' ≤ C * (1 + |Real.log ε'|) := hupper ε' hε'
    _ ≤ C * (R * (1 + |Real.log ε|)) := mul_le_mul_of_nonneg_left hlogs hC.le
    _ ≤ C * (R * (kappa d ε / c)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hR)
      exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlower ε hε)
    _ = C / c * R * kappa d ε := by ring

/-- The two microscopic norm prefactors vary uniformly under a bounded spacing ratio. -/
theorem microscopic_prefactors_comparable (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε ε' : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 → ε ≤ R * ε' →
        ε ^ (d + 2) ≤ A * ε' ^ (d + 2) ∧
        ε ^ d / kappa d ε ≤ A * (ε' ^ d / kappa d ε') := by
  obtain ⟨K, hK, hk⟩ := kappa_ratio_bound hd
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  refine ⟨R ^ (d + 2) + K * R ^ (d + 1), by positivity, ?_⟩
  intro ε ε' hε hε' hscale
  have hp (k : ℕ) : ε ^ k ≤ R ^ k * ε' ^ k := by
    simpa only [mul_pow] using pow_le_pow_left₀ hε.1.le hscale k
  constructor
  · exact (hp (d + 2)).trans (by
      have := mul_nonneg (mul_nonneg hK.le (pow_nonneg hRpos.le (d + 1)))
        (pow_nonneg hε'.1.le (d + 2))
      nlinarith only [this])
  · have hκ := hk R hR ε ε' hε hε' hscale
    have hprod := mul_le_mul (hp d) hκ (kappa_pos hd hε').le
      (mul_nonneg (pow_nonneg hRpos.le d) (pow_nonneg hε'.1.le d))
    have hbound : ε ^ d / kappa d ε ≤
        (K * R ^ (d + 1)) * (ε' ^ d / kappa d ε') := by
      apply (div_le_iff₀ (kappa_pos hd hε)).mpr
      apply (mul_le_mul_iff_left₀ (kappa_pos hd hε')).mp
      calc
        ε ^ d * kappa d ε' ≤ (R ^ d * ε' ^ d) * (K * R * kappa d ε) := hprod
        _ = K * R ^ (d + 1) * (ε' ^ d / kappa d ε') *
            kappa d ε * kappa d ε' := by
          rw [pow_succ]
          field_simp [(kappa_pos hd hε').ne']
    apply hbound.trans
    have hn := mul_nonneg (pow_nonneg hRpos.le (d + 2))
      (div_nonneg (pow_nonneg hε'.1.le d) (kappa_pos hd hε').le)
    nlinarith only [hn]

/-- A shared microscopic function gives uniform comparison of the combined squared norms. -/
theorem microscopic_norms_comparable (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε ε' : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 → ε ≤ R * ε' →
        ∀ (n : ℕ) (Ψ : Site d → ℝ),
          h1CritSq ε (fun q => ε * Ψ q) +
              l2NormSq ε (cube ε n) (fun q => ε * Ψ q) ≤
            A * (h1CritSq ε' (fun q => ε' * Ψ q) +
              l2NormSq ε' (cube ε' n) (fun q => ε' * Ψ q)) := by
  obtain ⟨A, hA, hbound⟩ := microscopic_prefactors_comparable hd hR
  refine ⟨A, hA, ?_⟩
  intro ε ε' hε hε' hscale n Ψ
  obtain ⟨hl, hh⟩ := hbound ε ε' hε hε' hscale
  rw [h1CritSq_scaling hε.1, h1CritSq_scaling hε'.1,
    l2NormSq_cube_scaling hε.1, l2NormSq_cube_scaling hε'.1]
  have hsumL : 0 ≤ ∑' q : integerBox d n, Ψ q ^ 2 := tsum_nonneg (fun q => sq_nonneg _)
  have hsumH : 0 ≤ ∑' v : Site d × Site d, jumpKernel (physical 1 v.2) *
      (Ψ (v.1 + v.2) - Ψ v.1) ^ 2 :=
    tsum_nonneg (fun v => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _))
  calc
    _ ≤ (A * (ε' ^ d / kappa d ε')) *
          (∑' v : Site d × Site d, jumpKernel (physical 1 v.2) *
            (Ψ (v.1 + v.2) - Ψ v.1) ^ 2) +
        (A * ε' ^ (d + 2)) * (∑' q : integerBox d n, Ψ q ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hh hsumH)
        (mul_le_mul_of_nonneg_right hl hsumL)
    _ = _ := by ring

/-- Corrector norms are uniformly comparable for a bounded ratio of positive spacings. -/
theorem corrector_cube_norms_comparable (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε ε' : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 → ε ≤ R * ε' →
        ∀ (lam : ℝ), 0 < lam → ∀ a : Edge d → ℝ,
          (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (p : Fin d → ℝ) (n : ℕ)
            (φ ψ : Site d → ℝ),
          SupportedIn ε (cube ε n) φ →
          (∀ q ∈ latticeSet ε (cube ε n),
            generator ε a (fun x => linearFn ε p x + φ x) q = 0) →
          SupportedIn ε' (cube ε' n) ψ →
          (∀ q ∈ latticeSet ε' (cube ε' n),
            generator ε' a (fun x => linearFn ε' p x + ψ x) q = 0) →
          h1CritSq ε φ + l2NormSq ε (cube ε n) φ ≤
            A * (h1CritSq ε' ψ + l2NormSq ε' (cube ε' n) ψ) := by
  obtain ⟨A, hA, hbound⟩ := microscopic_norms_comparable hd hR
  refine ⟨A, hA, ?_⟩
  intro ε ε' hε hε' hscale lam hlam a ha p n φ ψ hφ hφeq hψ hψeq
  have heq := corrector_cube_rescaling hd hε hε' hlam ha p n hφ hφeq hψ hψeq
  let Ψ : Site d → ℝ := ε⁻¹ • φ
  have hφrecover : (fun q => ε * Ψ q) = φ := by
    funext q
    change ε * (ε⁻¹ * φ q) = φ q
    rw [← mul_assoc, mul_inv_cancel₀ hε.1.ne', one_mul]
  have hψrecover : (fun q => ε' * Ψ q) = ψ := by
    funext q
    change ε' * (ε⁻¹ * φ q) = ψ q
    have hpoint : ε'⁻¹ * ψ q = ε⁻¹ * φ q := congrFun heq q
    rw [← hpoint]
    change ε' * (ε'⁻¹ * ψ q) = ψ q
    rw [← mul_assoc, mul_inv_cancel₀ hε'.1.ne', one_mul]
  have h := hbound ε ε' hε hε' hscale n Ψ
  rwa [hφrecover, hψrecover] at h

/-- Spacings in one block have ratio at most `C / c`, independently of the block index. -/
theorem spacing_ratio_of_block {c C ε ε' : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (m : ℕ)
    (hε : ε ≤ C * (3 : ℝ) ^ (-(m : ℤ)))
    (hε' : c * (3 : ℝ) ^ (-(m : ℤ)) ≤ ε') : ε ≤ (C / c) * ε' := by
  calc
    ε ≤ C * (3 : ℝ) ^ (-(m : ℤ)) := hε
    _ = (C / c) * (c * (3 : ℝ) ^ (-(m : ℤ))) := by field_simp
    _ ≤ (C / c) * ε' := mul_le_mul_of_nonneg_left hε' (div_nonneg hC hc.le)

/-- Corrector norms in a logarithmic block are comparable with a constant depending
only on `c`, `C`, and the dimension. -/
theorem corrector_cube_block_norms_comparable (hd : 1 ≤ d) {c C : ℝ}
    (hc : 0 < c) (hcC : c ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (ε ε' : ℝ),
      ε ∈ Set.Ioo (0 : ℝ) 1 → ε' ∈ Set.Ioo (0 : ℝ) 1 →
      ε ∈ Set.Icc (c * (3 : ℝ) ^ (-(m : ℤ))) (C * (3 : ℝ) ^ (-(m : ℤ))) →
      ε' ∈ Set.Icc (c * (3 : ℝ) ^ (-(m : ℤ))) (C * (3 : ℝ) ^ (-(m : ℤ))) →
        ∀ (lam : ℝ), 0 < lam → ∀ a : Edge d → ℝ,
          (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (p : Fin d → ℝ) (n : ℕ)
            (φ ψ : Site d → ℝ),
          SupportedIn ε (cube ε n) φ →
          (∀ q ∈ latticeSet ε (cube ε n),
            generator ε a (fun x => linearFn ε p x + φ x) q = 0) →
          SupportedIn ε' (cube ε' n) ψ →
          (∀ q ∈ latticeSet ε' (cube ε' n),
            generator ε' a (fun x => linearFn ε' p x + ψ x) q = 0) →
          h1CritSq ε φ + l2NormSq ε (cube ε n) φ ≤
            A * (h1CritSq ε' ψ + l2NormSq ε' (cube ε' n) ψ) := by
  have hR : 1 ≤ C / c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hcC)
  obtain ⟨A, hA, hbound⟩ := corrector_cube_norms_comparable hd hR
  refine ⟨A, hA, ?_⟩
  intro m ε ε' hε hε' hblock hblock'
  exact hbound ε ε' hε hε'
    (spacing_ratio_of_block hc (hc.le.trans hcC) m hblock.2 hblock'.1)

end

end LongRange
