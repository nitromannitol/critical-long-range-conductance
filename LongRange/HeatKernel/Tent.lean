import LongRange.HeatKernel.UnitWalk
import LatticeProb.External.ChenKimKumagaiWang
import LongRange.Appendix.LatticeSums

/-!
# Truncated rates and Euclidean tents

Truncating the unit walk preserves its uniformization clock. The radial tent has finite
support and its Lipschitz constant is its slope, measured with the Euclidean radius.
The squared Davies functional is bounded by the slope squared, an exponential factor,
and a critical logarithmic shell sum.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Truncate jumps at radius `ρ`, keeping the original uniformization clock. -/
def truncRates (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (ρ : ℝ) :
    JumpChain.BoundedRates (Site d) := by
  classical
  let rates := unitRates hd hlam a ha
  let q := fun x y => if radius (physical 1 (y - x)) ≤ ρ then unitRate a x y else 0
  have hn : ∀ x y, 0 ≤ q x y := by
    intro x y
    dsimp [q]
    split_ifs
    · exact unitRate_nonneg hlam ha x y
    · exact le_rfl
  have hle : ∀ x y, q x y ≤ rates.q x y := by
    intro x y
    dsimp [q, rates, unitRates]
    split_ifs
    · exact le_rfl
    · exact unitRate_nonneg hlam ha x y
  have hs : ∀ x, Summable (q x) := fun x =>
    (rates.summable x).of_nonneg_of_le (hn x) (hle x)
  exact {
    q := q
    q_nonneg := hn
    q_self := fun x => by simp [q, unitRate]
    summable := hs
    R := rates.R
    R_pos := rates.R_pos
    total_le := fun x => ((hs x).tsum_le_tsum (hle x) (rates.summable x)).trans
      (rates.total_le x) }

/-- Truncation keeps exactly the unit walk's uniformization rate. -/
theorem truncRates_R (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (ρ : ℝ) :
    (truncRates hd hlam a ha ρ).R = (unitRates hd hlam a ha).R := rfl

/-- Truncation only decreases the unit rates. -/
theorem truncRates_q_le (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (ρ : ℝ)
    (x y : Site d) : (truncRates hd hlam a ha ρ).q x y ≤ unitRate a x y := by
  classical
  change (if radius (physical 1 (y - x)) ≤ ρ then unitRate a x y else 0) ≤ _
  split_ifs
  · exact le_rfl
  · exact unitRate_nonneg hlam ha x y

/-- Euclidean truncation preserves symmetry. -/
theorem truncRates_symm (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (ρ : ℝ)
    (x y : Site d) : (truncRates hd hlam a ha ρ).q x y =
      (truncRates hd hlam a ha ρ).q y x := by
  classical
  change (if radius (physical 1 (y - x)) ≤ ρ then unitRate a x y else 0) =
    (if radius (physical 1 (x - y)) ≤ ρ then unitRate a y x else 0)
  have hr : radius (physical 1 (x - y)) = radius (physical 1 (y - x)) := by
    rw [show x - y = -(y - x) by abel, physical_neg]
    simp only [radius, Pi.neg_apply, neg_sq]
  rw [hr, unitRate_symm a x y]

/-- The Euclidean radial tent with peak radius `r` and slope `s`. -/
def tent (x : Site d) (r s : ℝ) (z : Site d) : ℝ :=
  s * max 0 (r - |radius (physical 1 (z - x)) - r|)

/-- The tent vanishes at its center. -/
theorem tent_center (x : Site d) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    tent x r s x = 0 := by
  simp [tent, physical, radius, abs_of_nonneg hr]

/-- The tent takes its peak value at any point of radius `r`. -/
theorem tent_peak (x y : Site d) (s : ℝ) :
    tent x (radius (physical 1 (y - x))) s y =
      s * radius (physical 1 (y - x)) := by
  simp only [tent, sub_self, abs_zero, sub_zero, max_eq_right (radius_nonneg _)]

/-- The tent vanishes outside the open ball of radius `2r`. -/
theorem tent_eq_zero_of_radius_ge (x z : Site d) (r s : ℝ)
    (hz : 2 * r ≤ radius (physical 1 (z - x))) : tent x r s z = 0 := by
  have hab := le_abs_self (radius (physical 1 (z - x)) - r)
  have h : r - |radius (physical 1 (z - x)) - r| ≤ 0 := by linarith
  rw [tent, max_eq_left h, mul_zero]

/-- The support lies in the open Euclidean ball of radius `2r` about its center. -/
theorem tent_support_subset (x : Site d) (r s : ℝ) :
    Function.support (tent x r s) ⊆
      {z | radius (physical 1 (z - x)) < 2 * r} := by
  intro z hz
  change radius (physical 1 (z - x)) < 2 * r
  by_contra! h
  exact hz (tent_eq_zero_of_radius_ge x z r s h)

/-- The radial tent has finite support. -/
theorem tent_hasFiniteSupport (x : Site d) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (Function.support (tent x r s)).Finite := by
  have hε : 0 < (2 * r)⁻¹ := inv_pos.mpr (by linarith)
  apply ((Finset.finite_toSet (cutoffBox d ((2 * r)⁻¹))).preimage
    (Equiv.subRight x).injective.injOn).subset
  intro z hz
  apply cutoff_mem_box hε
  rw [radius_physical_eq_mul hε.le]
  have hb : radius (physical 1 (z - x)) < 2 * r := by
    by_contra! h
    exact hz (tent_eq_zero_of_radius_ge x z r s h)
  exact (inv_mul_le_one₀ (by linarith : 0 < 2 * r)).mpr hb.le

/-- The tent is Lipschitz with slope `s` for the Euclidean lattice metric. -/
theorem tent_lipschitz (x : Site d) (r : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (z w : Site d) : |tent x r s z - tent x r s w| ≤
      s * radius (physical 1 (w - z)) := by
  have hm := abs_max_sub_max_le_max (0 : ℝ)
    (r - |radius (physical 1 (z - x)) - r|) 0
    (r - |radius (physical 1 (w - x)) - r|)
  have ha := abs_abs_sub_abs_le_abs_sub
    (radius (physical 1 (z - x)) - r) (radius (physical 1 (w - x)) - r)
  have hdif := radius_difference (physical 1 (w - x)) (physical 1 (z - x))
  have he : physical 1 (w - x) - physical 1 (z - x) = physical 1 (w - z) := by
    ext k
    simp only [physical, one_mul, Pi.sub_apply, Int.cast_sub]
    ring
  rw [he, abs_sub_comm] at hdif
  have hinner : |(r - |radius (physical 1 (z - x)) - r|) -
      (r - |radius (physical 1 (w - x)) - r|)| ≤
      radius (physical 1 (w - z)) := by
    rw [show (r - |radius (physical 1 (z - x)) - r|) -
      (r - |radius (physical 1 (w - x)) - r|) =
      -(|radius (physical 1 (z - x)) - r| -
        |radius (physical 1 (w - x)) - r|) by ring, abs_neg]
    exact (ha.trans (by simpa only [sub_sub_sub_cancel_right] using hdif))
  have hzero : |(0 : ℝ) - 0| ≤ radius (physical 1 (w - z)) := by
    simpa only [sub_self, abs_zero] using (radius_nonneg (physical 1 (w - z)))
  have hmax := hm.trans (max_le hzero hinner)
  simpa only [tent, ← mul_sub, abs_mul, abs_of_nonneg hs] using
    mul_le_mul_of_nonneg_left hmax hs

/-- Critical Euclidean shell sums have logarithmic growth, including radius one. -/
theorem tent_shell_sum_le (hd : 1 ≤ d) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∑ u ∈ unitBallIndices d ρ⁻¹, radius (physical 1 u) ^ (-(d : ℝ)) ≤
      Euclidean.Shell.shellConstant d * (1 + Real.log ρ) := by
  have hp : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hsum := Euclidean.Estimates.unitBallIndices_rpow_sum_le hd
    (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (inv_pos.mpr hp)
  rw [one_div, inv_inv, show (d : ℝ) - 1 - d = -1 by ring] at hsum
  have hf : 1 ≤ ⌊ρ⌋₊ := (Nat.one_le_floor_iff _).mpr hρ
  have hlog : Real.log (⌊ρ⌋₊ : ℝ) ≤ Real.log ρ :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hf))
      (Nat.floor_le hp.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left
    ((Euclidean.Series.sum_inv_Icc_le_one_add_log ⌊ρ⌋₊).trans (by linarith))
    (Euclidean.Shell.shellConstant_pos hd).le)

/-- The exponential increment is bounded by its argument times the maximal derivative. -/
theorem tent_exp_increment_le (b : ℝ) :
    |Real.exp b - 1| ≤ |b| * Real.exp |b| := by
  have hlower := Real.add_one_le_exp b
  have hupper := Real.add_one_le_exp (-b)
  have hm := mul_le_mul_of_nonneg_right hupper (Real.exp_pos b).le
  rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hm
  by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg hb, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hb))]
    linarith
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [abs_of_nonpos hb', abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hb'))]
    have he : 1 ≤ Real.exp (-b) := Real.one_le_exp (neg_nonneg.mpr hb')
    have hm' := mul_le_mul_of_nonneg_left he (neg_nonneg.mpr hb')
    linarith

/-- Squaring the exponential increment gives the Davies row estimate. -/
theorem tent_exp_increment_sq_le (b : ℝ) :
    (Real.exp b - 1) ^ 2 ≤ b ^ 2 * Real.exp (2 * |b|) := by
  have h := sq_le_sq₀ (abs_nonneg (Real.exp b - 1))
    (mul_nonneg (abs_nonneg b) (Real.exp_pos |b|).le)
  have he : Real.exp (2 * |b|) = Real.exp |b| ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [he, ← sq_abs b, ← mul_pow]
  exact (sq_abs (Real.exp b - 1)).symm.trans_le (h.mpr (tent_exp_increment_le b))

/-- Cancellation of the quadratic increment against the jump kernel. -/
lemma tent_kernel_quadratic {t : ℝ} (ht : 0 < t) :
    (t ^ (d + 2))⁻¹ * t ^ 2 = t ^ (-(d : ℝ)) := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast, pow_add]
  field_simp [ne_of_gt ht]

/-- A single truncated Davies summand is controlled by the critical radial kernel. -/
lemma tent_davies_summand_le (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ s : ℝ} (hρ : 1 ≤ ρ) (hs : 0 ≤ s) (z w : Site d) (b : ℝ)
    (hb : |b| ≤ s * radius (physical 1 (w - z))) :
    (1 / 2 : ℝ) * (truncRates hd hlam a ha ρ).q z w * (Real.exp b - 1) ^ 2 ≤
      if w - z ∈ unitBallIndices d ρ⁻¹ then
        ((1 / 2 : ℝ) * lam⁻¹ * s ^ 2 * Real.exp (2 * s * ρ)) *
          radius (physical 1 (w - z)) ^ (-(d : ℝ)) else 0 := by
  classical
  have hp : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  by_cases hn : w - z = 0
  · have hw : w = z := sub_eq_zero.mp hn
    subst w
    rw [(truncRates hd hlam a ha ρ).q_self]
    simp only [mul_zero, zero_mul, sub_self]
    rw [if_neg (by simp [unitBallIndices])]
  by_cases ht : radius (physical 1 (w - z)) ≤ ρ
  · have hmem : w - z ∈ unitBallIndices d ρ⁻¹ := by
      rw [mem_unitBallIndices (inv_pos.mpr hp), radius_physical_eq_mul (inv_nonneg.mpr hp.le)]
      exact ⟨hn, (inv_mul_le_one₀ hp).mpr ht⟩
    rw [if_pos hmem]
    have hr := radius_pos ((physical_eq_zero_iff zero_lt_one _).not.mpr hn)
    have hq := unitRate_le hlam ha z w
    rw [jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one _).not.mpr hn)] at hq
    have hexp : Real.exp (2 * |b|) ≤ Real.exp (2 * s * ρ) := by
      apply Real.exp_le_exp.mpr
      have := hb.trans (mul_le_mul_of_nonneg_left ht hs)
      linarith
    have hsquare : b ^ 2 ≤ s ^ 2 * radius (physical 1 (w - z)) ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg b)
        (mul_nonneg hs hr.le)).mpr hb
      simpa only [sq_abs, mul_pow] using h
    have hi := (tent_exp_increment_sq_le b).trans
      (mul_le_mul hsquare hexp (Real.exp_pos _).le
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hrate : (truncRates hd hlam a ha ρ).q z w ≤
        lam⁻¹ * (radius (physical 1 (w - z)) ^ (d + 2))⁻¹ :=
      (truncRates_q_le hd hlam a ha ρ z w).trans hq
    have hprod := mul_le_mul hrate hi (sq_nonneg (Real.exp b - 1))
      (mul_nonneg (inv_nonneg.mpr hlam.le) (inv_nonneg.mpr (pow_nonneg hr.le _)))
    have hhalf := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      _ ≤ (1 / 2 : ℝ) * (lam⁻¹ *
          (radius (physical 1 (w - z)) ^ (d + 2))⁻¹ *
          (s ^ 2 * radius (physical 1 (w - z)) ^ 2 * Real.exp (2 * s * ρ))) := by
        simpa only [mul_assoc] using hhalf
      _ = _ := by
        rw [← tent_kernel_quadratic hr]
        ring
  · have hq : (truncRates hd hlam a ha ρ).q z w = 0 := by
      change (if radius (physical 1 (w - z)) ≤ ρ then _ else 0) = 0
      rw [if_neg ht]
    rw [hq, mul_zero, zero_mul]
    split_ifs
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (radius_nonneg _) _)
    · exact le_rfl

/-- Summing the pointwise estimate gives a uniform bound for either orientation. -/
lemma tent_davies_row_le (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {ρ s : ℝ} (hρ : 1 ≤ ρ) (hs : 0 ≤ s) (z : Site d) (b : Site d → ℝ)
    (hb : ∀ w, |b w| ≤ s * radius (physical 1 (w - z))) :
    (∑' w, ENNReal.ofReal ((1 / 2 : ℝ) * (truncRates hd hlam a ha ρ).q z w *
      (Real.exp (b w) - 1) ^ 2)) ≤
      ENNReal.ofReal (((1 / 2 : ℝ) * lam⁻¹ * s ^ 2 * Real.exp (2 * s * ρ)) *
        (Euclidean.Shell.shellConstant d * (1 + Real.log ρ))) := by
  classical
  let K := (1 / 2 : ℝ) * lam⁻¹ * s ^ 2 * Real.exp (2 * s * ρ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hterm (w : Site d) := ENNReal.ofReal_le_ofReal
    (tent_davies_summand_le hd hlam a ha hρ hs z w (b w) (hb w))
  apply (ENNReal.tsum_le_tsum hterm).trans
  have he := (Equiv.addLeft z).tsum_eq (fun w : Site d => ENNReal.ofReal
    (if w - z ∈ unitBallIndices d ρ⁻¹ then
      K * radius (physical 1 (w - z)) ^ (-(d : ℝ)) else 0))
  simp only [Equiv.coe_addLeft, add_sub_cancel_left] at he
  rw [← he]
  simp only [apply_ite, ENNReal.ofReal_zero]
  have hfinite : (∑' u : Site d, if u ∈ unitBallIndices d ρ⁻¹ then
      ENNReal.ofReal (K * radius (physical 1 u) ^ (-(d : ℝ))) else 0) =
      ∑ u ∈ unitBallIndices d ρ⁻¹,
        ENNReal.ofReal (K * radius (physical 1 u) ^ (-(d : ℝ))) := by
    rw [tsum_eq_sum (s := unitBallIndices d ρ⁻¹) (fun u hu => if_neg hu)]
    exact Finset.sum_congr rfl (fun u hu => if_pos hu)
  rw [hfinite]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ =>
    mul_nonneg hK (Real.rpow_nonneg (radius_nonneg _) _)), ← Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (tent_shell_sum_le hd hρ) hK)

/-- The tent Davies functional has a logarithmic bound with a constant fixed before the tent. -/
theorem tent_ckkwLambdaSq_le (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a : Edge d → ℝ)
      (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) (r : ℝ)
      (s : ℝ), 0 ≤ s → ∀ ρ : ℝ, 1 ≤ ρ →
      External.ckkwLambdaSq (truncRates hd hlam a ha ρ) (tent x r s) ≤
        ENNReal.ofReal (B * s ^ 2 * Real.exp (2 * s * ρ) * (1 + Real.log ρ)) := by
  refine ⟨(1 / 2 : ℝ) * lam⁻¹ * Euclidean.Shell.shellConstant d,
    mul_pos (mul_pos (by norm_num) (inv_pos.mpr hlam))
      (Euclidean.Shell.shellConstant_pos hd), ?_⟩
  intro a ha x r s hs ρ hρ
  unfold External.ckkwLambdaSq
  apply max_le
  · apply iSup_le
    intro z
    have h := tent_davies_row_le hd hlam a ha hρ hs z
      (fun w => tent x r s w - tent x r s z) (fun w => by
        rw [abs_sub_comm]
        exact tent_lipschitz x r hs z w)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · apply iSup_le
    intro z
    have h := tent_davies_row_le hd hlam a ha hρ hs z
      (fun w => tent x r s z - tent x r s w) (tent_lipschitz x r hs z)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- The functional bound supplies the finiteness hypothesis of the Davies input. -/
theorem tent_ckkwLambdaSq_ne_top (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (x : Site d) (r : ℝ) {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 1 ≤ ρ) :
    External.ckkwLambdaSq (truncRates hd hlam a ha ρ) (tent x r s) ≠ ⊤ := by
  obtain ⟨_, _, hbound⟩ := tent_ckkwLambdaSq_le hd hlam
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound a ha x r s hs ρ hρ)

/-- A unit tent on the one-dimensional lattice is nonzero at its peak. -/
theorem tent_one_dim_peak : tent (0 : Site 1) 1 1 (fun _ => 1) = 1 := by
  norm_num [tent, physical, radius, Fin.sum_univ_one]

/-- The functional bound applies to a genuine unit tent and unit conductances. -/
theorem tent_one_dim_functional_bound :
    ∃ B : ℝ, 0 < B ∧
      External.ckkwLambdaSq
        (truncRates (d := 1) (by norm_num) (lam := 1) (by norm_num)
          (fun _ => 1) (by intro _; norm_num) 1) (tent 0 1 1) ≤
        ENNReal.ofReal (B * Real.exp 2) := by
  obtain ⟨B, hB, hbound⟩ := tent_ckkwLambdaSq_le (d := 1) (by norm_num)
    (lam := 1) (by norm_num)
  refine ⟨B, hB, ?_⟩
  simpa only [one_pow, mul_one, one_mul, Real.log_one, add_zero] using
    hbound (fun _ => 1) (by intro _; norm_num) 0 1 1 (by norm_num) 1 (by norm_num)

end

end LongRange
