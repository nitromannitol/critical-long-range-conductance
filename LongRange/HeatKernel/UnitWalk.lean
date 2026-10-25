import LongRange.Walk.Rates
import LatticeProb.Graph.LongRangeKernel.Lattice
import LatticeProb.Graph.LongRangeKernel.CriticalScale

/-!
# The unit-scale walk and lazy uniformization

The Euclidean jump rates at unit scale admit a uniform row bound. Doubling this bound
produces a symmetric Markov density with holding probability at least one half.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Graph.LongRangeKernel

noncomputable section

variable {d : ℕ}

/-- The unit-scale generator rate, with zero diagonal and Euclidean jump kernel. -/
def unitRate (a : Edge d → ℝ) (x y : Site d) : ℝ :=
  if h : y - x = 0 then 0 else
    a (edgeAdd x (y - x) h) * jumpKernel (physical 1 (y - x))

/-- Unordered conductances and the even Euclidean kernel give symmetric unit rates. -/
theorem unitRate_symm (a : Edge d → ℝ) (x y : Site d) :
    unitRate a x y = unitRate a y x := by
  by_cases hxy : y - x = 0
  · have hy : y = x := sub_eq_zero.mp hxy
    subst y
    simp only [unitRate, sub_self, dite_true]
  · have hneg : x - y = -(y - x) := by abel
    have hedge := edgeAdd_reverse x (y - x) hxy
    rw [add_sub_cancel] at hedge
    simp only [unitRate, hxy, hneg, neg_ne_zero.mpr hxy, dite_false,
      physical_neg, jumpKernel_neg, hedge]

/-- Physical homogeneity identifies the rescaled generator with a scalar multiple. -/
theorem walkRate_eq_smul_unitRate {ε : ℝ} (hε : 0 < ε)
    (a : Edge d → ℝ) (x y : Site d) :
    walkRate ε a x y = ε ^ d / kappa d ε * (ε ^ (d + 2))⁻¹ * unitRate a x y := by
  unfold walkRate unitRate
  split
  · ring
  · rename_i h
    rw [jumpKernel_physical hε h,
      jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one _).not.mpr h)]
    ring

/-- Ellipticity makes the unit rates nonnegative. -/
theorem unitRate_nonneg {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) : 0 ≤ unitRate a x y := by
  unfold unitRate
  split
  · exact le_rfl
  · exact mul_nonneg (hlam.le.trans (ha _).1) (jumpKernel_nonneg _)

/-- The upper ellipticity bound dominates each unit rate by a translated kernel. -/
theorem unitRate_le {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) :
    unitRate a x y ≤ lam⁻¹ * jumpKernel (physical 1 (y - x)) := by
  unfold unitRate
  split
  · exact mul_nonneg (inv_nonneg.mpr hlam.le) (jumpKernel_nonneg _)
  · exact mul_le_mul_of_nonneg_right (ha _).2 (jumpKernel_nonneg _)

/-- The positive-dimensional unit kernel has strictly positive total mass. -/
theorem unitKernel_tsum_pos (hd : 1 ≤ d) :
    0 < ∑' w : Site d, jumpKernel (physical 1 w) := by
  classical
  let i : Fin d := ⟨0, hd⟩
  let q : Site d := Pi.single i 1
  have hq : q ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp only [q, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hi
  have hp : 0 < jumpKernel (physical 1 q) := by
    rw [jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one q).not.mpr hq)]
    exact inv_pos.mpr (pow_pos (radius_pos
      ((physical_eq_zero_iff zero_lt_one q).not.mpr hq)) _)
  exact hp.trans_le ((summable_jumpKernel hd zero_lt_one).le_tsum q
    (fun w _ => jumpKernel_nonneg (physical 1 w)))

/-- Unit rates have summable rows bounded by the ellipticity-weighted kernel mass. -/
theorem unitRate_summable_bound (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) :
    Summable (unitRate a x) ∧
      ∑' y, unitRate a x y ≤ lam⁻¹ * ∑' w : Site d, jumpKernel (physical 1 w) := by
  have hdom : Summable (fun y : Site d => lam⁻¹ * jumpKernel (physical 1 (y - x))) := by
    apply (Equiv.summable_iff (Equiv.addLeft x)).mp
    simpa only [Function.comp_def, Equiv.coe_addLeft, add_sub_cancel_left] using
      (summable_jumpKernel hd zero_lt_one).mul_left lam⁻¹
  have hs := hdom.of_nonneg_of_le (unitRate_nonneg hlam ha x) (unitRate_le hlam ha x)
  refine ⟨hs, ?_⟩
  have ht := (Equiv.addLeft x).tsum_eq
    (fun y : Site d => lam⁻¹ * jumpKernel (physical 1 (y - x)))
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, tsum_mul_left] at ht
  have hb := hs.tsum_le_tsum (unitRate_le hlam ha x) hdom
  rw [tsum_mul_left, ← ht] at hb
  exact hb

/-- Doubling the uniform outgoing bound gives a positive uniformization clock. -/
def unitRates (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    LatticeProb.JumpChain.BoundedRates (Site d) where
  q := unitRate a
  q_nonneg := unitRate_nonneg hlam ha
  q_self x := by simp only [unitRate, sub_self, dite_true]
  summable x := (unitRate_summable_bound hd hlam a ha x).1
  R := 2 * (lam⁻¹ * ∑' w : Site d, jumpKernel (physical 1 w))
  R_pos := mul_pos (by norm_num) (mul_pos (inv_pos.mpr hlam) (unitKernel_tsum_pos hd))
  total_le x := (unitRate_summable_bound hd hlam a ha x).2.trans
    (by have h := mul_pos (inv_pos.mpr hlam) (unitKernel_tsum_pos hd); linarith)

/-- Uniformization is symmetric, including its holding entries. -/
theorem unitRates_p_symm (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) :
    (unitRates hd hlam a ha).p x y = (unitRates hd hlam a ha).p y x := by
  classical
  by_cases h : y = x
  · subst y
    rfl
  · simp only [JumpChain.BoundedRates.p, h, Ne.symm h, ite_false]
    change unitRate a x y / _ = unitRate a y x / _
    rw [unitRate_symm]

/-- The doubled clock leaves at least one half of the mass on the diagonal. -/
theorem unitRates_p_self_ge_half (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x : Site d) :
    1 / 2 ≤ (unitRates hd hlam a ha).p x x := by
  classical
  have hb := (unitRate_summable_bound hd hlam a ha x).2
  have hr := (unitRates hd hlam a ha).R_pos
  rw [JumpChain.BoundedRates.p, if_pos rfl]
  have hdiv : (∑' y, (unitRates hd hlam a ha).q x y) /
      (unitRates hd hlam a ha).R ≤ 1 / 2 := by
    apply (div_le_iff₀ hr).mpr
    change (∑' y, unitRate a x y) ≤
      1 / 2 * (2 * (lam⁻¹ * ∑' w : Site d, jumpKernel (physical 1 w)))
    nlinarith only [hb]
  linarith

/-- The uniformized density is Markov for counting measure. -/
theorem unitRates_isMarkovDensity (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    IsMarkovDensity (fun _ => 1)
      (fun x y => ENNReal.ofReal ((unitRates hd hlam a ha).p x y)) := by
  intro x
  simp only [ENNReal.coe_one, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg ((unitRates hd hlam a ha).p_nonneg x)
    ((unitRates hd hlam a ha).hasSum_p x).summable,
    ((unitRates hd hlam a ha).hasSum_p x).tsum_eq]
  exact ENNReal.ofReal_one

/-- The integer graph norm is the sum of the absolute physical unit coordinates. -/
theorem graphNorm_eq_sum_abs_physical (w : Site d) :
    (graphNorm w : ℝ) = ∑ i, |physical 1 w i| := by
  simp only [graphNorm, Nat.cast_sum, physical, one_mul, Nat.cast_natAbs,
    Int.cast_abs]

/-- The Euclidean radius and graph norm are comparable without changing the carrier. -/
theorem unit_radius_graphNorm (w : Site d) :
    radius (physical 1 w) ≤ (graphNorm w : ℝ) ∧
      (graphNorm w : ℝ) ≤ d * radius (physical 1 w) := by
  rw [graphNorm_eq_sum_abs_physical]
  constructor
  · have hs := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun i => |physical 1 w i|) (fun _ _ => abs_nonneg _)
    simp only [sq_abs] at hs
    have hr := radius_sq (physical 1 w)
    have hn := radius_nonneg (physical 1 w)
    have hsum : 0 ≤ ∑ i, |physical 1 w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    nlinarith only [hs, hr, hn, hsum]
  · calc
      (∑ i, |physical 1 w i|) ≤ ∑ _i : Fin d, radius (physical 1 w) :=
        Finset.sum_le_sum (fun i _ => abs_coord_le_radius _ i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- The polynomial MSC denominator is comparable to the Euclidean kernel off the diagonal. -/
theorem unitKernel_profile_bound (hd : 1 ≤ d) {w : Site d} (hw : w ≠ 0) :
    let D := latticeVolumeProfile d (graphNorm w) * quadraticScale (graphNorm w)
    1 / D ≤ jumpKernel (physical 1 w) ∧
      jumpKernel (physical 1 w) ≤ (2 * (d : ℝ)) ^ (d + 2) / D := by
  dsimp
  have hr := lattice_radius_ge_one hw
  have hcomp := unit_radius_graphNorm w
  have hn : (0 : ℝ) ≤ graphNorm w := Nat.cast_nonneg _
  have hrp : 0 < radius (physical 1 w) := lt_of_lt_of_le zero_lt_one hr
  have hD : 0 < (1 + (graphNorm w : ℝ)) ^ (d + 2) := by positivity
  have hp : 0 < radius (physical 1 w) ^ (d + 2) := pow_pos hrp _
  have hlo : radius (physical 1 w) ^ (d + 2) ≤
      (1 + (graphNorm w : ℝ)) ^ (d + 2) :=
    pow_le_pow_left₀ hrp.le (by linarith only [hcomp.1]) _
  have hbase : 1 + (graphNorm w : ℝ) ≤ 2 * (d : ℝ) * radius (physical 1 w) := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith only [hcomp.2, hr, hdR]
  have hhi := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (graphNorm w : ℝ))
    hbase (d + 2)
  rw [mul_pow] at hhi
  rw [jumpKernel_of_ne_zero ((physical_eq_zero_iff zero_lt_one w).not.mpr hw)]
  simp only [latticeVolumeProfile, quadraticScale, ← pow_add]
  constructor
  · rw [one_div]
    exact inv_le_inv₀ hD hp |>.mpr hlo
  · rw [← one_div]
    apply (div_le_div_iff₀ hp hD).mpr
    simpa only [one_mul] using hhi

/-- Counting-measure uniformization preserves symmetry of the density. -/
theorem unitRates_density_symm (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (x y : Site d) :
    ENNReal.ofReal ((unitRates hd hlam a ha).p x y) =
      ENNReal.ofReal ((unitRates hd hlam a ha).p y x) := by
  rw [unitRates_p_symm hd hlam a ha x y]

/-- The uniformized Euclidean walk satisfies the MSC polynomial jump comparison. -/
theorem unitRates_density_profile (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y,
      ENNReal.ofReal (C⁻¹ /
        (latticeVolumeProfile d (graphNorm (y - x)) * quadraticScale (graphNorm (y - x)))) ≤
        ENNReal.ofReal ((unitRates hd hlam a ha).p x y) ∧
      ENNReal.ofReal ((unitRates hd hlam a ha).p x y) ≤
        ENNReal.ofReal (C /
          (latticeVolumeProfile d (graphNorm (y - x)) *
            quadraticScale (graphNorm (y - x)))) := by
  classical
  let R := (unitRates hd hlam a ha).R
  let B := (2 * (d : ℝ)) ^ (d + 2)
  let C := max 2 (max (R / lam) (lam⁻¹ * B / R))
  have hR : 0 < R := (unitRates hd hlam a ha).R_pos
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCl : R / lam ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCu : lam⁻¹ * B / R ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hlow : C⁻¹ ≤ lam / R := by
    rw [← one_div, div_le_div_iff₀ hC hR]
    have ht := (div_le_iff₀ hlam).mp hCl
    nlinarith only [ht]
  refine ⟨C, hC, ?_⟩
  intro x y
  apply And.intro <;> apply ENNReal.ofReal_le_ofReal
  · by_cases h : y = x
    · subst y
      simp only [sub_self, graphNorm_zero, Nat.cast_zero, latticeVolumeProfile,
        quadraticScale, add_zero, one_pow, mul_one, div_one]
      have hi : C⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hC (by norm_num)).mpr hC2
      exact hi.trans (by simpa only [inv_eq_one_div] using
        unitRates_p_self_ge_half hd hlam a ha x)
    · have hw : y - x ≠ 0 := sub_ne_zero.mpr h
      have hk := (unitKernel_profile_bound hd hw).1
      have hD : 0 ≤ latticeVolumeProfile d (graphNorm (y - x)) *
          quadraticScale (graphNorm (y - x)) := by
        unfold latticeVolumeProfile quadraticScale
        positivity
      rw [JumpChain.BoundedRates.p, if_neg h]
      change _ ≤ unitRate a x y / R
      rw [unitRate, dif_neg hw]
      calc
        _ ≤ (lam / R) / _ := div_le_div_of_nonneg_right hlow hD
        _ = lam * (1 / (latticeVolumeProfile d (graphNorm (y - x)) *
            quadraticScale (graphNorm (y - x)))) / R := by ring
        _ ≤ a (edgeAdd x (y - x) hw) * jumpKernel (physical 1 (y - x)) / R := by
          apply div_le_div_of_nonneg_right _ hR.le
          exact mul_le_mul (ha _).1 hk (by positivity) (hlam.le.trans (ha _).1)
  · by_cases h : y = x
    · subst y
      simp only [sub_self, graphNorm_zero, Nat.cast_zero, latticeVolumeProfile,
        quadraticScale, add_zero, one_pow, mul_one, div_one]
      rw [JumpChain.BoundedRates.p, if_pos rfl]
      have ht : 0 ≤ (∑' k, (unitRates hd hlam a ha).q x k) /
          (unitRates hd hlam a ha).R :=
        div_nonneg (tsum_nonneg ((unitRates hd hlam a ha).q_nonneg x)) hR.le
      linarith only [ht, hC2]
    · have hw : y - x ≠ 0 := sub_ne_zero.mpr h
      have hk := (unitKernel_profile_bound hd hw).2
      have hD : 0 ≤ latticeVolumeProfile d (graphNorm (y - x)) *
          quadraticScale (graphNorm (y - x)) := by
        unfold latticeVolumeProfile quadraticScale
        positivity
      rw [JumpChain.BoundedRates.p, if_neg h]
      change unitRate a x y / R ≤ _
      rw [unitRate, dif_neg hw]
      calc
        _ ≤ (lam⁻¹ * (B / (latticeVolumeProfile d (graphNorm (y - x)) *
            quadraticScale (graphNorm (y - x))))) / R := by
          apply div_le_div_of_nonneg_right _ hR.le
          exact mul_le_mul (ha _).2 hk (jumpKernel_nonneg _) (inv_nonneg.mpr hlam.le)
        _ = (lam⁻¹ * B / R) / _ := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hCu hD

end

end LongRange
