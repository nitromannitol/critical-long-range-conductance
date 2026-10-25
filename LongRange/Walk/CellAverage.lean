import LongRange.Model.Lattice
import LongRange.Appendix.LatticeCount
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Full-cell averages

Cell averages use zero extension and the volume of the full half-open lattice cell.
The cells are disjoint even at their boundaries.
-/

namespace LongRange

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The full half-open cube centered at the physical lattice point. -/
def cellCube (ε : ℝ) (q : Site d) : Set (Fin d → ℝ) :=
  {y | ∀ i, physical ε q i - ε / 2 ≤ y i ∧ y i < physical ε q i + ε / 2}

/-- A cell is a product of half-open intervals. -/
theorem cellCube_eq_pi (ε : ℝ) (q : Site d) :
    cellCube ε q = Set.pi Set.univ
      (fun i => Set.Ico (physical ε q i - ε / 2) (physical ε q i + ε / 2)) := by
  ext y
  simp only [cellCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico,
    forall_const]

/-- Full cells are Lebesgue measurable. -/
theorem measurableSet_cellCube (ε : ℝ) (q : Site d) : MeasurableSet (cellCube ε q) := by
  rw [cellCube_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

/-- A full cell has volume `ε^d`. -/
theorem volume_cellCube {ε : ℝ} (hε : 0 < ε) (q : Site d) :
    volume (cellCube ε q) = ENNReal.ofReal (ε ^ d) := by
  rw [cellCube_eq_pi, Real.volume_pi_Ico]
  have hside : ∀ i, physical ε q i + ε / 2 - (physical ε q i - ε / 2) = ε := by
    intro i
    ring
  simp only [hside, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow hε.le _).symm

/-- Distinct lattice sites have disjoint full cells. -/
theorem cellCube_disjoint {ε : ℝ} (hε : 0 < ε) {q q' : Site d} (hne : q ≠ q') :
    Disjoint (cellCube ε q) (cellCube ε q') := by
  apply Set.disjoint_left.mpr
  intro y hy hy'
  apply hne
  funext i
  have h₁ := hy i
  have h₂ := hy' i
  dsimp [physical] at h₁ h₂
  have hlt : |(q i : ℝ) - q' i| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hint : |q i - q' i| < (1 : ℤ) := by exact_mod_cast hlt
  have := abs_lt.mp hint
  omega

/-- Zero extension averaged over a full cell, with denominator `ε^d`. -/
def cellAverage (ε : ℝ) (U : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ)
    (q : Site d) : ℝ :=
  (ε ^ d)⁻¹ * ∫ y in cellCube ε q, U.indicator f y

/-- Averaging a constant on the whole space preserves that constant. -/
theorem cellAverage_const_univ {ε : ℝ} (hε : 0 < ε) (c : ℝ) (q : Site d) :
    cellAverage ε Set.univ (fun _ => c) q = c := by
  simp only [cellAverage, Set.indicator_univ, integral_const, Measure.real,
    Measure.restrict_apply_univ,
    volume_cellCube hε, ENNReal.toReal_ofReal (pow_nonneg hε.le _), smul_eq_mul]
  field_simp [ne_of_gt (pow_pos hε d)]

/-- Cell averages depend only on the almost-everywhere class on the domain. -/
theorem cellAverage_congr_ae {ε : ℝ} {U : Set (Fin d → ℝ)} (hU : MeasurableSet U)
    {f g : (Fin d → ℝ) → ℝ} (hfg : f =ᵐ[volume.restrict U] g) (q : Site d) :
    cellAverage ε U f q = cellAverage ε U g q := by
  have he := (ae_eq_restrict_iff_indicator_ae_eq hU).mp hfg
  unfold cellAverage
  congr 1
  exact integral_congr_ae (he.filter_mono (ae_mono Measure.restrict_le_self))

/-- The physical center belongs to its full cell. -/
theorem physical_mem_cellCube {ε : ℝ} (hε : 0 < ε) (q : Site d) :
    physical ε q ∈ cellCube ε q := by
  intro i
  constructor <;> linarith

/-- The integral of the squared zero extension is the zero extension of the square. -/
theorem indicator_sq (U : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) :
    (fun y => (U.indicator f y) ^ 2) = U.indicator (fun y => f y ^ 2) := by
  classical
  funext y
  by_cases hy : y ∈ U <;> simp [hy]

/-- Jensen's inequality on a full cell for the square-integrable zero extension. -/
theorem cellAverage_sq_le {ε : ℝ} (hε : 0 < ε) (U : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (q : Site d)
    (hf : MemLp (U.indicator f) 2 (volume.restrict (cellCube ε q))) :
    (cellAverage ε U f q) ^ 2 ≤ (ε ^ d)⁻¹ *
      ∫ y in cellCube ε q, U.indicator (fun y => f y ^ 2) y := by
  let μ := volume.restrict (cellCube ε q)
  have hvol : μ Set.univ = ENNReal.ofReal (ε ^ d) := by
    simp only [μ, Measure.restrict_apply_univ, volume_cellCube hε]
  haveI : IsFiniteMeasure μ := ⟨by rw [hvol]; exact ENNReal.ofReal_lt_top⟩
  have hi : Integrable (U.indicator f) μ := hf.integrable (by norm_num)
  let a := cellAverage ε U f q
  have hn : 0 ≤ ∫ y, (U.indicator f y - a) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have heq : (fun y => (U.indicator f y - a) ^ 2) =
      (fun y => (U.indicator f y) ^ 2 - 2 * a * U.indicator f y + a ^ 2) := by
    funext y
    ring
  have hsq : Integrable (fun y => (U.indicator f y) ^ 2) μ := hf.integrable_sq
  have hmul : Integrable (fun y => 2 * a * U.indicator f y) μ := hi.const_mul (2 * a)
  have hexpand : (∫ y, (U.indicator f y) ^ 2 - 2 * a * U.indicator f y + a ^ 2 ∂μ) =
      (∫ y, (U.indicator f y) ^ 2 ∂μ) -
        2 * a * (∫ y, U.indicator f y ∂μ) + μ.real Set.univ * a ^ 2 := by
    calc
      _ = (∫ y, (U.indicator f y) ^ 2 - 2 * a * U.indicator f y ∂μ) +
          ∫ _y : Fin d → ℝ, a ^ 2 ∂μ :=
        integral_add (μ := μ) (f := fun y => (U.indicator f y) ^ 2 -
          2 * a * U.indicator f y) (g := fun _ => a ^ 2)
          (hsq.sub hmul) (integrable_const (a ^ 2))
      _ = _ := by
        rw [integral_sub hsq hmul, integral_const_mul, integral_const, smul_eq_mul]
  rw [heq, hexpand, Measure.real, hvol,
    ENNReal.toReal_ofReal (pow_nonneg hε.le _)] at hn
  have ha : (ε ^ d) * a = ∫ y, U.indicator f y ∂μ := by
    dsimp [a, cellAverage, μ]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hε _)), one_mul]
  rw [← indicator_sq]
  change a ^ 2 ≤ (ε ^ d)⁻¹ * ∫ y, (U.indicator f y) ^ 2 ∂μ
  have hp := pow_pos hε d
  have hb : (ε ^ d) * a ^ 2 ≤ ∫ y, (U.indicator f y) ^ 2 ∂μ := by
    rw [← ha] at hn
    nlinarith only [hn]
  exact (le_inv_mul_iff₀ hp).mpr hb

/-- Jensen also applies when the original function is square-integrable on the cell. -/
theorem cellAverage_sq_le_of_memLp {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U)
    {f : (Fin d → ℝ) → ℝ} (q : Site d)
    (hf : MemLp f 2 (volume.restrict (cellCube ε q))) :
    (cellAverage ε U f q) ^ 2 ≤ (ε ^ d)⁻¹ *
      ∫ y in cellCube ε q, U.indicator (fun y => f y ^ 2) y :=
  cellAverage_sq_le hε U f q (hf.indicator hU)

/-- Full-cell averaging contracts the squared discrete norm on a bounded measurable domain. -/
theorem l2NormSq_cellAverage_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : MeasurableSet U) (hb : Bornology.IsBounded U)
    {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    l2NormSq ε U (cellAverage ε U f) ≤ ∫ y in U, f y ^ 2 := by
  classical
  letI := (latticeSet_finite hε hb).fintype
  have he : MemLp (U.indicator f) 2 volume := (memLp_indicator_iff_restrict hU).mpr hf
  have hs : Integrable (U.indicator (fun y => f y ^ 2)) volume := by
    rw [← indicator_sq]
    exact he.integrable_sq
  have hj (q : latticeSet ε U) := cellAverage_sq_le hε U f q (he.restrict _)
  have hp : 0 < ε ^ d := pow_pos hε _
  calc
    l2NormSq ε U (cellAverage ε U f) =
        ε ^ d * ∑ q : latticeSet ε U, (cellAverage ε U f q) ^ 2 := by
      rw [l2NormSq, tsum_fintype]
    _ ≤ ε ^ d * ∑ q : latticeSet ε U,
        (ε ^ d)⁻¹ * ∫ y in cellCube ε q, U.indicator (fun y => f y ^ 2) y :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hj q)) hp.le
    _ = ∑ q : latticeSet ε U,
        ∫ y in cellCube ε q, U.indicator (fun y => f y ^ 2) y := by
      rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    _ = ∫ y in ⋃ q : latticeSet ε U, cellCube ε q,
        U.indicator (fun y => f y ^ 2) y := by
      symm
      have hd : Pairwise (fun q q' : latticeSet ε U =>
          Disjoint (cellCube ε q.val) (cellCube ε q'.val)) := by
        intro q q' hne
        exact cellCube_disjoint hε (fun h => hne (Subtype.ext h))
      exact integral_iUnion_fintype (μ := volume)
        (f := U.indicator (fun y => f y ^ 2))
        (s := fun q : latticeSet ε U => cellCube ε q.val)
        (fun q : latticeSet ε U => measurableSet_cellCube ε q.val) hd
        (fun _ => hs.integrableOn)
    _ ≤ ∫ y, U.indicator (fun y => f y ^ 2) y := by
      apply setIntegral_le_integral hs
      apply Filter.Eventually.of_forall
      intro y
      change 0 ≤ U.indicator (fun y => f y ^ 2) y
      by_cases hy : y ∈ U
      · simpa only [Set.indicator_of_mem hy] using sq_nonneg (f y)
      · simp only [Set.indicator_of_notMem hy, le_refl]
    _ = ∫ y in U, f y ^ 2 := integral_indicator hU

/-- Every point of a cell lies within its Euclidean half-diagonal of the center. -/
theorem radius_sub_physical_le {ε : ℝ} (hε : 0 < ε) (q : Site d)
    {y : Fin d → ℝ} (hy : y ∈ cellCube ε q) :
    radius (y - physical ε q) ≤ Real.sqrt d * ε / 2 := by
  have hc (i : Fin d) : (y i - physical ε q i) ^ 2 ≤ (ε / 2) ^ 2 := by
    have hi := hy i
    nlinarith [sq_nonneg (y i - physical ε q i - ε / 2),
      sq_nonneg (y i - physical ε q i + ε / 2)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hc i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply (sq_le_sq₀ (radius_nonneg _) (by positivity)).mp
  rw [radius_sq, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [Pi.sub_apply, div_pow, mul_div_assoc] using hsum

/-- A continuous function with a Euclidean modulus differs little from its cell average. -/
theorem abs_cellAverage_sub_sample_le {ε : ℝ} (hε : 0 < ε)
    (U : Set (Fin d → ℝ)) {F : (Fin d → ℝ) → ℝ} (hF : Continuous F)
    (hzero : ∀ y, y ∉ U → F y = 0) (ω : ℝ → ℝ)
    (hω : ∀ y z r, radius (y - z) ≤ r → |F y - F z| ≤ ω r) (q : Site d) :
    |cellAverage ε U F q - F (physical ε q)| ≤ ω (Real.sqrt d * ε / 2) := by
  classical
  let R := Real.sqrt (d : ℝ) * ε / 2
  have hext : U.indicator F = F := by
    funext y
    by_cases hy : y ∈ U
    · exact Set.indicator_of_mem hy F
    · rw [Set.indicator_of_notMem hy, hzero y hy]
  have hm : ∀ y ∈ cellCube ε q, |F y - F (physical ε q)| ≤ ω R := by
    intro y hy
    exact hω _ _ _ (radius_sub_physical_le hε q hy)
  have hv : volume (cellCube ε q) ≠ ⊤ := by
    rw [volume_cellCube hε]
    exact ENNReal.ofReal_ne_top
  have hi : IntegrableOn F (cellCube ε q) volume := by
    apply Measure.integrableOn_of_bounded hv hF.aestronglyMeasurable
    apply (ae_restrict_mem (measurableSet_cellCube ε q)).mono
    intro y hy
    have := hm y hy
    have ht := abs_add_le (F y - F (physical ε q)) (F (physical ε q))
    rw [Real.norm_eq_abs]
    simp only [sub_add_cancel] at ht
    exact ht.trans (add_le_add this le_rfl)
  have hid : cellAverage ε U F q - F (physical ε q) =
      (ε ^ d)⁻¹ * ∫ y in cellCube ε q, (F y - F (physical ε q)) := by
    rw [cellAverage, hext, integral_sub hi (integrableOn_const hv),
      integral_const, Measure.real, Measure.restrict_apply_univ, volume_cellCube hε,
      ENNReal.toReal_ofReal (pow_nonneg hε.le _), smul_eq_mul]
    field_simp [ne_of_gt (pow_pos hε d)]
  have hn := norm_setIntegral_le_of_norm_le_const hv.lt_top
    (fun y hy => (show ‖F y - F (physical ε q)‖ ≤ ω R from hm y hy))
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  have hvreal : volume.real (cellCube ε q) = ε ^ d := by
    rw [Measure.real, volume_cellCube hε, ENNReal.toReal_ofReal (pow_nonneg hε.le _)]
  rw [hvreal, Real.norm_eq_abs] at hn
  calc
    (ε ^ d)⁻¹ * |∫ y in cellCube ε q, F y - F (physical ε q)| ≤
        (ε ^ d)⁻¹ * (ω R * ε ^ d) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (pow_nonneg hε.le _))
    _ = ω R := by field_simp

/-- Summing the squared cell sampling error gives the lattice count times the modulus squared. -/
theorem cellAverage_sub_sample_le {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    {F : (Fin d → ℝ) → ℝ} (hF : Continuous F)
    (hzero : ∀ y, y ∉ U → F y = 0) (ω : ℝ → ℝ)
    (hω : ∀ y z r, radius (y - z) ≤ r → |F y - F z| ≤ ω r) :
    l2NormSq ε U (fun q => cellAverage ε U F q - F (physical ε q)) ≤
      ε ^ d * (latticeSet ε U).ncard * ω (Real.sqrt d * ε / 2) ^ 2 := by
  classical
  letI := (latticeSet_finite hε hb).fintype
  have hm (q : Site d) := abs_cellAverage_sub_sample_le hε U hF hzero ω hω q
  have hn : 0 ≤ ω (Real.sqrt d * ε / 2) :=
    (abs_nonneg _).trans (hm 0)
  have hs (q : Site d) : (cellAverage ε U F q - F (physical ε q)) ^ 2 ≤
      ω (Real.sqrt d * ε / 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hn).mpr (hm q)
  rw [l2NormSq, tsum_fintype]
  calc
    ε ^ d * ∑ q : latticeSet ε U, (cellAverage ε U F q - F (physical ε q)) ^ 2 ≤
        ε ^ d * ∑ _q : latticeSet ε U, ω (Real.sqrt d * ε / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hs q))
        (pow_nonneg hε.le _)
    _ = ε ^ d * (latticeSet ε U).ncard * ω (Real.sqrt d * ε / 2) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Set.fintypeCard_eq_ncard]
      ring

/-- On bounded domains the squared sampling error tends to zero for a vanishing modulus. -/
theorem tendsto_l2NormSq_cellAverage_sub_sample
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    {F : (Fin d → ℝ) → ℝ} (hF : Continuous F)
    (hzero : ∀ y, y ∉ U → F y = 0) (ω : ℝ → ℝ)
    (hω : ∀ y z r, radius (y - z) ≤ r → |F y - F z| ≤ ω r)
    (hlim : Filter.Tendsto ω (nhds 0) (nhds 0)) :
    Filter.Tendsto
      (fun ε => l2NormSq ε U (fun q => cellAverage ε U F q - F (physical ε q)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC, hc⟩ := ncard_latticeSet_le d (euclideanDiam U)
  have hcount {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
      ε ^ d * (latticeSet ε U).ncard ≤ C := by
    have hh := mul_le_mul_of_nonneg_left
      (hc U hb le_rfl ε hε) (pow_nonneg hε.1.le d)
    rw [Real.rpow_neg hε.1.le, Real.rpow_natCast] at hh
    have hp : ε ^ d ≠ 0 := (pow_pos hε.1 d).ne'
    calc
      ε ^ d * (latticeSet ε U).ncard ≤ ε ^ d * (C * (ε ^ d)⁻¹) := hh
      _ = C := by field_simp
  have he : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε ∈ Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, (show ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ε < 1 from (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds)] with ε hpos hlt
    exact ⟨hpos, hlt⟩
  have hr : Filter.Tendsto (fun ε : ℝ => Real.sqrt d * ε / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hi : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero, zero_div] using
      ((tendsto_const_nhds (x := Real.sqrt (d : ℝ))).mul hi).div_const (2 : ℝ)
  have ht := (tendsto_const_nhds (x := C)).mul ((hlim.comp hr).pow 2)
  apply squeeze_zero' _ _ (by simpa using ht : Filter.Tendsto
    (fun ε : ℝ => C * ω (Real.sqrt d * ε / 2) ^ 2) _ (nhds 0))
  · filter_upwards [he] with ε hε
    exact mul_nonneg (pow_nonneg hε.1.le _) (tsum_nonneg (fun _ => sq_nonneg _))
  · filter_upwards [he] with ε hε
    exact (cellAverage_sub_sample_le hε.1 hb hF hzero ω hω).trans
      (mul_le_mul_of_nonneg_right (hcount hε) (sq_nonneg _))

end

end LongRange
