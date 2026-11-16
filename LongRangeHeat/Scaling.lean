import LongRangeHeat.Continuum
import LongRange.Scaling.Generator
import LatticeProb.Euclidean.Asymptotic

/-!
# Scaling of the lattice heat flow

Halving the lattice spacing with the same integer indexing scales the generator and time.
-/


/-!
# Critical sums on expanding Euclidean annuli

The sum of the critical radial power over integer points with `R < |w| ≤ 2R` tends to
`d V_d log 2`. Summable cell errors vanish on escaping annuli, while unit cubes sandwich
the integral between annuli whose radius ratios tend to two.

Carried from Lattice-Probability revision 47027b49 (`LatticeProb/Euclidean/LatticeAnnulusRiemann.lean`).
-/

noncomputable section

open scoped BigOperators
open Filter Topology MeasureTheory Set
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube
open LatticeProb.Euclidean.Shell LatticeProb.Euclidean.Summability
open LatticeProb.Euclidean.Integral LatticeProb.Euclidean.Asymptotic

namespace LatticeProb.Euclidean.LatticeAnnulusRiemann

/-- Integer points in the annulus with strict inner and closed outer radius. -/
def annulusIndices (d : ℕ) (R : ℝ) : Finset (Site d) :=
  (unitBallIndices d (1 / (2 * R))).filter (fun w => R < radius (physical 1 w))

/-- Membership retains the exact Euclidean radial cutoffs. -/
lemma mem_annulusIndices {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Site d) :
    w ∈ annulusIndices d R ↔ R < radius (physical 1 w) ∧
      radius (physical 1 w) ≤ 2 * R := by
  rw [annulusIndices, Finset.mem_filter, mem_unitBallIndices (by positivity),
    radius_physical_eq_mul (by positivity), one_div_mul_le_one_iff (by positivity)]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · intro h
    refine ⟨⟨?_, h.2⟩, h.1⟩
    intro hz
    have hr : radius (physical 1 w) = 0 := by simp [hz, physical, radius]
    linarith [h.1]

/-- The union of centered unit cubes over the expanding integer annulus. -/
def annulusCubes (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  ⋃ w ∈ annulusIndices d R, cube w

/-- The annulus cube union is measurable. -/
lemma annulusCubes_measurable (d : ℕ) (R : ℝ) :
    MeasurableSet (annulusCubes d R) :=
  Finset.measurableSet_biUnion _ (fun w _ => cube_measurable w)

/-- The integrand is integrable on the annulus cube union away from the origin. -/
lemma integrableOn_annulusCubes {d : ℕ} (hd : 1 ≤ d) {R : ℝ}
    (hR : 2 * Real.sqrt d ≤ R) :
    IntegrableOn (criticalIntegrand d) (annulusCubes d R) volume := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  apply integrableOn_finset_iUnion.mpr
  intro w hw
  exact criticalIntegrand_integrableOn_cube d hd w
    (hR.trans ((mem_annulusIndices (by linarith) w).mp hw).1.le)

/-- The integral over the disjoint cubes is the sum of the individual cell integrals. -/
lemma integral_annulusCubes {d : ℕ} (hd : 1 ≤ d) {R : ℝ}
    (hR : 2 * Real.sqrt d ≤ R) :
    ∫ x in annulusCubes d R, criticalIntegrand d x =
      ∑ w ∈ annulusIndices d R, ∫ x in cube w, criticalIntegrand d x := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  exact integral_biUnion_finset _ (fun w _ => cube_measurable w)
    (fun _ _ _ _ h => cubes_disjoint h)
    (fun w hw => criticalIntegrand_integrableOn_cube d hd w
      (hR.trans ((mem_annulusIndices (by linarith) w).mp hw).1.le))

/-- The finite cell comparison retains the error sum on the escaping annulus. -/
lemma annulus_cell_error {d : ℕ} (hd : 1 ≤ d) {R : ℝ}
    (hR : 2 * Real.sqrt d ≤ R) :
    |(∑ w ∈ annulusIndices d R, criticalIntegrand d (physical 1 w)) -
      ∫ x in annulusCubes d R, criticalIntegrand d x| ≤
      comparisonConstant d * ∑ w ∈ annulusIndices d R,
        Real.rpow (radius (physical 1 w)) (-(d : ℝ) - 1) := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  rw [integral_annulusCubes hd hR, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ annulusIndices d R,
        |criticalIntegrand d (physical 1 w) - ∫ x in cube w, criticalIntegrand d x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ annulusIndices d R,
        comparisonConstant d * Real.rpow (radius (physical 1 w)) (-(d : ℝ) - 1) :=
      Finset.sum_le_sum fun w hw => cube_integral_error d hd w
        (hR.trans ((mem_annulusIndices (by linarith) w).mp hw).1.le)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Summability makes the radial error sum tend to zero on the escaping annulus. -/
lemma tendsto_annulus_error_sum {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun R : ℝ => ∑ w ∈ annulusIndices d R,
      Real.rpow (radius (physical 1 w)) (-(d : ℝ) - 1)) atTop (𝓝 0) := by
  classical
  have he : -(d : ℝ) - 1 = -((d + 1 : ℕ) : ℝ) := by push_cast; ring
  have hsum : Summable (fun w : Site d =>
      Real.rpow (radius (physical 1 w)) (-(d : ℝ) - 1)) := by
    rw [he]
    exact (euclidean_radial_error_summable d hd).congr
      (fun w => (Real.rpow_neg_natCast _ (d + 1)).symm)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum ε hε
  filter_upwards [eventually_ge_atTop (∑ w ∈ s, radius (physical 1 w)),
    eventually_gt_atTop (0 : ℝ)] with R hR hRpos
  have hdis : Disjoint (annulusIndices d R) s := by
    apply Finset.disjoint_left.mpr
    intro w hw hws
    have hle := Finset.single_le_sum (fun z _ => radius_nonneg (physical 1 z)) hws
    exact (not_lt_of_ge (hle.trans hR)) ((mem_annulusIndices hRpos w).mp hw).1
  simpa only [dist_zero_right, Real.norm_eq_abs] using hs _ hdis

/-- The annulus cube union lies in the annulus expanded by half a cube diagonal. -/
lemma annulusCubes_subset {d : ℕ} {R : ℝ} (hR : 0 < R) :
    annulusCubes d R ⊆ {x : Fin d → ℝ |
      R - Real.sqrt d / 2 ≤ radius x ∧ radius x ≤ 2 * R + Real.sqrt d / 2} := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨hw1, hw2⟩ := (mem_annulusIndices hR w).mp hw
  obtain ⟨he1, he2⟩ := abs_le.mp (cube_radius_error w hxw)
  constructor <;> linarith

/-- A contracted annulus lies in the cube union; the extra unit preserves the strict cutoff. -/
lemma subset_annulusCubes {d : ℕ} {R : ℝ} (hR : 0 < R) :
    {x : Fin d → ℝ | R + Real.sqrt d / 2 + 1 ≤ radius x ∧
      radius x ≤ 2 * R - Real.sqrt d / 2} ⊆ annulusCubes d R := by
  intro x hx
  have hxcube : x ∈ cube (fun k => ⌊x k + 1 / 2⌋) := by
    intro k
    have h1 := Int.floor_le (x k + 1 / 2)
    have h2 := Int.lt_floor_add_one (x k + 1 / 2)
    constructor <;> linarith
  obtain ⟨he1, he2⟩ := abs_le.mp (cube_radius_error _ hxcube)
  have hw : (fun k => ⌊x k + 1 / 2⌋) ∈ annulusIndices d R := by
    rw [mem_annulusIndices hR]
    constructor <;> linarith [hx.1, hx.2]
  exact Set.mem_iUnion₂.mpr ⟨_, hw, hxcube⟩

/-- Polar integral bounds for the union of cells in the expanding annulus. -/
lemma annulus_integral_bounds {d : ℕ} (hd : 1 ≤ d) {R : ℝ}
    (hR : 2 * Real.sqrt d + 2 ≤ R) :
    (d : ℝ) * unitBallVolume d *
        Real.log ((2 * R - Real.sqrt d / 2) / (R + Real.sqrt d / 2 + 1)) ≤
      ∫ x in annulusCubes d R, criticalIntegrand d x ∧
    (∫ x in annulusCubes d R, criticalIntegrand d x) ≤
      (d : ℝ) * unitBallVolume d *
        Real.log ((2 * R + Real.sqrt d / 2) / (R - Real.sqrt d / 2)) := by
  have hs : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hRpos : 0 < R := by linarith
  constructor
  · have ha : 0 < R + Real.sqrt d / 2 + 1 := by linarith
    have hab : R + Real.sqrt d / 2 + 1 ≤ 2 * R - Real.sqrt d / 2 := by linarith
    have hm := setIntegral_mono_set
      (s := {x : Fin d → ℝ | R + Real.sqrt d / 2 + 1 ≤ radius x ∧
        radius x ≤ 2 * R - Real.sqrt d / 2})
      (integrableOn_annulusCubes hd (by linarith : 2 * Real.sqrt d ≤ R))
      (criticalIntegrand_nonneg_ae d _)
      (Filter.Eventually.of_forall fun x hx => subset_annulusCubes hRpos hx)
    simp only [criticalIntegrand] at hm
    rw [annulus_rpow_integral hd ha hab] at hm
    exact hm
  · have ha : 0 < R - Real.sqrt d / 2 := by linarith
    have hab : R - Real.sqrt d / 2 ≤ 2 * R + Real.sqrt d / 2 := by linarith
    have hm := setIntegral_mono_set
      (criticalIntegrand_integrableOn_annulus d (b := 2 * R + Real.sqrt d / 2) ha)
      (criticalIntegrand_nonneg_ae d _)
      (Filter.Eventually.of_forall fun x hx => annulusCubes_subset hRpos hx)
    rw [annulus_rpow_integral hd ha hab] at hm
    exact hm

/-- Fixed additive shifts disappear from the ratio of two linearly expanding radii. -/
lemma tendsto_radius_ratio (a b : ℝ) :
    Tendsto (fun R : ℝ => (2 * R + a) / (R + b)) atTop (𝓝 2) := by
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have ht : Tendsto (fun R : ℝ => (2 + a * R⁻¹) / (1 + b * R⁻¹))
      atTop (𝓝 ((2 + a * 0) / (1 + b * 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hi)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hi)) (by norm_num)
  have heq : (fun R : ℝ => (2 * R + a) / (R + b)) =ᶠ[atTop]
      (fun R : ℝ => (2 + a * R⁻¹) / (1 + b * R⁻¹)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    field_simp
  have ht' : Tendsto (fun R : ℝ => (2 + a * R⁻¹) / (1 + b * R⁻¹))
      atTop (𝓝 2) := by simpa only [mul_zero, add_zero, div_one] using ht
  exact ht'.congr' heq.symm

/-- The cell union integral has the exact annulus limit. -/
lemma tendsto_annulus_integral {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun R : ℝ => ∫ x in annulusCubes d R, criticalIntegrand d x)
      atTop (𝓝 ((d : ℝ) * unitBallVolume d * Real.log 2)) := by
  have hlo := (tendsto_radius_ratio (-Real.sqrt d / 2) (Real.sqrt d / 2 + 1)).log
    (by norm_num : (2 : ℝ) ≠ 0)
  have hhi := (tendsto_radius_ratio (Real.sqrt d / 2) (-Real.sqrt d / 2)).log
    (by norm_num : (2 : ℝ) ≠ 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds.mul hlo) (tendsto_const_nhds.mul hhi)
  · filter_upwards [eventually_ge_atTop (2 * Real.sqrt (d : ℝ) + 2)] with R hR
    simpa only [add_assoc, sub_eq_add_neg, neg_div] using (annulus_integral_bounds hd hR).1
  · filter_upwards [eventually_ge_atTop (2 * Real.sqrt (d : ℝ) + 2)] with R hR
    simpa only [sub_eq_add_neg, neg_div] using (annulus_integral_bounds hd hR).2

/-- The critical Euclidean integer annulus sum tends to `d V_d log 2`. -/
theorem tendsto_annulus_sum {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun R : ℝ => ∑ w ∈ annulusIndices d R,
      Real.rpow (radius (physical 1 w)) (-(d : ℝ)))
      atTop (𝓝 ((d : ℝ) * unitBallVolume d * Real.log 2)) := by
  have he : Tendsto (fun R : ℝ => comparisonConstant d * ∑ w ∈ annulusIndices d R,
      Real.rpow (radius (physical 1 w)) (-(d : ℝ) - 1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_annulus_error_sum hd)
  have hdist : Tendsto (fun R : ℝ => dist
      (∑ w ∈ annulusIndices d R, criticalIntegrand d (physical 1 w))
      (∫ x in annulusCubes d R, criticalIntegrand d x)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ he
    filter_upwards [eventually_ge_atTop (2 * Real.sqrt (d : ℝ))] with R hR
    rw [Real.dist_eq]
    exact annulus_cell_error hd hR
  apply (tendsto_annulus_integral hd).congr_dist
  simpa only [dist_comm, criticalIntegrand] using hdist

end LatticeProb.Euclidean.LatticeAnnulusRiemann


open Filter Topology
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Shell
open LatticeProb.Euclidean.LatticeAnnulusRiemann

namespace LongRange

/-- Halving the mesh adds exactly the strict-inner, closed-outer integer annulus. -/
theorem kappa_half_sub_eq_annulus_sum {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    kappa d (ε / 2) - kappa d ε =
      ∑ w ∈ annulusIndices d (1 / ε),
        Real.rpow (radius (physical 1 w)) (-(d : ℝ)) := by
  classical
  have hhalf : 0 < ε / 2 := by positivity
  have hrad (η : ℝ) (hη : 0 < η) (w : LatticeProb.Site d) :
      w ∈ unitBallIndices d η ↔ w ≠ 0 ∧ radius (physical 1 w) ≤ 1 / η := by
    rw [mem_unitBallIndices hη, radius_physical_eq_mul hη.le,
      mul_comm η, ← le_div_iff₀ hη]
  have hsub : unitBallIndices d ε ⊆ unitBallIndices d (ε / 2) := by
    intro w hw
    obtain ⟨hw0, hw⟩ := (hrad ε hε w).mp hw
    apply (hrad (ε / 2) hhalf w).mpr
    refine ⟨hw0, hw.trans ?_⟩
    exact one_div_le_one_div_of_le hhalf (by linarith)
  have heq : unitBallIndices d (ε / 2) \ unitBallIndices d ε =
      annulusIndices d (1 / ε) := by
    ext w
    rw [Finset.mem_sdiff, hrad (ε / 2) hhalf, hrad ε hε,
      mem_annulusIndices (by positivity)]
    have he : 1 / (ε / 2) = 2 * (1 / ε) := by ring
    rw [he]
    constructor
    · rintro ⟨⟨hw0, hw⟩, hn⟩
      exact ⟨lt_of_not_ge (fun h => hn ⟨hw0, h⟩), hw⟩
    · rintro ⟨hw1, hw2⟩
      have hw0 : w ≠ 0 := by
        intro hz
        have hr : radius (physical 1 w) = 0 := by simp [hz, physical, radius]
        have hp : 0 < 1 / ε := by positivity
        linarith
      exact ⟨⟨hw0, hw2⟩, fun h => not_le_of_gt hw1 h.2⟩
  rw [kappa_eq_integer_sum hhalf, kappa_eq_integer_sum hε,
    ← Finset.sum_sdiff hsub, heq, add_sub_cancel_right]
  rfl

/-- The exact normalization increment tends to the Euclidean annulus integral. -/
theorem tendsto_kappa_half_sub {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε) (𝓝[>] 0)
      (𝓝 ((d : ℝ) *
        (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)) * Real.log 2)) := by
  have ht := (tendsto_annulus_sum hd).comp
    (show Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop by
      simpa only [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)))
  rw [unitBallVolume_eq_pi_div_gamma] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (kappa_half_sub_eq_annulus_sum hε).symm


end LongRange

namespace LongRangeHeat

open LatticeProb LatticeProb.Euclidean.Lattice LongRange

noncomputable section

/-- The lattice heat series scales under a simultaneous halving of the lattice and initial data. -/
theorem latticeHeat_half {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (a : Edge d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (t : ℝ) (q : Site d) :
    latticeHeat (ε / 2) a (fun x => f (2 • x)) t q =
      latticeHeat ε a f ((4 * kappa d ε / kappa d (ε / 2)) * t) q := by
  let c : ℝ := 4 * kappa d ε / kappa d (ε / 2)
  have hr : restrict (ε / 2) (fun x => f (2 • x)) = restrict ε f := by
    funext q
    change f (2 • physical (ε / 2) q) = f (physical ε q)
    apply congrArg f
    funext i
    simp only [physical, Pi.smul_apply]
    ring
  have hi (n : ℕ) : (generator (ε / 2) a)^[n] (restrict ε f) =
      fun q => c ^ n * (generator ε a)^[n] (restrict ε f) q := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext q
      rw [generator_const_mul, Scaling.generator_half hd hε]
      rw [Function.iterate_succ_apply']
      dsimp only [c]
      rw [pow_succ]
      ring
  unfold latticeHeat
  rw [hr]
  apply tsum_congr
  intro n
  rw [hi]
  dsimp only
  rw [mul_pow]
  ring

/-- The continuum heat flow obeys the same spatial dilation with diffusive time scaling. -/
theorem continuumHeat_half {d : ℕ} (hd : 1 ≤ d) (f : (Fin d → ℝ) → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    continuumHeat (fun y => f (2 • y)) t ((1 / 2 : ℝ) • x) =
      continuumHeat f (4 * t) x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [continuumHeat, mul_zero, ↓reduceIte]
    apply congrArg f
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [continuumHeat_eq_integral _ ht, continuumHeat_eq_integral _ (by positivity)]
    rw [LatticeProb.Heat.integral_heatKernel_mul_eq hd (τ := t) ht,
      LatticeProb.Heat.integral_heatKernel_mul_eq hd (τ := 4 * t) (by positivity)]
    have hs : Real.sqrt ((4 * t) / d) = 2 * Real.sqrt (t / d) := by
      rw [show (4 * t) / (d : ℝ) = 4 * (t / d) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hs]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    congr 1
    congr 1
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- The halving time defect has the exact inverse-logarithmic coefficient. -/
theorem kappa_half_ratio_tendsto {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun ε : ℝ =>
      ((kappa d (ε / 2) - kappa d ε) / kappa d (ε / 2)) * |Real.log ε|)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  have hA : 0 < A := by
    dsimp [A]
    rw [← unitBallVolume_eq_pi_div_gamma]
    exact mul_pos (Nat.cast_pos.mpr (by omega)) (unitBallVolume_pos d)
  have hL : Tendsto (fun ε : ℝ => |Real.log ε|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  obtain ⟨K, _, hK⟩ := kappa_asymptotic hd
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hε hε'
    exact ⟨hε, hε'.le⟩
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      -K ≤ kappa d ε - A * |Real.log ε| ∧ kappa d ε - A * |Real.log ε| ≤ K := by
    filter_upwards [hsmall] with ε hε
    exact abs_le.mp (hK ε hε)
  have hz : Tendsto (fun ε : ℝ => (kappa d ε - A * |Real.log ε|) / |Real.log ε|)
      (𝓝[>] 0) (𝓝 0) := tendsto_bdd_div_atTop_nhds_zero (hb.mono fun _ h => h.1)
        (hb.mono fun _ h => h.2) hL
  have hLpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < |Real.log ε| := hL.eventually_gt_atTop 0
  have hk : Tendsto (fun ε : ℝ => kappa d ε / |Real.log ε|) (𝓝[>] 0) (𝓝 A) := by
    have h := hz.add (tendsto_const_nhds (x := A))
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [hLpos] with ε hε
    field_simp
    ring
  have hi : Tendsto (fun ε : ℝ => kappa d (ε / 2) - kappa d ε)
      (𝓝[>] 0) (𝓝 (A * Real.log 2)) := by
    simpa [A] using tendsto_kappa_half_sub hd
  have hi0 := hi.div_atTop hL
  have hkhalf : Tendsto (fun ε : ℝ => kappa d (ε / 2) / |Real.log ε|)
      (𝓝[>] 0) (𝓝 A) := by
    have h := hi0.add hk
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [] with ε
    ring
  have hfinal := hi.div hkhalf hA.ne'
  have htarget : A * Real.log 2 / A = Real.log 2 := by field_simp
  rw [htarget] at hfinal
  apply hfinal.congr'
  filter_upwards [] with ε
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end
end LongRangeHeat
