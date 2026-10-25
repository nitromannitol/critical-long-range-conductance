import LongRange.TwoScale.KernelSums
import LongRange.Appendix.LatticeCount
import LongRange.Model.Energy

/-!
# Boundary defect of the zero extension

The distance to the domain is measured in the Euclidean carrier. Finite support and
vanishing in the domain justify endpoint reindexing of the boundary energy.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Euclidean distance of a physical lattice point from the domain. -/
def boundaryDistance (ε : ℝ) (U : Set (Fin d → ℝ)) (y : Site d) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (physical ε y)) (WithLp.toLp 2 '' U)

/-- The boundary defect energy, with the first endpoint restricted to the domain. -/
def boundaryDefectEnergy (ε : ℝ) (U : Set (Fin d → ℝ)) (r : Site d → ℝ) : ℝ :=
  ε ^ (2 * d) / kappa d ε * ∑' p : latticeSet ε U × Site d,
    jumpKernel (physical ε p.2) * r ((p.1 : Site d) + p.2) ^ 2

/-- The boundary error in the generator of the zero extension. -/
def boundaryDefect (ε : ℝ) (a : Edge d → ℝ) (r : Site d → ℝ) (x : Site d) : ℝ :=
  -(ε ^ d / kappa d ε) * ∑' w : Site d,
    if hw : w = 0 then 0 else
      a (edgeAdd x w hw) * jumpKernel (physical ε w) * r (x + w)

/-- Endpoint reindexing exchanges increments with the second endpoint. -/
def boundaryEndpointEquiv (ε : ℝ) (U : Set (Fin d → ℝ)) :
    (latticeSet ε U × Site d) ≃ (Site d × latticeSet ε U) where
  toFun p := ((p.1 : Site d) + p.2, p.1)
  invFun p := (p.2, p.1 - (p.2 : Site d))
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Restricting the first endpoint and the support of the second gives a finite series. -/
lemma boundary_endpoint_finite {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hU : (latticeSet ε U).Finite) {r : Site d → ℝ}
    (hr : Function.HasFiniteSupport r) (f : latticeSet ε U × Site d → ℝ)
    (hf : ∀ p, r ((p.1 : Site d) + p.2) = 0 → f p = 0) :
    Function.HasFiniteSupport f := by
  have hfinite : Set.Finite (Set.univ : Set (latticeSet ε U)) := by
    letI := hU.fintype
    exact Set.finite_univ
  apply ((hfinite.prod hr).image
    (fun p : latticeSet ε U × Site d => (p.1, p.2 - (p.1 : Site d)))).subset
  intro p hp
  refine ⟨(p.1, (p.1 : Site d) + p.2), ⟨Set.mem_univ _, ?_⟩, ?_⟩
  · exact fun hz => hp (hf p hz)
  · simp

/-- Boundary energy is a finite sum even though increments range over the entire lattice. -/
lemma summable_boundary_energy {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hU : (latticeSet ε U).Finite) {r : Site d → ℝ}
    (hr : Function.HasFiniteSupport r) :
    Summable (fun p : latticeSet ε U × Site d =>
      jumpKernel (physical ε p.2) * r ((p.1 : Site d) + p.2) ^ 2) := by
  apply summable_of_hasFiniteSupport (boundary_endpoint_finite hU hr _ ?_)
  intro p hp
  simp only [hp, zero_pow (by decide : 2 ≠ 0), mul_zero]

/-- Reindexing the defect energy by its exterior endpoint preserves the normalization. -/
lemma boundaryDefectEnergy_eq {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hU : (latticeSet ε U).Finite) {r : Site d → ℝ}
    (hr : Function.HasFiniteSupport r) :
    boundaryDefectEnergy ε U r = ε ^ (2 * d) / kappa d ε *
      ∑' y : Site d, r y ^ 2 *
        ∑' x : latticeSet ε U, jumpKernel (physical ε (y - (x : Site d))) := by
  have hs := summable_boundary_energy hU hr
  let e := boundaryEndpointEquiv ε U
  have he : (fun p : latticeSet ε U × Site d =>
      jumpKernel (physical ε p.2) * r ((p.1 : Site d) + p.2) ^ 2) =
      (fun p : Site d × latticeSet ε U =>
        jumpKernel (physical ε (p.1 - (p.2 : Site d))) * r p.1 ^ 2) ∘ e := by
    funext p
    simp [e, boundaryEndpointEquiv]
  rw [he] at hs
  unfold boundaryDefectEnergy
  rw [he]
  simp only [Function.comp_def]
  rw [e.tsum_eq (fun p : Site d × latticeSet ε U =>
    jumpKernel (physical ε (p.1 - (p.2 : Site d))) * r p.1 ^ 2)]
  rw [((e.summable_iff).mp hs).tsum_prod]
  congr 1
  apply tsum_congr
  intro y
  rw [← tsum_mul_left]
  congr 1
  funext x
  ring

/-- Distance zero forces a Lipschitz boundary defect to vanish. -/
lemma boundary_defect_zero_of_distance_zero {ε L : ℝ} {U : Set (Fin d → ℝ)}
    {r : Site d → ℝ} (hr : ∀ y, |r y| ≤ L * boundaryDistance ε U y)
    {y : Site d} (hy : boundaryDistance ε U y = 0) : r y = 0 := by
  have h := hr y
  rw [hy, mul_zero] at h
  exact abs_nonpos_iff.mp h

/-- A squared Lipschitz defect cancels the inverse-square boundary-kernel singularity. -/
lemma boundary_distance_cancellation {ε L δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    {t : ℝ} (ht : |t| ≤ L * δ) :
    t ^ 2 * (δ + ε) ^ (-2 : ℝ) ≤ L ^ 2 := by
  have hs : 0 < δ + ε := add_pos_of_nonneg_of_pos hδ hε
  rw [Real.rpow_neg hs.le, Real.rpow_two, ← div_eq_mul_inv,
    div_le_iff₀ (sq_pos_of_pos hs)]
  have hsq := sq_le_sq₀ (abs_nonneg t) ((abs_nonneg t).trans ht) |>.mpr ht
  rw [sq_abs, mul_pow] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hδ (by linarith : δ ≤ δ + ε) 2) (sq_nonneg L))

/-- A Euclidean ball is bounded also on the coordinate carrier. -/
lemma boundary_ball_bounded (R : ℝ) :
    Bornology.IsBounded {z : Fin d → ℝ | radius z ≤ R} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max R 0, ?_⟩
  intro z hz
  apply (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr
  intro i
  exact (abs_coord_le_radius z i).trans (hz.trans (le_max_left R 0))

/-- The Euclidean diameter of a radius-`R` ball is at most `2 max R 0`. -/
lemma boundary_ball_diam_le (R : ℝ) :
    euclideanDiam {z : Fin d → ℝ | radius z ≤ R} ≤ 2 * max R 0 := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  calc
    dist (WithLp.toLp 2 x) (WithLp.toLp 2 y) ≤
        ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := dist_le_norm_add_norm _ _
    _ = radius x + radius y := by rw [← radius_norm, ← radius_norm]
    _ ≤ 2 * max R 0 := by
      change radius x ≤ R at hx
      change radius y ≤ R at hy
      linarith [le_max_left R 0]

/-- The boundary energy bound has a constant depending only on dimension and support radius. -/
theorem boundaryDefectEnergy_le (d : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ (r : Site d → ℝ) (L : ℝ),
        (∀ y, R < radius (physical ε y) → r y = 0) →
        (∀ y, |r y| ≤ L * boundaryDistance ε U y) →
        boundaryDefectEnergy ε U r ≤ C * L ^ 2 / kappa d ε := by
  classical
  obtain ⟨B, hB, hb⟩ := boundary_kernel_sum_dist_bound d
  obtain ⟨A, hA, ha⟩ := ncard_latticeSet_le d (2 * max R 0)
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro ε hε U hU r L hR hr
  let V : Set (Fin d → ℝ) := {z | radius z ≤ R}
  have hV := latticeSet_finite hε.1 (boundary_ball_bounded (d := d) R)
  have hs : Function.support r ⊆ latticeSet ε V := by
    intro y hy
    exact le_of_not_gt (fun h => hy (hR y h))
  have hrf : Function.HasFiniteSupport r := hV.subset hs
  have hc := ha V (boundary_ball_bounded R) (boundary_ball_diam_le R) ε hε
  have hpoint (y : Site d) :
      r y ^ 2 * (ε ^ d * ∑' x : latticeSet ε U,
        jumpKernel (physical ε (y - (x : Site d)))) ≤ B * L ^ 2 := by
    by_cases hy : r y = 0
    · simp only [hy, zero_pow (by decide : 2 ≠ 0), zero_mul]
      exact mul_nonneg hB.le (sq_nonneg L)
    have hδ : 0 < boundaryDistance ε U y := by
      apply lt_of_le_of_ne Metric.infDist_nonneg
      exact fun hz => hy (boundary_defect_zero_of_distance_zero hr hz.symm)
    obtain ⟨_, hbound⟩ := hb ε hε.1 y U hδ
    calc
      _ ≤ r y ^ 2 * (B * (boundaryDistance ε U y + ε) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
      _ = B * (r y ^ 2 * (boundaryDistance ε U y + ε) ^ (-2 : ℝ)) := by ring
      _ ≤ B * L ^ 2 := mul_le_mul_of_nonneg_left
        (boundary_distance_cancellation hε.1 hδ.le (hr y)) hB.le
  have hsum : ε ^ d * ∑' y : Site d, r y ^ 2 *
      ∑' x : latticeSet ε U, jumpKernel (physical ε (y - (x : Site d))) ≤
      (A * B) * L ^ 2 / ε ^ d := by
    rw [← tsum_mul_left]
    rw [tsum_eq_sum (s := hrf.toFinset) (fun y hy => by
      have hz : r y = 0 := by simpa only [Set.Finite.mem_toFinset,
        Function.mem_support, not_not] using hy
      simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero])]
    calc
      _ ≤ ∑ y ∈ hrf.toFinset, B * L ^ 2 := by
        apply Finset.sum_le_sum
        intro y _
        simpa only [mul_left_comm] using hpoint y
      _ = ((Function.support r).ncard : ℝ) * (B * L ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hrf]
      _ ≤ ((latticeSet ε V).ncard : ℝ) * (B * L ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Set.ncard_le_ncard hs hV)
          (mul_nonneg hB.le (sq_nonneg L))
      _ ≤ (A * ε ^ (-(d : ℝ))) * (B * L ^ 2) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hB.le (sq_nonneg L))
      _ = (A * B) * L ^ 2 / ε ^ d := by
        rw [Real.rpow_neg hε.1.le, Real.rpow_natCast]
        ring
  rw [boundaryDefectEnergy_eq (latticeSet_finite hε.1 hU) hrf]
  have hk : 0 ≤ kappa d ε := by
    unfold kappa
    exact mul_nonneg (pow_nonneg hε.1.le _) (Finset.sum_nonneg fun _ _ =>
      inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))
  calc
    _ = (ε ^ d / kappa d ε) * (ε ^ d * ∑' y : Site d, r y ^ 2 *
        ∑' x : latticeSet ε U, jumpKernel (physical ε (y - (x : Site d)))) := by
      rw [show 2 * d = d + d by omega, pow_add]
      ring
    _ ≤ (ε ^ d / kappa d ε) * ((A * B) * L ^ 2 / ε ^ d) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (pow_nonneg hε.1.le _) hk)
    _ = (A * B) * L ^ 2 / kappa d ε := by
      field_simp [hε.1.ne']

/-- Disjoint supports give the pointwise boundary pairing identity. -/
lemma boundary_defect_product {ε : ℝ} {U : Set (Fin d → ℝ)}
    {r ψ : Site d → ℝ} (hr : ∀ x ∈ latticeSet ε U, r x = 0)
    (hψ : SupportedIn ε U ψ) (x : latticeSet ε U) (w : Site d) :
    r ((x : Site d) + w) * ψ x =
      (r ((x : Site d) + w) - r x) * (ψ x - ψ ((x : Site d) + w)) := by
  have hprod : r ((x : Site d) + w) * ψ ((x : Site d) + w) = 0 := by
    by_cases hx : (x : Site d) + w ∈ latticeSet ε U
    · rw [hr _ hx, zero_mul]
    · rw [hψ _ hx, mul_zero]
  rw [hr x x.property, sub_zero, mul_sub, hprod, sub_zero]

/-- Absolute convergence of the restricted boundary pairing follows from finite support. -/
lemma summable_boundary_pair {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hU : (latticeSet ε U).Finite) (a : Edge d → ℝ) {r : Site d → ℝ}
    (hr : Function.HasFiniteSupport r) (ψ : Site d → ℝ) :
    Summable (fun p : latticeSet ε U × Site d =>
      if hw : p.2 = 0 then 0 else
        a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
          r ((p.1 : Site d) + p.2) * ψ p.1) := by
  apply summable_of_hasFiniteSupport (boundary_endpoint_finite hU hr _ ?_)
  intro p hp
  split_ifs <;> simp only [hp, mul_zero, zero_mul]

/-- The pairing identity before (e.E1bd.CS), with both sums absolutely convergent. -/
theorem boundary_defect_pairing_eq {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hU : (latticeSet ε U).Finite) (a : Edge d → ℝ) {r ψ : Site d → ℝ}
    (hrf : Function.HasFiniteSupport r) (hr : ∀ x ∈ latticeSet ε U, r x = 0)
    (hψ : SupportedIn ε U ψ) :
    ε ^ d * ∑' x : latticeSet ε U, boundaryDefect ε a r x * ψ x =
      -(ε ^ (2 * d) / kappa d ε) * ∑' p : latticeSet ε U × Site d,
        if hw : p.2 = 0 then 0 else
          a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
            (r ((p.1 : Site d) + p.2) - r p.1) *
              (ψ p.1 - ψ ((p.1 : Site d) + p.2)) := by
  have hs := summable_boundary_pair hU a hrf ψ
  have he : ∀ p : latticeSet ε U × Site d,
      (if hw : p.2 = 0 then 0 else
        a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
          (r ((p.1 : Site d) + p.2) - r p.1) *
            (ψ p.1 - ψ ((p.1 : Site d) + p.2))) =
      (if hw : p.2 = 0 then 0 else
        a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
          r ((p.1 : Site d) + p.2) * ψ p.1) := by
    intro p
    split_ifs
    · rfl
    · have hp := boundary_defect_product hr hψ p.1 p.2
      simpa only [mul_assoc] using congrArg
        (fun t => a (edgeAdd p.1 p.2 ‹p.2 ≠ 0›) * jumpKernel (physical ε p.2) * t)
        hp.symm
  simp_rw [he]
  rw [hs.tsum_prod]
  have hx (x : latticeSet ε U) : boundaryDefect ε a r x * ψ x =
      -(ε ^ d / kappa d ε) * ∑' w : Site d,
        if hw : w = 0 then 0 else
          a (edgeAdd x w hw) * jumpKernel (physical ε w) *
            r ((x : Site d) + w) * ψ x := by
    unfold boundaryDefect
    rw [mul_assoc, ← tsum_mul_right]
    congr 1
    apply tsum_congr
    intro w
    split_ifs <;> simp only [zero_mul]
  simp_rw [hx]
  rw [tsum_mul_left]
  rw [show 2 * d = d + d by omega, pow_add]
  ring

/-- Nonnegativity of the Euclidean boundary kernel. -/
lemma boundary_kernel_nonneg (z : Fin d → ℝ) : 0 ≤ jumpKernel z := by
  unfold jumpKernel
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)

/-- The jump kernel is summable at each admissible scale. -/
lemma boundary_kernel_summable {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun w : Site d => jumpKernel (physical ε w)) := by
  classical
  obtain ⟨_, _, ht⟩ := kernel_tail_sum_bound d
  have htail := (ht ε hε).1
  let f := fun w : Site d => if w ∈ unitBallIndices d ε then
    jumpKernel (physical ε w) else 0
  have hf : Function.HasFiniteSupport f := by
    apply (unitBallIndices d ε).finite_toSet.subset
    intro w hw
    by_contra hn
    exact hw (if_neg hn)
  refine ((summable_of_hasFiniteSupport hf).add htail).of_nonneg_of_le
    (fun w => boundary_kernel_nonneg _) ?_
  intro w
  by_cases hw : w = 0
  · subst w
    simp [f, (physical_eq_zero_iff hε.1 0).mpr rfl, jumpKernel_zero]
  by_cases hr : radius (physical ε w) ≤ 1
  · have hm := (mem_unitBallIndices hε.1 w).mpr ⟨hw, hr⟩
    simp only [f, if_pos hm, if_neg (not_lt.mpr hr), add_zero, le_refl]
  · have hm : w ∉ unitBallIndices d ε := by
      intro h
      exact hr ((mem_unitBallIndices hε.1 w).mp h).2
    simp only [f, if_neg hm, if_pos (lt_of_not_ge hr), zero_add]
    exact le_mul_of_one_le_right (boundary_kernel_nonneg _)
      (by linarith [radius_nonneg (physical ε w)])

/-- The critical energy converges for a finitely supported test function. -/
lemma boundary_test_energy_summable {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    {ψ : Site d → ℝ} (hψ : Function.HasFiniteSupport ψ) :
    Summable (fun p : Site d × Site d => jumpKernel (physical ε p.2) *
      (ψ (p.1 + p.2) - ψ p.1) ^ 2) := by
  have hsq : Function.HasFiniteSupport (fun x => ψ x ^ 2) := by
    apply hψ.subset
    intro x hx hz
    exact hx (by simp only [hz, zero_pow (by decide : 2 ≠ 0)])
  have hs := (summable_of_hasFiniteSupport hsq).mul_of_nonneg
    (boundary_kernel_summable (d := d) hε)
    (fun x => sq_nonneg (ψ x)) (fun w => boundary_kernel_nonneg (physical ε w))
  let e : (Site d × Site d) ≃ (Site d × Site d) :=
    { toFun := fun p => (p.1 + p.2, p.2)
      invFun := fun p => (p.1 - p.2, p.2)
      left_inv := fun p => by ext <;> simp
      right_inv := fun p => by ext <;> simp }
  have ht := e.summable_iff.mpr hs
  have hdom := (ht.add hs).mul_left 2
  apply hdom.of_nonneg_of_le
  · intro p
    exact mul_nonneg (boundary_kernel_nonneg _) (sq_nonneg _)
  · intro p
    have hsq' : (ψ (p.1 + p.2) - ψ p.1) ^ 2 ≤
        2 * (ψ (p.1 + p.2) ^ 2 + ψ p.1 ^ 2) := by
      nlinarith only [sq_nonneg (ψ (p.1 + p.2) + ψ p.1)]
    dsimp [e, Function.comp_def]
    calc
      _ ≤ jumpKernel (physical ε p.2) *
          (2 * (ψ (p.1 + p.2) ^ 2 + ψ p.1 ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq' (boundary_kernel_nonneg _)
      _ = _ := by ring

/-- Weighted Cauchy--Schwarz on a finite set with an explicit coefficient bound. -/
lemma boundary_weighted_sum_le {ι : Type*} (s : Finset ι) (b k u v : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hk : ∀ i, 0 ≤ k i) (hb : ∀ i, |b i| ≤ c) :
    |∑ i ∈ s, b i * k i * u i * v i| ≤
      c * Real.sqrt (∑ i ∈ s, k i * u i ^ 2) *
        Real.sqrt (∑ i ∈ s, k i * v i ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Real.sqrt (k i) * |u i|) (fun i => Real.sqrt (k i) * |v i|)
  have he (i : ι) : (Real.sqrt (k i) * |u i|) *
      (Real.sqrt (k i) * |v i|) = k i * |u i| * |v i| := by
    calc
      _ = Real.sqrt (k i) ^ 2 * (|u i| * |v i|) := by ring
      _ = _ := by rw [Real.sq_sqrt (hk i)]; ring
  have hsquare (f : ι → ℝ) (i : ι) :
      (Real.sqrt (k i) * |f i|) ^ 2 = k i * f i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hk i), sq_abs]
  simp_rw [he, hsquare] at hcs
  calc
    _ ≤ ∑ i ∈ s, |b i * k i * u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, c * (k i * |u i| * |v i|) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [abs_mul, abs_of_nonneg (hk i)]
      calc
        _ = |b i| * (k i * |u i| * |v i|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hb i)
          (mul_nonneg (mul_nonneg (hk i) (abs_nonneg _)) (abs_nonneg _))
    _ = c * ∑ i ∈ s, k i * |u i| * |v i| := (Finset.mul_sum _ _ _).symm
    _ ≤ c * (Real.sqrt (∑ i ∈ s, k i * u i ^ 2) *
        Real.sqrt (∑ i ∈ s, k i * v i ^ 2)) := mul_le_mul_of_nonneg_left hcs hc
    _ = _ := by ring

/-- Cauchy--Schwarz bounds the pairing by the defect energy and critical test energy. -/
theorem boundary_defect_pairing_le (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {r ψ : Site d → ℝ}
    (hrf : Function.HasFiniteSupport r) (hr : ∀ x ∈ latticeSet ε U, r x = 0)
    (hψ : SupportedIn ε U ψ) :
    |ε ^ d * ∑' x : latticeSet ε U, boundaryDefect ε a r x * ψ x| ≤
      lam⁻¹ * Real.sqrt (boundaryDefectEnergy ε U r) * Real.sqrt (h1CritSq ε ψ) := by
  classical
  have hUf := latticeSet_finite hε.1 hU
  let k := fun p : latticeSet ε U × Site d => jumpKernel (physical ε p.2)
  let u := fun p : latticeSet ε U × Site d => r ((p.1 : Site d) + p.2)
  let v := fun p : latticeSet ε U × Site d => ψ p.1 - ψ ((p.1 : Site d) + p.2)
  let b := fun p : latticeSet ε U × Site d =>
    if hw : p.2 = 0 then 0 else a (edgeAdd p.1 p.2 hw)
  let t := ε ^ (2 * d) / kappa d ε
  have ht : 0 ≤ t := div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le
  have huf : Function.HasFiniteSupport u := boundary_endpoint_finite hUf hrf u
    (fun _ h => h)
  let s := huf.toFinset
  have hzero (p : latticeSet ε U × Site d) (hp : p ∉ s) : u p = 0 := by
    simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hp
  have hid : ε ^ d * ∑' x : latticeSet ε U, boundaryDefect ε a r x * ψ x =
      -t * ∑ p ∈ s, b p * k p * u p * v p := by
    rw [boundary_defect_pairing_eq hUf a hrf hr hψ]
    congr 1
    rw [tsum_eq_sum (s := s) (fun p hp => by
      have hz := hzero p hp
      dsimp [u] at hz
      rw [hr p.1 p.1.property, sub_zero, hz]
      split_ifs <;> simp only [mul_zero, zero_mul])]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [b, k, u, v]
    rw [hr p.1 p.1.property, sub_zero]
    split_ifs <;> simp only [zero_mul]
  have henergy : t * ∑ p ∈ s, k p * u p ^ 2 = boundaryDefectEnergy ε U r := by
    unfold boundaryDefectEnergy
    rw [tsum_eq_sum (s := s) (fun p hp => by
      have hz := hzero p hp
      dsimp [u] at hz
      simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero])]
  have hψf : Function.HasFiniteSupport ψ := by
    apply hUf.subset
    intro x hx
    by_contra hn
    exact hx (hψ x hn)
  have htest := boundary_test_energy_summable hε hψf
  let j := fun p : latticeSet ε U × Site d => ((p.1 : Site d), p.2)
  have hj : Function.Injective j := by
    intro p q hpq
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : Site d × Site d => z.1) hpq)
    · exact congrArg (fun z : Site d × Site d => z.2) hpq
  have hpartial : t * ∑ p ∈ s, k p * v p ^ 2 ≤ h1CritSq ε ψ := by
    unfold h1CritSq
    apply mul_le_mul_of_nonneg_left _ ht
    calc
      _ = ∑ p ∈ s.image j, jumpKernel (physical ε p.2) *
          (ψ (p.1 + p.2) - ψ p.1) ^ 2 := by
        rw [Finset.sum_image (fun p _ q _ h => hj h)]
        apply Finset.sum_congr rfl
        intro p _
        dsimp [k, v, j]
        rw [sub_sq_comm]
      _ ≤ _ := htest.sum_le_tsum _ (fun _ _ =>
        mul_nonneg (boundary_kernel_nonneg _) (sq_nonneg _))
  have hb (p : latticeSet ε U × Site d) : |b p| ≤ lam⁻¹ := by
    dsimp [b]
    split_ifs with hw
    · simpa only [abs_zero] using (inv_nonneg.mpr hlam.le)
    · rw [abs_of_nonneg (hlam.le.trans (ha _).1)]
      exact (ha _).2
  have hcs := boundary_weighted_sum_le s b k u v (inv_nonneg.mpr hlam.le)
    (fun _ => boundary_kernel_nonneg _) hb
  rw [hid, abs_mul, abs_neg, abs_of_nonneg ht]
  calc
    _ ≤ t * (lam⁻¹ * Real.sqrt (∑ p ∈ s, k p * u p ^ 2) *
        Real.sqrt (∑ p ∈ s, k p * v p ^ 2)) := mul_le_mul_of_nonneg_left hcs ht
    _ = lam⁻¹ * Real.sqrt (t * ∑ p ∈ s, k p * u p ^ 2) *
        Real.sqrt (t * ∑ p ∈ s, k p * v p ^ 2) := by
      rw [Real.sqrt_mul ht, Real.sqrt_mul ht]
      have hsq := Real.sq_sqrt ht
      calc
        _ = lam⁻¹ * (Real.sqrt t ^ 2 *
            (Real.sqrt (∑ p ∈ s, k p * u p ^ 2) *
              Real.sqrt (∑ p ∈ s, k p * v p ^ 2))) := by rw [hsq]; ring
        _ = _ := by ring
    _ ≤ lam⁻¹ * Real.sqrt (boundaryDefectEnergy ε U r) *
        Real.sqrt (h1CritSq ε ψ) := by
      rw [henergy]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpartial)
        (mul_nonneg (inv_nonneg.mpr hlam.le) (Real.sqrt_nonneg _))

/-- The pathwise boundary-defect bound (e.E1bd.bound), with explicit ellipticity factor. -/
theorem boundary_defect_bound (d : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ lam : ℝ, 0 < lam → ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (r : Site d → ℝ) (L : ℝ), 1 ≤ d →
        (∀ x ∈ latticeSet ε U, r x = 0) →
        (∀ y, R < radius (physical ε y) → r y = 0) →
        (∀ y, |r y| ≤ L * boundaryDistance ε U y) →
        ∀ ψ : Site d → ℝ, SupportedIn ε U ψ →
          |ε ^ d * ∑' x : latticeSet ε U, boundaryDefect ε a r x * ψ x| ≤
            lam⁻¹ * Real.sqrt (C * L ^ 2 / kappa d ε) *
              Real.sqrt (h1CritSq ε ψ) := by
  obtain ⟨C, hC, hc⟩ := boundaryDefectEnergy_le d R
  refine ⟨C, hC, ?_⟩
  intro ε hε lam hlam U hU a ha r L hd hr hR hdist ψ hψ
  have hrf : Function.HasFiniteSupport r := by
    apply (latticeSet_finite hε.1 (boundary_ball_bounded (d := d) R)).subset
    intro y hy
    exact le_of_not_gt (fun h => hy (hR y h))
  exact (boundary_defect_pairing_le hd hε hlam hU a ha hrf hr hψ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hc ε hε U hU r L hR hdist))
        (inv_nonneg.mpr hlam.le)) (Real.sqrt_nonneg _))

end
end LongRange
