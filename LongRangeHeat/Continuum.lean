import LongRangeHeat.Defs
import LatticeProb.Analysis.HeatDuhamel

/-!
# The continuum solution

For `f ∈ C_c^∞(ℝ^d)`, the solution `ū = continuumHeat f` of (1.5) is, at every positive time, the
convolution `Φ_t * f` of `f` with the heat kernel `Φ_t` of `(2d)⁻¹ Δ`. This file shows:

* `contDiff_continuumHeat`: `ū(t, ·)` is smooth for every `t ≥ 0`;
* `multiDeriv_continuumHeat`: spatial derivatives commute with the heat flow,
  `∂^β ū(t, ·) = Φ_t * ∂^β f`, where `∂^β` is the iterated partial derivative `multiDeriv β`;
* `hasDerivAt_continuumHeat`: for `t > 0`, `∂_t ū(t, x) = (2d)⁻¹ Δ ū(t, x)`;
* `hasDerivWithinAt_continuumHeat_zero`: the right derivative at `t = 0` is `(2d)⁻¹ Δ f`.

The operator `(2d)⁻¹ Δ` is `LatticeProb.WhiteNoise.contOp d`.
-/

namespace LongRangeHeat

open MeasureTheory Filter Topology Set LatticeProb.Heat LatticeProb.WhiteNoise
open scoped ContDiff Convolution

noncomputable section

variable {d : ℕ}

/-- The partial derivative `∂_i g` in the direction of the `i`-th basis vector. -/
def coordDeriv (i : Fin d) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single i 1)

/-- The iterated partial derivative `∂^β g = ∂_0^{β_0} ⋯ ∂_{d-1}^{β_{d-1}} g` of a multi-index
`β`. -/
def multiDeriv (β : Fin d → ℕ) (g : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  (List.finRange d).foldr (fun i h => (coordDeriv i)^[β i] h) g

/-- An operator that commutes with every partial derivative on a class of functions closed under
partial derivatives commutes with every iterated partial derivative on that class. -/
theorem multiDeriv_comm {P : ((Fin d → ℝ) → ℝ) → Prop}
    {T : ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ}
    (hP : ∀ i g, P g → P (coordDeriv i g))
    (hT : ∀ i g, P g → coordDeriv i (T g) = T (coordDeriv i g))
    (β : Fin d → ℕ) {g : (Fin d → ℝ) → ℝ} (hg : P g) :
    multiDeriv β (T g) = T (multiDeriv β g) ∧ P (multiDeriv β g) := by
  have hiter : ∀ (i : Fin d) (n : ℕ) (h : (Fin d → ℝ) → ℝ), P h →
      (coordDeriv i)^[n] (T h) = T ((coordDeriv i)^[n] h) ∧ P ((coordDeriv i)^[n] h) := by
    intro i n
    induction n with
    | zero => intro h hh; exact ⟨rfl, hh⟩
    | succ n ih =>
      intro h hh
      obtain ⟨h1, h2⟩ := ih h hh
      simp only [Function.iterate_succ_apply']
      exact ⟨by rw [h1, hT i _ h2], hP i _ h2⟩
  unfold multiDeriv
  induction List.finRange d with
  | nil => exact ⟨rfl, hg⟩
  | cons i l ih =>
    simp only [List.foldr_cons]
    obtain ⟨h1, h2⟩ := ih
    rw [h1]
    exact hiter i (β i) _ h2

/-- A property preserved by partial derivatives is preserved by iterated partial derivatives. -/
theorem multiDeriv_induction {P : ((Fin d → ℝ) → ℝ) → Prop}
    (hP : ∀ i g, P g → P (coordDeriv i g)) (β : Fin d → ℕ) {g : (Fin d → ℝ) → ℝ} (hg : P g) :
    P (multiDeriv β g) :=
  (multiDeriv_comm (T := id) hP (fun _ _ _ => rfl) β hg).2

theorem contDiff_coordDeriv {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    ContDiff ℝ ∞ (coordDeriv i g) :=
  contDiff_fderiv_apply hg _

theorem hasCompactSupport_coordDeriv {g : (Fin d → ℝ) → ℝ} (hgc : HasCompactSupport g)
    (i : Fin d) : HasCompactSupport (coordDeriv i g) :=
  hgc.fderiv_apply (𝕜 := ℝ) _

/-- Iterated partial derivatives of a smooth compactly supported function are smooth and
compactly supported. -/
theorem contDiff_multiDeriv {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (β : Fin d → ℕ) :
    ContDiff ℝ ∞ (multiDeriv β g) ∧ HasCompactSupport (multiDeriv β g) :=
  multiDeriv_induction (P := fun g => ContDiff ℝ ∞ g ∧ HasCompactSupport g)
    (fun i _ h => ⟨contDiff_coordDeriv h.1 i, hasCompactSupport_coordDeriv h.2 i⟩) β ⟨hg, hgc⟩

theorem continuumHeat_zero (f : (Fin d → ℝ) → ℝ) : continuumHeat f 0 = f := by
  funext x
  simp [continuumHeat]

/-- At positive time the continuum solution is the convolution with the heat kernel. -/
theorem continuumHeat_of_pos (f : (Fin d → ℝ) → ℝ) {t : ℝ} (ht : 0 < t) :
    continuumHeat f t = heatKernel d t ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := by
  funext x
  rw [convolution_eq_swap]
  simp [continuumHeat, ht.ne']

/-- The convolution form `ū(t, x) = ∫ Φ_t(w) f(x - w) dw` at positive time. -/
theorem continuumHeat_eq_integral (f : (Fin d → ℝ) → ℝ) {t : ℝ} (ht : 0 < t)
    (x : Fin d → ℝ) : continuumHeat f t x = ∫ w, heatKernel d t w * f (x - w) := by
  rw [continuumHeat_of_pos f ht, convolution_def]
  simp

theorem locallyIntegrable_heatKernel (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    LocallyIntegrable (heatKernel d t) volume :=
  (integrable_heatKernel hd ht).locallyIntegrable

/-- `ū(t, ·)` is smooth for every `t ≥ 0`. -/
theorem contDiff_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (continuumHeat f t) := by
  rcases ht.eq_or_lt with rfl | ht
  · rwa [continuumHeat_zero]
  · rw [continuumHeat_of_pos f ht]
    exact hfc.contDiff_convolution_right _ (locallyIntegrable_heatKernel hd ht) hf

/-- Directional derivatives commute with the heat flow. -/
theorem fderiv_continuumHeat_apply (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (x v : Fin d → ℝ) :
    fderiv ℝ (continuumHeat f t) x v = continuumHeat (fun y => fderiv ℝ f y v) t x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [continuumHeat_zero]
  · rw [continuumHeat_of_pos f ht, continuumHeat_of_pos _ ht]
    exact fderiv_convolution_apply (locallyIntegrable_heatKernel hd ht) hf hfc x v

theorem coordDeriv_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (i : Fin d) :
    coordDeriv i (continuumHeat f t) = continuumHeat (coordDeriv i f) t := by
  funext x
  exact fderiv_continuumHeat_apply hd hf hfc ht x _

/-- `∂^β ū(t, ·) = Φ_t * ∂^β f`: iterated partial derivatives commute with the heat flow. -/
theorem multiDeriv_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (β : Fin d → ℕ) :
    multiDeriv β (continuumHeat f t) = continuumHeat (multiDeriv β f) t :=
  (multiDeriv_comm (P := fun g => ContDiff ℝ ∞ g ∧ HasCompactSupport g)
    (T := fun g => continuumHeat g t)
    (fun i _ h => ⟨contDiff_coordDeriv h.1 i, hasCompactSupport_coordDeriv h.2 i⟩)
    (fun i _ h => coordDeriv_continuumHeat hd h.1 h.2 ht i) β ⟨hf, hfc⟩).1

/-- The second directional derivative of a `C²` function. -/
theorem fderiv_fderiv_apply_eq {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ 2 g) (x w v : Fin d → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- Second directional derivatives commute with the heat flow. -/
theorem fderiv_fderiv_continuumHeat_apply (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (x w v : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ (continuumHeat f t)) x w v =
      continuumHeat (fun y => fderiv ℝ (fderiv ℝ f) y w v) t x := by
  have hu := contDiff_continuumHeat hd hf hfc ht
  have hfv : ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) := contDiff_fderiv_apply hf v
  have hfvc : HasCompactSupport (fun y => fderiv ℝ f y v) := hfc.fderiv_apply (𝕜 := ℝ) v
  rw [← fderiv_fderiv_apply_eq (hu.of_le (by simp))]
  have h1 : (fun y => fderiv ℝ (continuumHeat f t) y v) =
      continuumHeat (fun y => fderiv ℝ f y v) t := by
    funext y
    exact fderiv_continuumHeat_apply hd hf hfc ht y v
  rw [h1, fderiv_continuumHeat_apply hd hfv hfvc ht x w]
  congr 1
  funext y
  exact fderiv_fderiv_apply_eq (hf.of_le (by simp)) y w v

/-- The Laplacian as the sum of the second partial derivatives. -/
theorem lap_eq_sum_coordDeriv {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (x : Fin d → ℝ) :
    lap g x = ∑ i, coordDeriv i (coordDeriv i g) x := by
  rw [lap_eq_sum_fderiv hg]
  rfl

/-- The heat flow is linear on continuous compactly supported functions. -/
theorem continuumHeat_finset_sum {ι : Type*} (s : Finset ι) {g : ι → (Fin d → ℝ) → ℝ}
    (hg : ∀ i ∈ s, Continuous (g i)) (hgc : ∀ i ∈ s, HasCompactSupport (g i)) (t : ℝ)
    (x : Fin d → ℝ) :
    continuumHeat (fun y => ∑ i ∈ s, g i y) t x = ∑ i ∈ s, continuumHeat (g i) t x := by
  unfold continuumHeat
  split_ifs with ht
  · rfl
  · simp_rw [Finset.mul_sum]
    refine integral_finsetSum s fun i hi => ?_
    have hk : Continuous (fun y => heatKernel d t (x - y)) := by
      rcases le_or_gt t 0 with ht' | ht'
      · simp only [heatKernel_of_nonpos ht']
        exact continuous_const
      · exact (continuous_heatKernel ht').comp (continuous_const.sub continuous_id)
    exact (hk.mul (hg i hi)).integrable_of_hasCompactSupport (hgc i hi).mul_left

theorem continuumHeat_const_mul (c : ℝ) (g : (Fin d → ℝ) → ℝ) (t : ℝ) (x : Fin d → ℝ) :
    continuumHeat (fun y => c * g y) t x = c * continuumHeat g t x := by
  unfold continuumHeat
  split_ifs
  · rfl
  · rw [← integral_const_mul]
    congr 1
    funext y
    ring

/-- The operator `(2d)⁻¹ Δ` commutes with the heat flow. -/
theorem contOp_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    contOp d (continuumHeat f t) x = continuumHeat (contOp d f) t x := by
  have hcd : ∀ i, ContDiff ℝ ∞ (coordDeriv i (coordDeriv i f)) := fun i =>
    contDiff_coordDeriv (contDiff_coordDeriv hf i) i
  have hcc : ∀ i, HasCompactSupport (coordDeriv i (coordDeriv i f)) := fun i =>
    hasCompactSupport_coordDeriv (hasCompactSupport_coordDeriv hfc i) i
  have hop : contOp d f = fun y => (1 / (2 * d)) * ∑ i, coordDeriv i (coordDeriv i f) y := by
    funext y
    rw [contOp, lap_eq_sum_coordDeriv hf]
    ring
  rw [hop, continuumHeat_const_mul,
    continuumHeat_finset_sum _ (fun i _ => (hcd i).continuous) (fun i _ => hcc i), contOp,
    lap_eq_sum_coordDeriv (contDiff_continuumHeat hd hf hfc ht)]
  have h2 : ∀ i, coordDeriv i (coordDeriv i (continuumHeat f t)) =
      continuumHeat (coordDeriv i (coordDeriv i f)) t := fun i => by
    rw [coordDeriv_continuumHeat hd hf hfc ht,
      coordDeriv_continuumHeat hd (contDiff_coordDeriv hf i) (hasCompactSupport_coordDeriv hfc i)
        ht]
  simp_rw [h2]
  ring

/-- At positive time the solution solves the heat equation: `∂_t ū(t, x) = (2d)⁻¹ Δ ū(t, x)`. -/
theorem hasDerivAt_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    HasDerivAt (fun s => continuumHeat f s x) (contOp d (continuumHeat f t) x) t := by
  let χ : ContDiffBump (1 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let v : ℝ × (Fin d → ℝ) → ℝ := fun p => χ p.1 * f p.2
  have hv : ContDiff ℝ ∞ v := (χ.contDiff.comp contDiff_fst).mul (hf.comp contDiff_snd)
  have hvc : HasCompactSupport v := by
    refine HasCompactSupport.intro (χ.hasCompactSupport.isCompact.prod hfc.isCompact)
      fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport χ ∧ p.2 ∈ tsupport f) from hp) with h | h
    · simp [v, image_eq_zero_of_notMem_tsupport h]
    · simp [v, image_eq_zero_of_notMem_tsupport h]
  have hχ1 : ∀ r, |r - 1| ≤ 1 / 2 → χ r = 1 := fun r hr =>
    χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq]; exact hr)
  have hχev : (χ : ℝ → ℝ) =ᶠ[𝓝 1] fun _ => 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
      with r hr
    exact hχ1 r (by rwa [Metric.mem_closedBall, Real.dist_eq] at hr)
  have hD := hasDerivAt_integral_heatKernel_mul hd hv hvc (s := 1) (t := t + 1)
    (by linarith) x
  have hD' := hD.comp_of_eq t ((hasDerivAt_id t).const_sub (t + 1)) (by simp)
  have hsrc : ∀ y, heatSource d v (1, y) = -contOp d f y := by
    intro y
    have hderiv : deriv (fun r => v (r, y)) 1 = 0 := by
      have : (fun r => v (r, y)) =ᶠ[𝓝 1] fun _ => f y := by
        filter_upwards [hχev] with r hr
        simp [v, hr]
      rw [this.deriv_eq]
      simp
    have hslice : (fun z => v (1, z)) = f := by
      funext z
      simp [v, hχ1 1 (by norm_num)]
    simp [heatSource, hderiv, hslice]
  refine (hD'.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioi_mem_nhds ht,
      Metric.closedBall_mem_nhds t (by norm_num : (0 : ℝ) < 1 / 2)] with s hs hs'
    rw [Metric.mem_closedBall, Real.dist_eq] at hs'
    have hχs : χ (t + 1 - s) = 1 :=
      hχ1 _ (by rw [show t + 1 - s - 1 = -(s - t) by ring, abs_neg]; exact hs')
    show continuumHeat f s x =
      ∫ y, heatKernel d (t + 1 - (t + 1 - s)) (x - y) * (χ (t + 1 - s) * f y)
    rw [hχs, show t + 1 - (t + 1 - s) = s by ring]
    simp [continuumHeat, (ne_of_gt (show 0 < s from hs))]
  · simp only [hsrc, mul_neg, integral_neg, show t + 1 - 1 = t by ring]
    rw [contOp_continuumHeat hd hf hfc ht.le]
    simp [continuumHeat, ht.ne']

/-- Continuity of the heat flow at `t = 0` for continuous compactly supported data. -/
theorem tendsto_continuumHeat (hd : 1 ≤ d) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : Fin d → ℝ) :
    Tendsto (fun s => continuumHeat g s x) (𝓝[>] 0) (𝓝 (g x)) := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg
  refine (tendsto_integral_heatKernel_mul hd hg ⟨M, fun y => by simpa using hM y⟩ x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (continuumHeat_eq_integral g hs x).symm

/-- At `t = 0` the right derivative of the solution is `(2d)⁻¹ Δ f`. -/
theorem hasDerivWithinAt_continuumHeat_zero (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : Fin d → ℝ) :
    HasDerivWithinAt (fun s => continuumHeat f s x) (contOp d f x) (Ici 0) 0 := by
  have hderiv : ∀ s, 0 < s → HasDerivAt (fun s => continuumHeat f s x)
      (continuumHeat (contOp d f) s x) s := fun s hs => by
    have h := hasDerivAt_continuumHeat hd hf hfc hs x
    rwa [contOp_continuumHeat hd hf hfc hs.le] at h
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt) ?_
    self_mem_nhdsWithin ?_
  · have h := tendsto_continuumHeat hd hf.continuous hfc x
    rw [ContinuousWithinAt, continuumHeat_zero]
    exact h
  · refine (tendsto_continuumHeat hd (contDiff_contOp hf).continuous
      (hasCompactSupport_contOp hf hfc) x).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hderiv s hs).deriv.symm

/-- The right time derivative at every `t ≥ 0`: `∂_t⁺ ū(t, x) = (2d)⁻¹ Δ ū(t, x)`. -/
theorem hasDerivWithinAt_continuumHeat (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    HasDerivWithinAt (fun s => continuumHeat f s x) (contOp d (continuumHeat f t) x) (Ici t) t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [continuumHeat_zero]
    exact hasDerivWithinAt_continuumHeat_zero hd hf hfc x
  · exact (hasDerivAt_continuumHeat hd hf hfc ht x).hasDerivWithinAt

end

end LongRangeHeat
