import LongRange.Model.CorrectorEnergy
import LongRange.Corrector.Quadratic
import LongRange.Calculus.Green
import LongRange.Appendix.LatticeCount
import LongRange.Appendix.Kappa

/-!
# Solenoidal comparison for the corrector energy

Young's inequality bounds the Dirichlet functional below by a solenoidal pairing minus
its flux defect. Endpoint reversal cancels the pairing and bounds the touching-edge defect
by twice the defect with initial site in the domain.
-/

namespace LongRange

open Classical LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Absolute convergence of a real array with finitely many nonzero, summable rows. -/
private theorem summable_of_finite_rows {α β : Type*} {f : α × β → ℝ}
    {s : Set α} (hs : s.Finite) (hf : ∀ x ∈ s, Summable (fun y => f (x, y)))
    (hz : ∀ x ∉ s, ∀ y, f (x, y) = 0) : Summable f := by
  apply Summable.of_norm
  refine (summable_prod_of_nonneg (fun q => norm_nonneg (f q))).mpr ⟨?_, ?_⟩
  · intro x
    by_cases hx : x ∈ s
    · exact (hf x hx).norm
    · simpa only [hz x hx, norm_zero] using (summable_zero : Summable (fun _ : β => (0 : ℝ)))
  · apply summable_of_hasFiniteSupport
    apply hs.subset
    intro x hx
    by_contra hxs
    apply hx
    simp only [hz x hxs, norm_zero, tsum_zero]

/-- Pairing a solenoidal antisymmetric field with a supported increment gives zero. -/
theorem solenoidal_pairing_eq_zero {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hfinite : (latticeSet ε U).Finite) (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x)
    (hsol : ∀ x ∈ latticeSet ε U,
      Summable (fun z => g (x + z) x) ∧ ∑' z, g (x + z) x = 0)
    {w : Site d → ℝ} (hw : SupportedIn ε U w) :
    Summable (fun q : Site d × Site d =>
      g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) ∧
      ∑' q : Site d × Site d,
        g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1) = 0 := by
  let f : Site d × Site d → ℝ := fun q => g (q.1 + q.2) q.1 * w q.1
  have hf : Summable f := summable_of_finite_rows hfinite
    (fun x hx => (hsol x hx).1.mul_right (w x))
    (fun x hx z => by dsimp [f]; rw [hw x hx, mul_zero])
  have hr : Summable (fun q => f (edgeReverse d q)) :=
    (edgeReverse d).summable_iff.mpr hf
  have he (q : Site d × Site d) :
      g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1) =
        -f (edgeReverse d q) - f q := by
    dsimp [f, edgeReverse]
    rw [add_neg_cancel_right, hanti q.1 (q.1 + q.2)]
    ring
  have hz : ∑' q, f q = 0 := by
    rw [hf.tsum_prod]
    suffices hrow : ∀ x, (∑' z, f (x, z)) = 0 by
      simp only [hrow, tsum_zero]
    intro x
    by_cases hx : x ∈ latticeSet ε U
    · change (∑' z, g (x + z) x * w x) = 0
      rw [tsum_mul_right, (hsol x hx).2, zero_mul]
    · simp only [f, hw x hx, mul_zero, tsum_zero]
  constructor
  · exact (hr.neg.sub hf).congr (fun q => (he q).symm)
  · simp_rw [he]
    rw [hr.neg.tsum_sub hf, tsum_neg, (edgeReverse d).tsum_eq f, hz]
    ring

/-- Completing the square gives Young's bound with the lower conductance constant. -/
private theorem young_flux_bound {lam a J L G D : ℝ} (hlam : 0 < lam)
    (ha : lam ≤ a) (hJ : 0 < J) :
    2 * (G * D) - lam⁻¹ * (J⁻¹ * (G - a * J * L) ^ 2) ≤
      a * J * ((L + D) ^ 2 - L ^ 2) := by
  have ha0 : 0 < a := hlam.trans_le ha
  have hsq := sq_nonneg (a * J * D - (G - a * J * L))
  have hid : a * J * (a * J * ((L + D) ^ 2 - L ^ 2) - 2 * (G * D) +
      a⁻¹ * (J⁻¹ * (G - a * J * L) ^ 2)) =
      (a * J * D - (G - a * J * L)) ^ 2 := by
    field_simp [ha0.ne', hJ.ne']
    ring
  have hn : 0 ≤ a * J * ((L + D) ^ 2 - L ^ 2) - 2 * (G * D) +
      a⁻¹ * (J⁻¹ * (G - a * J * L) ^ 2) :=
    (mul_nonneg_iff_of_pos_left (mul_pos ha0 hJ)).mp (hid.symm ▸ hsq)
  have hi : a⁻¹ ≤ lam⁻¹ := inv_anti₀ hlam ha
  have hm := mul_le_mul_of_nonneg_right hi
    (mul_nonneg (inv_nonneg.mpr hJ.le) (sq_nonneg (G - a * J * L)))
  linarith

/-- Reversing the physical linear increment changes its sign. -/
private theorem linearFn_neg_increment (ε : ℝ) (p : Fin d → ℝ) (z : Site d) :
    linearFn ε p (-z) = -linearFn ε p z := by
  simp only [linearFn, physical_neg, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-- The squared flux defect on a directed edge, including its inverse kernel weight. -/
private def fluxDefect (ε : ℝ) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (g : Site d → Site d → ℝ) (q : Site d × Site d) : ℝ :=
  if hw : q.2 = 0 then 0 else
    (jumpKernel (physical ε q.2))⁻¹ *
      (g (q.1 + q.2) q.1 - a (edgeAdd q.1 q.2 hw) *
        jumpKernel (physical ε q.2) * linearFn ε p q.2) ^ 2

/-- Antisymmetry makes the squared defect invariant under endpoint reversal. -/
private theorem fluxDefect_reverse (ε : ℝ) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (g : Site d → Site d → ℝ) (hanti : ∀ x y, g x y = -g y x)
    (q : Site d × Site d) :
    fluxDefect ε a p g (edgeReverse d q) = fluxDefect ε a p g q := by
  rcases q with ⟨x, z⟩
  by_cases hz : z = 0
  · simp only [fluxDefect, edgeReverse, Equiv.coe_fn_mk, hz, neg_zero, ↓reduceDIte]
  · simp only [fluxDefect, edgeReverse, Equiv.coe_fn_mk, neg_eq_zero, hz,
      ↓reduceDIte, add_neg_cancel_right, physical_neg, jumpKernel_neg,
      linearFn_neg_increment, hanti x (x + z)]
    rw [edgeAdd_reverse x z hz]
    ring

/-- The inverse-kernel weighted squared defect is nonnegative. -/
private theorem fluxDefect_nonneg (ε : ℝ) (a : Edge d → ℝ) (p : Fin d → ℝ)
    (g : Site d → Site d → ℝ) (q : Site d × Site d) : 0 ≤ fluxDefect ε a p g q := by
  unfold fluxDefect
  split
  · exact le_rfl
  · exact mul_nonneg (inv_nonneg.mpr (jumpKernel_nonneg _)) (sq_nonneg _)

/-- Every supported competitor is bounded below by the solenoidal flux defect. -/
private theorem correctorFunctional_lower_bound (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    (g : Site d → Site d → ℝ) (hanti : ∀ x y, g x y = -g y x)
    (hsol : ∀ x ∈ latticeSet ε U,
      Summable (fun z => g (x + z) x) ∧ ∑' z, g (x + z) x = 0)
    (hres : Summable (fun q : Site d × Site d =>
      if q.1 ∈ latticeSet ε U then fluxDefect ε a p g q else 0))
    {w : Site d → ℝ} (hw : SupportedIn ε U w) :
    -(lam⁻¹ * (ε ^ (2 * d) / kappa d ε) * ∑' q : Site d × Site d,
      if q.1 ∈ latticeSet ε U then fluxDefect ε a p g q else 0) ≤
      correctorFunctional ε U a p w := by
  let R : Site d × Site d → ℝ := fun q =>
    if q.1 ∈ latticeSet ε U then fluxDefect ε a p g q else 0
  have hR : Summable R := hres
  have hr : Summable (fun q => R (edgeReverse d q)) :=
    (edgeReverse d).summable_iff.mpr hR
  have hn (q) : 0 ≤ R q := by
    dsimp [R]
    split
    · exact fluxDefect_nonneg ε a p g q
    · exact le_rfl
  have hc := solenoidal_pairing_eq_zero (latticeSet_finite hε.1 hU) g hanti hsol hw
  have hs := summable_correctorFunctional hd hε.1 hU hlam ha p hw
  have hl := (hc.1.mul_left 2).sub ((hR.add hr).mul_left lam⁻¹)
  have hpoint (q : Site d × Site d) :
      2 * (g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) -
        lam⁻¹ * (R q + R (edgeReverse d q)) ≤
      (if hz : q.2 = 0 then 0 else
        if q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U then
          a (edgeAdd q.1 q.2 hz) * jumpKernel (physical ε q.2) *
            ((linearFn ε p q.2 + w (q.1 + q.2) - w q.1) ^ 2 -
              linearFn ε p q.2 ^ 2) else 0) := by
    by_cases hz : q.2 = 0
    · simp only [hz, add_zero, sub_self, mul_zero, zero_sub, ↓reduceDIte]
      exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr hlam.le)
        (add_nonneg (hn q) (hn (edgeReverse d q))))
    · simp only [hz, ↓reduceDIte]
      by_cases hq : q.1 ∈ latticeSet ε U ∨ q.1 + q.2 ∈ latticeSet ε U
      · simp only [hq, ↓reduceIte]
        have hJ : 0 < jumpKernel (physical ε q.2) := by
          rw [jumpKernel_of_ne_zero (fun h => hz ((physical_eq_zero_iff hε.1 _).mp h))]
          exact inv_pos.mpr (pow_pos (radius_pos
            (fun h => hz ((physical_eq_zero_iff hε.1 _).mp h))) _)
        have hy := young_flux_bound hlam (ha (edgeAdd q.1 q.2 hz)).1 hJ
          (L := linearFn ε p q.2) (G := g (q.1 + q.2) q.1)
          (D := w (q.1 + q.2) - w q.1)
        have hdef : fluxDefect ε a p g q ≤ R q + R (edgeReverse d q) := by
          rcases hq with hx | hx
          · have he : R q = fluxDefect ε a p g q := if_pos hx
            rw [he]
            exact le_add_of_nonneg_right (hn _)
          · have he : R (edgeReverse d q) = fluxDefect ε a p g q := by
              dsimp [R, edgeReverse]
              rw [if_pos hx]
              exact fluxDefect_reverse ε a p g hanti q
            rw [he]
            exact le_add_of_nonneg_left (hn _)
        have hm := mul_le_mul_of_nonneg_left hdef (inv_nonneg.mpr hlam.le)
        simp only [fluxDefect, hz, ↓reduceDIte] at hm
        have he : linearFn ε p q.2 + w (q.1 + q.2) - w q.1 =
            linearFn ε p q.2 + (w (q.1 + q.2) - w q.1) := by ring
        rw [he]
        exact (sub_le_sub_left hm _).trans hy
      · simp only [hq, ↓reduceIte]
        push Not at hq
        rw [hw _ hq.1, hw _ hq.2, sub_self, mul_zero, mul_zero, zero_sub]
        exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr hlam.le)
          (add_nonneg (hn q) (hn (edgeReverse d q))))
  have hsum := hl.tsum_le_tsum hpoint hs
  rw [Summable.tsum_sub (hc.1.mul_left 2) ((hR.add hr).mul_left lam⁻¹),
    tsum_mul_left, hc.2, mul_zero, zero_sub, tsum_mul_left,
    hR.tsum_add hr, (edgeReverse d).tsum_eq R] at hsum
  have hscale : 0 ≤ ε ^ (2 * d) / (2 * kappa d ε) :=
    div_nonneg (pow_nonneg hε.1.le _) (mul_nonneg (by norm_num) (kappa_pos hd hε).le)
  have hbound := mul_le_mul_of_nonneg_left hsum hscale
  unfold correctorFunctional
  calc
    _ = (ε ^ (2 * d) / (2 * kappa d ε)) *
        -(lam⁻¹ * ((∑' q, R q) + ∑' q, R q)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    _ ≤ _ := hbound

/-- Proposition 3.3, Step 1: any antisymmetric solenoidal field bounds the corrector energy
by its inverse-kernel weighted squared flux defect. -/
theorem correctorEnergy_le_of_solenoidal {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (p : Fin d → ℝ) (g : Site d → Site d → ℝ) (hanti : ∀ x y, g x y = -g y x)
    (hsol : ∀ x ∈ latticeSet ε U, Summable (fun z => g (x + z) x) ∧
      ∑' z, g (x + z) x = 0)
    (hres : Summable (fun q : Site d × Site d => if hw : q.2 = 0 then 0 else
      if q.1 ∈ latticeSet ε U then (jumpKernel (physical ε q.2))⁻¹ *
        (g (q.1 + q.2) q.1 - a (edgeAdd q.1 q.2 hw) * jumpKernel (physical ε q.2) *
          linearFn ε p q.2) ^ 2 else 0)) :
    correctorEnergy ε U a p ≤ lam⁻¹ * (ε ^ (2 * d) / kappa d ε) * ∑' q : Site d × Site d,
      (if hw : q.2 = 0 then 0 else if q.1 ∈ latticeSet ε U then
        (jumpKernel (physical ε q.2))⁻¹ * (g (q.1 + q.2) q.1 - a (edgeAdd q.1 q.2 hw) *
          jumpKernel (physical ε q.2) * linearFn ε p q.2) ^ 2 else 0) := by
  have he (q : Site d × Site d) :
      (if hw : q.2 = 0 then 0 else if q.1 ∈ latticeSet ε U then
        (jumpKernel (physical ε q.2))⁻¹ * (g (q.1 + q.2) q.1 - a (edgeAdd q.1 q.2 hw) *
          jumpKernel (physical ε q.2) * linearFn ε p q.2) ^ 2 else 0) =
      (if q.1 ∈ latticeSet ε U then fluxDefect ε a p g q else 0) := by
    by_cases hz : q.2 = 0 <;> by_cases hx : q.1 ∈ latticeSet ε U <;>
      simp only [fluxDefect, hz, hx, ↓reduceDIte, ↓reduceIte]
  simp_rw [he] at hres ⊢
  unfold correctorEnergy
  rw [neg_le]
  apply le_csInf
  · exact ⟨_, ⟨⟨(fun _ => 0), fun _ _ => rfl⟩, rfl⟩⟩
  · rintro _ ⟨w, rfl⟩
    exact correctorFunctional_lower_bound hd hε hU hlam ha p g hanti hsol hres w.property

/-- The constant-conductance background flux at the physical displacement of its endpoints. -/
def backgroundFlux (ε : ℝ) (p : Fin d → ℝ) (x y : Site d) : ℝ :=
  jumpKernel (physical ε (x - y)) * linearFn ε p (x - y)

/-- The background flux is antisymmetric in its two endpoints. -/
theorem backgroundFlux_antisymmetric (ε : ℝ) (p : Fin d → ℝ) (x y : Site d) :
    backgroundFlux ε p x y = -backgroundFlux ε p y x := by
  unfold backgroundFlux
  rw [show x - y = -(y - x) by abel, physical_neg, jumpKernel_neg,
    linearFn_neg_increment, mul_neg]

/-- The background field has absolutely convergent, zero divergence at every site. -/
theorem backgroundFlux_solenoidal (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (p : Fin d → ℝ) (x : Site d) :
    Summable (fun z => backgroundFlux ε p (x + z) x) ∧
      ∑' z, backgroundFlux ε p (x + z) x = 0 := by
  have hs : Summable (fun z : Site d =>
      jumpKernel (physical ε z) * linearFn ε p z) := by
    refine ((summable_jumpKernel_firstMoment hd hε).mul_left (∑ i, |p i|)).of_norm_bounded ?_
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (jumpKernel_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (abs_linearFn_le ε p z)
      (jumpKernel_nonneg _)).trans_eq (by ring)
  simp only [backgroundFlux, add_sub_cancel_left]
  refine ⟨hs, ?_⟩
  have he := (Equiv.neg (Site d)).tsum_eq
    (fun z => jumpKernel (physical ε z) * linearFn ε p z)
  simp only [Equiv.neg_apply, physical_neg, jumpKernel_neg,
    linearFn_neg_increment, mul_neg, tsum_neg] at he
  linarith

/-- For unit conductance the background flux defect vanishes on every nonzero edge. -/
theorem backgroundFlux_residual_zero (ε : ℝ) (p : Fin d → ℝ) (x z : Site d) :
    backgroundFlux ε p (x + z) x - (1 : ℝ) * jumpKernel (physical ε z) *
      linearFn ε p z = 0 := by
  simp only [backgroundFlux, add_sub_cancel_left, one_mul, sub_self]

/-- A nonvacuous application of the solenoidal comparison: unit conductance has
nonpositive corrector energy, for every physical slope and bounded domain. -/
theorem correctorEnergy_unit_nonpos (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (p : Fin d → ℝ) :
    correctorEnergy ε U (fun _ => 1) p ≤ 0 := by
  let r : Site d × Site d → ℝ := fun q => if hz : q.2 = 0 then 0 else
    if q.1 ∈ latticeSet ε U then (jumpKernel (physical ε q.2))⁻¹ *
      (backgroundFlux ε p (q.1 + q.2) q.1 - (1 : ℝ) * jumpKernel (physical ε q.2) *
        linearFn ε p q.2) ^ 2 else 0
  have hzres (q : Site d × Site d) : r q = 0 := by
    dsimp only [r]
    split
    · rfl
    · split
      · rw [backgroundFlux_residual_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      · rfl
  have hr : Summable r := summable_zero.congr (fun q => (hzres q).symm)
  have hb := correctorEnergy_le_of_solenoidal hd hε hU (lam := 1) zero_lt_one
    (a := fun _ => 1) (fun _ => by norm_num) p (backgroundFlux ε p)
    (backgroundFlux_antisymmetric ε p) (fun x _ => backgroundFlux_solenoidal hd hε.1 p x) hr
  change correctorEnergy ε U (fun _ => 1) p ≤
    (1 : ℝ)⁻¹ * (ε ^ (2 * d) / kappa d ε) * ∑' q, r q at hb
  simpa only [hzres, tsum_zero, mul_zero] using hb

end

end LongRange
