import LongRange.Dirichlet.Field

/-!
# Coefficients of the flux defect

The flux defect is a summable linear combination of centred edge conductances.
Its coefficients split into short and long physical displacements.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Coefficient of the centred conductance of `r` in the flux defect `Σ_p(x+z, x)`. -/
def defectCoeff (ε : ℝ) (U : Set (Fin d → ℝ)) (p : Fin d → ℝ) (x z : Site d)
    (r : Cycle.indexSet ε U) : ℝ :=
  jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
      (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ) -
    if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
      jumpKernel (physical ε z) * linearFn ε p z else 0

/-- An indicator of the two orientations of an edge has finite support. -/
lemma summable_edge_indicator (ε : ℝ) (U : Set (Fin d → ℝ)) (x z : Site d)
    (f : Cycle.indexSet ε U → ℝ) :
    Summable (fun r : Cycle.indexSet ε U =>
      if r.1 = (x, z) ∨ r.1 = (x + z, -z) then f r else 0) := by
  classical
  apply summable_of_hasFiniteSupport
  apply (((Set.finite_singleton (x, z)).union
    (Set.finite_singleton (x + z, -z))).preimage Subtype.val_injective.injOn).subset
  intro r hr
  simp only [Function.mem_support, ne_eq] at hr
  simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff]
  by_contra hn
  exact hr (if_neg hn)

/-- The cycle correction is summable on a fixed observation edge. -/
lemma summable_cycle_coefficient (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    {a : Edge d → ℝ} {A : ℝ} (ha : ∀ e, |a e| ≤ A)
    (m : ℝ) (p : Fin d → ℝ) (x z : Site d) :
    Summable (fun r : Cycle.indexSet ε U =>
      (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
        jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
          (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)) := by
  apply Summable.of_abs
  exact (summable_field_correction_prod hd hε hU ha m p x).comp_injective
    (i := fun r => (r, x + z)) (fun _ _ h => congrArg Prod.fst h)

/-- The deterministic coefficients of the flux defect are summable. -/
theorem summable_defectCoeff (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (p : Fin d → ℝ) (x z : Site d) : Summable (defectCoeff ε U p x z) := by
  have hc := summable_cycle_coefficient hd hε hU
    (a := fun _ => 1) (A := 1) (fun _ => by norm_num) 0 p x z
  simp only [sub_zero, one_mul] at hc
  exact hc.sub (summable_edge_indicator ε U x z (fun _ =>
    jumpKernel (physical ε z) * linearFn ε p z))

/-- The coefficient supported on physical displacements strictly less than one. -/
def shortCoeff (ε : ℝ) (U : Set (Fin d → ℝ)) (p : Fin d → ℝ) (x z : Site d)
    (r : Cycle.indexSet ε U) : ℝ :=
  if radius (physical ε r.1.2) < 1 then defectCoeff ε U p x z r else 0

/-- The coefficient supported on physical displacements at least one. -/
def longCoeff (ε : ℝ) (U : Set (Fin d → ℝ)) (p : Fin d → ℝ) (x z : Site d)
    (r : Cycle.indexSet ε U) : ℝ :=
  if 1 ≤ radius (physical ε r.1.2) then defectCoeff ε U p x z r else 0

/-- The short and long coefficients partition the defect coefficient. -/
theorem defectCoeff_eq_short_add_long (ε : ℝ) (U : Set (Fin d → ℝ))
    (p : Fin d → ℝ) (x z : Site d) (r : Cycle.indexSet ε U) :
    defectCoeff ε U p x z r = shortCoeff ε U p x z r + longCoeff ε U p x z r := by
  by_cases h : radius (physical ε r.1.2) < 1
  · simp only [shortCoeff, longCoeff, if_pos h, if_neg (not_le.mpr h), add_zero]
  · simp only [shortCoeff, longCoeff, if_neg h, if_pos (le_of_not_gt h), zero_add]

/-- Restricting the summable defect coefficients to short displacements preserves summability. -/
theorem summable_shortCoeff (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (p : Fin d → ℝ) (x z : Site d) : Summable (shortCoeff ε U p x z) := by
  apply (summable_defectCoeff hd hε hU p x z).abs.of_norm_bounded
  intro r
  simp only [shortCoeff, Real.norm_eq_abs]
  split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg]

/-- Restricting the summable defect coefficients to long displacements preserves summability. -/
theorem summable_longCoeff (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (p : Fin d → ℝ) (x z : Site d) : Summable (longCoeff ε U p x z) := by
  apply (summable_defectCoeff hd hε hU p x z).abs.of_norm_bounded
  intro r
  simp only [longCoeff, Real.norm_eq_abs]
  split_ifs <;> simp only [le_refl, abs_zero, abs_nonneg]

/-- Only finitely many representatives have short physical displacement in a bounded domain. -/
theorem shortIndex_finite {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) :
    {r : Cycle.indexSet ε U | radius (physical ε r.1.2) < 1}.Finite := by
  have hb : Bornology.IsBounded {y : Fin d → ℝ | radius y < 1} := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1, fun y hy => ?_⟩
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (abs_coord_le_radius y i).trans hy.le
  apply (((latticeSet_finite hε hU).prod (latticeSet_finite hε hb)).preimage
    Subtype.val_injective.injOn).subset
  intro r hr
  exact ⟨r.2.1, hr⟩

/-- The flux defect is the series of deterministic coefficients times centred conductances. -/
theorem gpField_sub_eq_tsum_defectCoeff (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {a : Edge d → ℝ} {A : ℝ}
    (ha : ∀ e, |a e| ≤ A) (m : ℝ) (p : Fin d → ℝ) {x z : Site d}
    (hx : x ∈ latticeSet ε U) (hz : z ≠ 0) :
    gpField ε U a m p (x + z) x -
        a (edgeAdd x z hz) * jumpKernel (physical ε z) * linearFn ε p z =
      ∑' r : Cycle.indexSet ε U,
        defectCoeff ε U p x z r * (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) := by
  classical
  have hc := summable_cycle_coefficient hd hε hU ha m p x z
  let f : Cycle.indexSet ε U → ℝ := fun r =>
    if r.1 = (x, z) ∨ r.1 = (x + z, -z) then
      jumpKernel (physical ε z) * linearFn ε p z *
        (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) else 0
  have hf : Summable f := summable_edge_indicator ε U x z _
  have he : ∑' r, f r = jumpKernel (physical ε z) * linearFn ε p z *
      (a (edgeAdd x z hz) - m) := by
    rcases Cycle.indexSet_exactly_one ε U x z hx hz with h | h
    · let r₀ : Cycle.indexSet ε U := ⟨(x, z), h.1⟩
      rw [tsum_eq_single r₀]
      · simp only [f, r₀, ite_true, true_or]
      · intro r hr
        have hn : ¬(r.1 = (x, z) ∨ r.1 = (x + z, -z)) := by
          rintro (heq | heq)
          · exact hr (Subtype.ext heq)
          · exact h.2 (heq ▸ r.2)
        exact if_neg hn
    · let r₀ : Cycle.indexSet ε U := ⟨(x + z, -z), h.2⟩
      rw [tsum_eq_single r₀]
      · simp only [f, r₀, ite_true, or_true, edgeAdd_reverse x z hz]
      · intro r hr
        have hn : ¬(r.1 = (x, z) ∨ r.1 = (x + z, -z)) := by
          rintro (heq | heq)
          · exact h.1 (heq ▸ r.2)
          · exact hr (Subtype.ext heq)
        exact if_neg hn
  have ht : (∑' r : Cycle.indexSet ε U,
      defectCoeff ε U p x z r * (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m)) =
      (∑' r : Cycle.indexSet ε U,
        (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m) *
          jumpKernel (physical ε r.1.2) * linearFn ε p r.1.2 *
            (Cycle.cycle r.1.1 r.1.2 (x + z) x : ℝ)) - ∑' r, f r := by
    rw [← hc.tsum_sub hf]
    apply tsum_congr
    intro r
    dsimp only [defectCoeff, f]
    split_ifs <;> ring
  rw [ht, he, gpField_sub_conductance]
  ring

end

end LongRange.Dirichlet
