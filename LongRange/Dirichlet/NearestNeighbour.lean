import LongRange.Dirichlet.Young
import LongRange.Dirichlet.Field

/-!
# Nearest-neighbour reduction of the corrector energy

The comparison field cancels the flux defect on every non-nearest-neighbour edge.
The remaining finite sum has the physical kernel normalization of Proposition 3.3.
-/

namespace LongRange

open Classical LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The flux defect of the comparison field, with background coefficient `m`. -/
noncomputable def fluxDefect (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ) (m : ℝ)
    (p : Fin d → ℝ) (x z : Site d) : ℝ :=
  if hz : z = 0 then 0 else
    Dirichlet.gpField ε U a m p (x + z) x -
      a (edgeAdd x z hz) * jumpKernel (physical ε z) * linearFn ε p z

/-- The physical kernel on a positive coordinate unit increment. -/
theorem jumpKernel_physical_unit {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    jumpKernel (physical ε (unit i)) = (ε ^ (d + 2))⁻¹ := by
  rw [jumpKernel_of_ne_zero (fun h => unit_ne_zero i
    ((physical_eq_zero_iff hε _).mp h)), radius_physical_eq_mul hε.le]
  have hr : radius (physical 1 (unit i)) = 1 := by
    simp [radius, physical, unit, Pi.single_apply]
  rw [hr, mul_one]

/-- The physical kernel on a negative coordinate unit increment. -/
theorem jumpKernel_physical_neg_unit {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    jumpKernel (physical ε (-unit i)) = (ε ^ (d + 2))⁻¹ := by
  rw [physical_neg, jumpKernel_neg, jumpKernel_physical_unit hε]

/-- Coordinate unit increments are injectively indexed. -/
private theorem unit_injective : Function.Injective (unit : Fin d → Site d) := by
  intro i j hij
  by_contra h
  have hi := congrFun hij i
  simp [unit, h] at hi

/-- A positive coordinate unit increment cannot be a negative coordinate unit increment. -/
private theorem unit_ne_neg_unit (i j : Fin d) : unit i ≠ -unit j := by
  intro h
  have hi := congrFun h i
  by_cases hij : i = j
  · subst j
    simp [unit] at hi
  · simp [unit, hij] at hi

/-- Summing an array supported on the coordinate neighbours gives the `2d`-term sum. -/
private theorem tsum_neighbours (S : Finset (Site d)) (f : Site d × Site d → ℝ)
    (hf : ∀ q, q.1 ∉ S ∨ (∀ i, q.2 ≠ unit i ∧ q.2 ≠ -unit i) → f q = 0) :
    Summable f ∧ ∑' q, f q = ∑ x ∈ S, ∑ i : Fin d,
      (f (x, unit i) + f (x, -unit i)) := by
  let T := (Finset.univ.image (unit : Fin d → Site d)) ∪
    (Finset.univ.image (fun i : Fin d => -unit i))
  have hz : ∀ q ∉ S ×ˢ T, f q = 0 := by
    intro q hq
    apply hf
    by_cases hx : q.1 ∈ S
    · right
      have ht : q.2 ∉ T := fun ht => hq (Finset.mem_product.mpr ⟨hx, ht⟩)
      intro i
      constructor
      · intro he
        apply ht
        simp [T, he]
      · intro he
        apply ht
        simp [T, he]
    · exact Or.inl hx
  have hs : Summable f := summable_of_hasFiniteSupport
    (Set.Finite.subset (S ×ˢ T).finite_toSet (by
      intro q hq
      by_contra hn
      exact hq (hz q hn)))
  refine ⟨hs, ?_⟩
  rw [tsum_eq_sum hz, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  have hdis : Disjoint (Finset.univ.image (unit : Fin d → Site d))
      (Finset.univ.image (fun i : Fin d => -unit i)) := by
    rw [Finset.disjoint_left]
    intro z hz hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hn
    exact unit_ne_neg_unit i j hj.symm
  dsimp only [T]
  rw [Finset.sum_union hdis,
    Finset.sum_image (fun i _ j _ hij => unit_injective hij),
    Finset.sum_image (fun i _ j _ hij => unit_injective (neg_injective hij)),
    ← Finset.sum_add_distrib]

/-- Proposition 3.3, Step 2: only nearest-neighbour flux defects contribute to the bound. -/
theorem correctorEnergy_le_fluxDefect (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {lam : ℝ} (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (m : ℝ)
    (p : Fin d → ℝ) :
    correctorEnergy ε U a p ≤ lam⁻¹ * (ε ^ (3 * d + 2) / kappa d ε) *
      ∑ x ∈ (latticeSet_finite hε.1 hU).toFinset, ∑ i : Fin d,
        (fluxDefect ε U a m p x (unit i) ^ 2 +
          fluxDefect ε U a m p x (-unit i) ^ 2) := by
  let S := (latticeSet_finite hε.1 hU).toFinset
  let f : Site d × Site d → ℝ := fun q =>
    if q.1 ∈ latticeSet ε U then
      (jumpKernel (physical ε q.2))⁻¹ * fluxDefect ε U a m p q.1 q.2 ^ 2 else 0
  have hz (q : Site d × Site d)
      (hq : q.1 ∉ S ∨ (∀ i, q.2 ≠ unit i ∧ q.2 ≠ -unit i)) : f q = 0 := by
    rcases hq with hx | hn
    · have hx' : q.1 ∉ latticeSet ε U := by simpa only [S, Set.Finite.mem_toFinset] using hx
      simp only [f, hx', if_false]
    · by_cases hx : q.1 ∈ latticeSet ε U
      · by_cases hw : q.2 = 0
        · simp [f, fluxDefect, hw, hx]
        · rw [show f q = (jumpKernel (physical ε q.2))⁻¹ *
              fluxDefect ε U a m p q.1 q.2 ^ 2 by simp only [f, hx, if_true]]
          rw [fluxDefect, dif_neg hw,
            Dirichlet.gpField_nonnearest ε U a m p q.1 q.2 hx hw hn, sub_self,
            zero_pow (by decide : 2 ≠ 0), mul_zero]
      · simp only [f, hx, if_false]
  obtain ⟨hs, ht⟩ := tsum_neighbours S f hz
  have he (q : Site d × Site d) :
      (if hw : q.2 = 0 then 0 else if q.1 ∈ latticeSet ε U then
        (jumpKernel (physical ε q.2))⁻¹ *
          (Dirichlet.gpField ε U a m p (q.1 + q.2) q.1 -
            a (edgeAdd q.1 q.2 hw) * jumpKernel (physical ε q.2) *
              linearFn ε p q.2) ^ 2 else 0) = f q := by
    by_cases hw : q.2 = 0 <;> by_cases hx : q.1 ∈ latticeSet ε U <;>
      simp [f, fluxDefect, hw, hx]
  have habs : ∀ e, |a e| ≤ lam⁻¹ := fun e =>
    abs_le.mpr ⟨le_trans (neg_nonpos.mpr (inv_nonneg.mpr hlam.le))
      (hlam.le.trans (ha e).1), (ha e).2⟩
  have hres : Summable (fun q : Site d × Site d =>
      if hw : q.2 = 0 then 0 else if q.1 ∈ latticeSet ε U then
        (jumpKernel (physical ε q.2))⁻¹ *
          (Dirichlet.gpField ε U a m p (q.1 + q.2) q.1 -
            a (edgeAdd q.1 q.2 hw) * jumpKernel (physical ε q.2) *
              linearFn ε p q.2) ^ 2 else 0) := by
    simpa only [he] using hs
  have hb := correctorEnergy_le_of_solenoidal hd hε hU hlam ha p
    (Dirichlet.gpField ε U a m p) (Dirichlet.gpField_antisymm ε U a m p)
    (fun x _ => ⟨Dirichlet.summable_gpField hd hε.1 hU habs m p x,
      Dirichlet.gpField_divergence hd hε.1 hU habs m p x⟩) hres
  simp only [he] at hb
  rw [ht] at hb
  have hv (x : Site d) (hx : x ∈ S) (i : Fin d) :
      f (x, unit i) + f (x, -unit i) = ε ^ (d + 2) *
        (fluxDefect ε U a m p x (unit i) ^ 2 +
          fluxDefect ε U a m p x (-unit i) ^ 2) := by
    have hx' : x ∈ latticeSet ε U := by simpa only [S, Set.Finite.mem_toFinset] using hx
    simp only [f, hx', if_true, jumpKernel_physical_unit hε.1,
      jumpKernel_physical_neg_unit hε.1, inv_inv]
    ring
  have hsum : (∑ x ∈ S, ∑ i : Fin d, (f (x, unit i) + f (x, -unit i))) =
      ε ^ (d + 2) * ∑ x ∈ S, ∑ i : Fin d,
        (fluxDefect ε U a m p x (unit i) ^ 2 +
          fluxDefect ε U a m p x (-unit i) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hv x hx i)
  rw [hsum] at hb
  have hpow : ε ^ (2 * d) * ε ^ (d + 2) = ε ^ (3 * d + 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ _ := hb
    _ = _ := by rw [← hpow]; dsimp only [S]; ring

end

end LongRange
