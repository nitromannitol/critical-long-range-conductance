import LongRange.HeatKernel.Rescaled
import LatticeProb.Prob.JumpChain.InitialKilling

/-!
# The killed rescaled heat kernel

The killed kernel restricts the initial point and uses the arrival-filtered
Poisson series thereafter. Its exact survival-event characterization includes
time zero and all starting sites. Domination preserves the common bound constant.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Physical-volume density of the actual walk killed outside the physical domain. -/
def rescaledKilledDensity (hd : 1 ≤ d) {ε lam : ℝ} (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam)
    (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (U : Set (Fin d → ℝ)) (t : ℝ≥0) (x y : Site d) : ℝ :=
  (ε ^ d)⁻¹ * (walkRates hd hε.1 hlam a ha).initialKilledKernel (latticeSet ε U) t x y

/-- The density equals the actual surviving physical-position law for every initial site. -/
theorem rescaledKilledDensity_eq_position_mass (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (U : Set (Fin d → ℝ))
    (t : ℝ≥0) (x y : Site d) :
    rescaledKilledDensity hd hε hlam a ha U t x y = (ε ^ d)⁻¹ *
      ((walkRates hd hε.1 hlam a ha).regularLaw (MeasureTheory.Measure.dirac x)).real
        {h | physical ε (h.position t) = physical ε y ∧
          ∀ s ≤ t, physical ε (h.position s) ∈ U} := by
  have hevent : {h : JumpChain.RegularHistory (Site d) |
      physical ε (h.position t) = physical ε y ∧
        ∀ s ≤ t, physical ε (h.position s) ∈ U} =
      {h | h.position t = y ∧ ∀ s ≤ t, h.position s ∈ latticeSet ε U} := by
    ext h
    simp only [latticeSet, Set.mem_setOf_eq, (physical_injective hε.1).eq_iff]
  rw [hevent, rescaledKilledDensity,
    JumpChain.BoundedRates.initialKilledKernel_eq_position_mass]

/-- An initial point outside the physical domain is killed at time zero. -/
theorem rescaledKilledDensity_eq_zero_of_not_mem (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (U : Set (Fin d → ℝ))
    (t : ℝ≥0) (x y : Site d) (hx : physical ε x ∉ U) :
    rescaledKilledDensity hd hε hlam a ha U t x y = 0 := by
  classical
  simp only [rescaledKilledDensity, JumpChain.BoundedRates.initialKilledKernel,
    latticeSet, Set.mem_setOf_eq, if_neg hx, mul_zero]

/-- Inside the domain the density uses the original arrival-filtered surviving series. -/
theorem rescaledKilledDensity_of_mem (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (U : Set (Fin d → ℝ))
    (t : ℝ≥0) (x y : Site d) (hx : physical ε x ∈ U) :
    rescaledKilledDensity hd hε hlam a ha U t x y = (ε ^ d)⁻¹ *
      (walkRates hd hε.1 hlam a ha).killedKernel (latticeSet ε U) t x y := by
  classical
  simp only [rescaledKilledDensity, JumpChain.BoundedRates.initialKilledKernel,
    latticeSet, Set.mem_setOf_eq, if_pos hx]

/-- At time zero the density is the physical Dirac mass restricted to the domain. -/
theorem rescaledKilledDensity_zero (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (U : Set (Fin d → ℝ))
    (x y : Site d) :
    rescaledKilledDensity hd hε hlam a ha U 0 x y = (ε ^ d)⁻¹ *
      (if physical ε x ∈ U then (if x = y then 1 else 0) else 0) := by
  classical
  simp only [rescaledKilledDensity, JumpChain.BoundedRates.initialKilledKernel_zero,
    latticeSet, Set.mem_setOf_eq]
  split_ifs <;> rfl

/-- Killing decreases the actual physical-volume density. -/
theorem rescaledKilledDensity_le (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo 0 1) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (U : Set (Fin d → ℝ))
    (t : ℝ≥0) (x y : Site d) :
    rescaledKilledDensity hd hε hlam a ha U t x y ≤
      rescaledDensity hd hε hlam a ha t x y :=
  mul_le_mul_of_nonneg_left
    ((walkRates hd hε.1 hlam a ha).initialKilledKernel_le_transitionKernel (latticeSet ε U) t x y)
    (inv_nonneg.mpr (pow_nonneg hε.1.le d))

/-- The same constant bounds the full and killed physical densities at every scale. -/
theorem rescaledDensity_and_killed_offDiagonal_uniform
    (hMSCUniform : External.MuruganSaloffCosteUniform)
    (hNash : External.ChenKimKumagaiWangNash)
    (hDavies : External.ChenKimKumagaiWangDavies) (d : ℕ) (hd : 1 ≤ d)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ hε : ε ∈ Set.Ioo 0 1,
      ∀ a : Edge d → ℝ, ∀ ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹,
      ∀ t : ℝ≥0, 0 < t → ∀ x y : Site d, x ≠ y →
      let bound := C * min
        ((ε ^ 2 + t / kappa d ε * Real.log (2 + t / (kappa d ε * ε ^ 2))) ^
          (-((d : ℝ) / 2)))
        (t / kappa d ε * Real.log (2 + radius (physical ε (y - x)) / ε) /
          radius (physical ε (y - x)) ^ (d + 2))
      rescaledDensity hd hε hlam a ha t x y ≤ bound ∧
        ∀ U : Set (Fin d → ℝ),
          rescaledKilledDensity hd hε hlam a ha U t x y ≤ bound := by
  obtain ⟨C, hC, hbound⟩ :=
    rescaledDensity_offDiagonal_uniform hMSCUniform hNash hDavies d hd hlam
  refine ⟨C, hC, ?_⟩
  intro ε hε a ha t ht x y hxy
  have hb := hbound ε hε a ha t ht x y hxy
  exact ⟨hb, fun U ↦ (rescaledKilledDensity_le hd hε hlam a ha U t x y).trans hb⟩

end

end LongRange
