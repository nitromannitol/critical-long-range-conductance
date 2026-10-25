import LongRange.Dirichlet.Energies
import LongRange.Dirichlet.CoefficientBounds
import LongRange.Dirichlet.BoundedDifference

/-!
# Finite conductance dependence of the short-range energy

The short defect depends on finitely many conductances in a bounded domain. Its energy
has a coordinate influence bound obtained from the absolute coefficient row sums.
-/

namespace LongRange.Dirichlet

open LatticeProb LatticeProb.Euclidean.Lattice
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The short-range energy as a function of the conductances `y` on the finite index set `J`. -/
def shortEnergyFn (ε : ℝ) (U : Set (Fin d → ℝ)) (S : Finset (Site d))
    (J : Finset (Cycle.indexSet ε U)) (p : Fin d → ℝ) (m : ℝ) (y : J → ℝ) : ℝ :=
  nnEnergy ε S (fun x z => ∑ j : J, shortCoeff ε U p x z j * (y j - m))

/-- The short defect is a finite sum over precisely the short representatives. -/
theorem shortDefect_eq_sum {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (a : Edge d → ℝ) (m : ℝ) (p : Fin d → ℝ) (x z : Site d) :
    shortDefect ε U a m p x z =
      ∑ j : (shortIndex_finite hε hU).toFinset, shortCoeff ε U p x z j *
        (a (edgeAdd j.1.1.1 j.1.1.2 j.1.2.2.1) - m) := by
  classical
  let f : Cycle.indexSet ε U → ℝ := fun r =>
    shortCoeff ε U p x z r * (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m)
  change (∑' r, f r) = ∑ j : (shortIndex_finite hε hU).toFinset, f j
  rw [Finset.sum_coe_sort]
  apply tsum_eq_sum
  intro r hr
  have hr' : ¬ radius (physical ε r.1.2) < 1 := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hr
  simp only [f, shortCoeff, if_neg hr', zero_mul]

/-- The short defect energy is the finite conductance energy evaluated at the edge field. -/
theorem nnEnergy_shortDefect_eq {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U)
    (S : Finset (Site d)) (a : Edge d → ℝ) (m : ℝ) (p : Fin d → ℝ) :
    nnEnergy ε S (shortDefect ε U a m p) =
      shortEnergyFn ε U S (shortIndex_finite hε hU).toFinset p m
        (fun j => a (edgeAdd j.1.1.1 j.1.1.2 j.1.2.2.1)) := by
  unfold shortEnergyFn
  congr 1
  funext x z
  exact shortDefect_eq_sum hε hU a m p x z

/-- Boolean signs enumerate both nearest-neighbour directions in the energy. -/
theorem nnEnergy_eq_sum_bool (ε : ℝ) (S : Finset (Site d))
    (D : Site d → Site d → ℝ) :
    nnEnergy ε S D = ε ^ (3 * d + 2) / kappa d ε *
      ∑ k : S × Fin d × Bool,
        D k.1 (if k.2.2 then unit k.2.1 else -unit k.2.1) ^ 2 := by
  classical
  simp only [nnEnergy, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  exact congrArg (fun v => ε ^ (3 * d + 2) / kappa d ε * v)
    (Finset.sum_coe_sort S
      (fun x => ∑ i : Fin d, (D x (unit i) ^ 2 + D x (-unit i) ^ 2))).symm

/-- Replacing one short conductance has the influence bound of Proposition 3.3. -/
theorem shortEnergyFn_update_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (U : Set (Fin d → ℝ)) (hU : Bornology.IsBounded U) (p : Fin d → ℝ)
      {lam m : ℝ}, 0 < lam → m ∈ Set.Icc lam lam⁻¹ →
      ∀ (y : (shortIndex_finite hε.1 hU).toFinset → ℝ),
      (∀ j, y j ∈ Set.Icc lam lam⁻¹) →
      ∀ (j : (shortIndex_finite hε.1 hU).toFinset) {t : ℝ},
      t ∈ Set.Icc lam lam⁻¹ →
        |shortEnergyFn ε U (latticeSet_finite hε.1 hU).toFinset
            (shortIndex_finite hε.1 hU).toFinset p m y -
          shortEnergyFn ε U (latticeSet_finite hε.1 hU).toFinset
            (shortIndex_finite hε.1 hU).toFinset p m (Function.update y j t)| ≤
        ε ^ (3 * d + 2) / kappa d ε * (2 * lam⁻¹ ^ 2 *
          (C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|)) *
          ∑ x ∈ (latticeSet_finite hε.1 hU).toFinset, ∑ i : Fin d,
            (|shortCoeff ε U p x (unit i) j| +
              |shortCoeff ε U p x (-unit i) j|)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := shortCoeff_abs_sum_bound hd
  refine ⟨C, hC, ?_⟩
  intro ε hε U hU p lam m hlam hm y hy j t ht
  let S := (latticeSet_finite hε.1 hU).toFinset
  let J := (shortIndex_finite hε.1 hU).toFinset
  let B : (S × Fin d × Bool) → J → ℝ := fun k r =>
    shortCoeff ε U p k.1 (if k.2.2 then unit k.2.1 else -unit k.2.1) r
  let A := C * radius p * ε ^ (-((d : ℝ) + 1)) * (1 + |Real.log ε|)
  let w := ε ^ (3 * d + 2) / kappa d ε
  have hw : 0 ≤ w := div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le
  have hrow (k : S × Fin d × Bool) : ∑ r : J, |B k r| ≤ A := by
    calc
      _ = ∑ r ∈ J, |shortCoeff ε U p k.1
          (if k.2.2 then unit k.2.1 else -unit k.2.1) r| :=
        Finset.sum_coe_sort _ _
      _ ≤ ∑' r, |shortCoeff ε U p k.1
          (if k.2.2 then unit k.2.1 else -unit k.2.1) r| :=
        (summable_shortCoeff hd hε.1 hU p _ _).abs.sum_le_tsum J
          (fun _ _ => abs_nonneg _)
      _ ≤ A := hbound ε hε U hU p _ _ k.2.1 (by cases k.2.2 <;> simp)
  have hinfluence := weighted_sum_sq_linearForm_update_le hlam B hm y hy j ht w hw
  have hsum : (∑ k, |B k j| * ∑ r : J, |B k r|) ≤
      A * ∑ k, |B k j| := by
    calc
      _ ≤ ∑ k, |B k j| * A := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hcolumn : (∑ k, |B k j|) =
      ∑ x ∈ S, ∑ i : Fin d,
        (|shortCoeff ε U p x (unit i) j| +
          |shortCoeff ε U p x (-unit i) j|) := by
    simp only [B, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
      ↓reduceIte]
    exact Finset.sum_coe_sort S (fun x => ∑ i : Fin d,
      (|shortCoeff ε U p x (unit i) j| + |shortCoeff ε U p x (-unit i) j|))
  unfold shortEnergyFn
  rw [nnEnergy_eq_sum_bool, nnEnergy_eq_sum_bool]
  calc
    _ ≤ w * (2 * lam⁻¹ ^ 2 * ∑ k, |B k j| * ∑ r : J, |B k r|) := hinfluence
    _ ≤ w * (2 * lam⁻¹ ^ 2 * (A * ∑ k, |B k j|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (by positivity)) hw
    _ = _ := by rw [hcolumn, mul_assoc (2 * lam⁻¹ ^ 2)]

end

end LongRange.Dirichlet
