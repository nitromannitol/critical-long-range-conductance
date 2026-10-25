import LongRange.Dirichlet.Energies
import LongRange.Dirichlet.CoefficientBounds
import LongRange.Dirichlet.Hoeffding

/-!
# Mean short-range energy

The centered Hoeffding second moment and the deterministic coefficient square sum
bound the expectation of the short-range nearest-neighbour energy.
-/

namespace LongRange.Dirichlet

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The short-range energy has mean bounded uniformly in the domain and scale. -/
theorem shortPart_integral_le (d : ℕ) (lam R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a) (ε : ℝ)
      (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (U : Set (Fin d → ℝ)) (hU : Bornology.IsBounded U), euclideanDiam U ≤ R →
      ∀ p : Fin d → ℝ,
        Integrable (fun ω => nnEnergy ε (latticeSet_finite hε.1 hU).toFinset
            (shortDefect ε U (a ω) (meanConductance P hA.one_le_dim a) p)) P ∧
        ∫ ω, nnEnergy ε (latticeSet_finite hε.1 hU).toFinset
            (shortDefect ε U (a ω) (meanConductance P hA.one_le_dim a) p) ∂P ≤
          C * radius p ^ 2 / kappa d ε := by
  classical
  by_cases hd : 1 ≤ d
  · obtain ⟨C₀, hC₀, hm⟩ := edge_hoeffding_second_moment
    obtain ⟨C₁, hC₁, hc⟩ := defectCoeff_sq_sum_bound_with_summable hd
    obtain ⟨C₂, hC₂, hn⟩ := ncard_latticeSet_le d R
    let C := 2 * (d : ℝ) * C₂ * C₀ * C₁ * lam⁻¹ ^ 2
    refine ⟨C + 1, by dsimp [C]; positivity, ?_⟩
    intro Ω _ P a hA ε hε U hU hR p
    let S := (latticeSet_finite hε.1 hU).toFinset
    let D := fun ω => shortDefect ε U (a ω) (meanConductance P hA.one_le_dim a) p
    let B := C₀ * lam⁻¹ ^ 2 *
      (C₁ * radius p ^ 2 * ε ^ (-(2 * (d : ℝ) + 2)))
    have hB : 0 ≤ B := by
      dsimp only [B]
      exact mul_nonneg (mul_nonneg hC₀.le (sq_nonneg _))
        (mul_nonneg (mul_nonneg hC₁.le (sq_nonneg _))
          (Real.rpow_nonneg hε.1.le _))
    have hterm (x z : Site d) (i : Fin d) (hz : z = unit i ∨ z = -unit i) :
        Integrable (fun ω => D ω x z ^ 2) P ∧
          ∫ ω, D ω x z ^ 2 ∂P ≤ B := by
      obtain ⟨hs, hb⟩ := hc ε hε U hU p x z i hz
      have hs' := summable_sq_of_summable_real (summable_shortCoeff hd hε.1 hU p x z)
      have hle (r : Cycle.indexSet ε U) :
          shortCoeff ε U p x z r ^ 2 ≤ defectCoeff ε U p x z r ^ 2 := by
        unfold shortCoeff
        split_ifs <;> simp only [le_refl, zero_pow (by decide : 2 ≠ 0), sq_nonneg]
      obtain ⟨hi, ht⟩ := hm hA _ (reprEdge_injective ε U)
        (shortCoeff ε U p x z) (summable_shortCoeff hd hε.1 hU p x z)
      refine ⟨hi, ht.trans ?_⟩
      exact mul_le_mul_of_nonneg_left ((hs'.tsum_le_tsum hle hs).trans hb)
        (mul_nonneg hC₀.le (sq_nonneg _))
    have hi (x : Site d) (i : Fin d) :
        Integrable (fun ω => D ω x (unit i) ^ 2 + D ω x (-unit i) ^ 2) P :=
      (hterm x (unit i) i (Or.inl rfl)).1.add
        (hterm x (-unit i) i (Or.inr rfl)).1
    have his (x : Site d) := integrable_finsetSum Finset.univ (fun i _ => hi x i)
    have hall := integrable_finsetSum S (fun x _ => his x)
    refine ⟨hall.const_mul _, ?_⟩
    change ∫ ω, (ε ^ (3 * d + 2) / kappa d ε) *
      (∑ x ∈ S, ∑ i : Fin d, (D ω x (unit i) ^ 2 + D ω x (-unit i) ^ 2)) ∂P ≤ _
    rw [integral_const_mul, integral_finsetSum S (fun x _ => his x)]
    have hsum : (∑ x ∈ S, ∫ ω, ∑ i : Fin d,
        (D ω x (unit i) ^ 2 + D ω x (-unit i) ^ 2) ∂P) ≤
        (S.card : ℝ) * ((d : ℝ) * (B + B)) := by
      calc
        _ ≤ ∑ x ∈ S, ∑ _i : Fin d, (B + B) := by
          apply Finset.sum_le_sum
          intro x _
          rw [integral_finsetSum Finset.univ (fun i _ => hi x i)]
          apply Finset.sum_le_sum
          intro i _
          rw [integral_add (hterm x _ i (Or.inl rfl)).1
            (hterm x _ i (Or.inr rfl)).1]
          exact add_le_add (hterm x _ i (Or.inl rfl)).2
            (hterm x _ i (Or.inr rfl)).2
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≤ C₂ * ε ^ (-(d : ℝ)) := by
      simpa only [S, ← Set.ncard_eq_toFinset_card] using hn U hU hR ε hε
    have hscale : ε ^ (3 * d + 2) * ε ^ (-(d : ℝ)) *
        ε ^ (-(2 * (d : ℝ) + 2)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hε.1, ← Real.rpow_add hε.1]
      have hexp : ((3 * d + 2 : ℕ) : ℝ) + -(d : ℝ) +
          -(2 * (d : ℝ) + 2) = 0 := by push_cast; ring
      rw [hexp, Real.rpow_zero]
    have hk := (kappa_pos hd hε).le
    calc
      _ ≤ (ε ^ (3 * d + 2) / kappa d ε) *
          ((C₂ * ε ^ (-(d : ℝ))) * ((d : ℝ) * (B + B))) :=
        mul_le_mul_of_nonneg_left
          (hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity)))
          (div_nonneg (pow_nonneg hε.1.le _) hk)
      _ = C * radius p ^ 2 / kappa d ε := by
        dsimp only [B, C]
        calc
          _ = (2 * (d : ℝ) * C₂ * C₀ * C₁ * lam⁻¹ ^ 2) * radius p ^ 2 *
              (ε ^ (3 * d + 2) * ε ^ (-(d : ℝ)) *
                ε ^ (-(2 * (d : ℝ) + 2))) / kappa d ε := by ring
          _ = _ := by rw [hscale, mul_one]
      _ ≤ (C + 1) * radius p ^ 2 / kappa d ε := by
        apply div_le_div_of_nonneg_right _ hk
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (sq_nonneg _)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hd hA.one_le_dim).elim

end

end LongRange.Dirichlet
