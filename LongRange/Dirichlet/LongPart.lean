import LongRange.Dirichlet.Energies
import LongRange.Dirichlet.CoefficientBounds
import LongRange.Dirichlet.Hoeffding
import LatticeProb.Prob.StochasticO.Sums

/-!
# Long-range defect energy

The coefficient square-sum estimate and Hoeffding's inequality control the long-range
part of the nearest-neighbour energy in Proposition 3.3.
-/

namespace LongRange.Dirichlet

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The long-range energy has exponential tails at the scale of Proposition 3.3. -/
theorem longPart_osBound (d : ℕ) (lam R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a) (ε : ℝ)
      (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
      (U : Set (Fin d → ℝ)) (hU : Bornology.IsBounded U), euclideanDiam U ≤ R →
      ∀ p : Fin d → ℝ,
        OsBound P 1 (C * radius p ^ 2 * ε ^ d / kappa d ε)
          (fun ω => nnEnergy ε (latticeSet_finite hε.1 hU).toFinset
            (longDefect ε U (a ω) (meanConductance P hA.one_le_dim a) p)) := by
  classical
  by_cases hd : 1 ≤ d
  · obtain ⟨C₁, hC₁, hb⟩ := longCoeff_sq_sum_bound_with_summable hd
    obtain ⟨C₂, hC₂, hcount⟩ := ncard_latticeSet_le d R
    obtain ⟨Cs, hCs, hsum⟩ := osBound_sum 1 le_rfl
    let C := 8 * (d : ℝ) * Cs * C₂ * C₁ * lam⁻¹ ^ 2
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨C + 1, by positivity, ?_⟩
    intro Ω _ P a hA ε hε U hU hdiam p
    haveI := hA.isProbabilityMeasure
    have hlam := hA.lam_pos
    have heps := hε.1
    have hk := kappa_pos hd hε
    let S := (latticeSet_finite hε.1 hU).toFinset
    let B := C₁ * radius p ^ 2 * ε ^ (-((d : ℝ) + 2))
    let θ := 2 * lam⁻¹ * Real.sqrt B
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hθ : 0 ≤ θ := by dsimp [θ]; positivity
    let D := fun ω => longDefect ε U (a ω) (meanConductance P hA.one_le_dim a) p
    have hpoint (x z : Site d) (i : Fin d) (hz : z = unit i ∨ z = -unit i) :
        OsBound P 1 (θ ^ 2) (fun ω => D ω x z ^ 2) := by
      have hh := (hA.osBound_weighted_tsum _ (reprEdge_injective ε U)
        (longCoeff ε U p x z) (summable_longCoeff hd hε.1 hU p x z)).2
      have hmono : OsBound P 2 θ (fun ω => |D ω x z|) := by
        apply OsBound.mono (Y := fun ω => |D ω x z|) _ _ (fun _ => le_rfl) hh
        · exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (hb ε hε U hU p x z i hz).2)
            (by positivity)
        · positivity
      simpa only [sq_abs] using hmono.sq hθ (fun _ => abs_nonneg _)
    let X := fun q : S × Fin d × Bool => fun ω =>
      D ω q.1.1 (if q.2.2 then unit q.2.1 else -unit q.2.1) ^ 2
    have hx (q : S × Fin d × Bool) : Measurable (X q) :=
      (measurable_longDefect hA.measurable ε U _ p _ _).pow_const 2
    have ho (q : S × Fin d × Bool) : OsBound P 1 (θ ^ 2) (X q) := by
      apply hpoint q.1.1 _ q.2.1
      cases q.2.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> tauto
    have hh := hsum P (S × Fin d × Bool) X (fun _ => θ ^ 2)
      hx (fun _ => sq_nonneg _) ho
    have he (ω : Ω) : (∑ q, X q ω) =
        ∑ x ∈ S, ∑ i : Fin d, (D ω x (unit i) ^ 2 + D ω x (-unit i) ^ 2) := by
      simp only [X, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
        ↓reduceIte]
      exact Finset.sum_coe_sort S (fun x =>
        ∑ i : Fin d, (D ω x (unit i) ^ 2 + D ω x (-unit i) ^ 2))
    have hs : OsBound P 1 (Cs * ((S.card : ℝ) * d * 2 * θ ^ 2))
        (fun ω => ∑ x ∈ S, ∑ i : Fin d,
          (D ω x (unit i) ^ 2 + D ω x (-unit i) ^ 2)) := by
      simpa only [he, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
        Fintype.card_coe, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
        Nat.cast_ofNat, mul_assoc] using hh
    have hscaled := osBound_const_mul hs
      (div_nonneg (pow_nonneg hε.1.le (3 * d + 2)) (kappa_pos hd hε).le)
    have hcard : (S.card : ℝ) ≤ C₂ * ε ^ (-(d : ℝ)) := by
      simpa only [S, Set.ncard_eq_toFinset_card _ (latticeSet_finite hε.1 hU)] using
        hcount U hU hdiam ε hε
    have hθsq : θ ^ 2 = 4 * lam⁻¹ ^ 2 * B := by
      dsimp only [θ]
      rw [mul_pow, mul_pow, Real.sq_sqrt hB]
      ring
    have hexp : ε ^ (3 * d + 2) * ε ^ (-(d : ℝ)) *
        ε ^ (-((d : ℝ) + 2)) = ε ^ d := by
      rw [← Real.rpow_natCast ε (3 * d + 2), ← Real.rpow_natCast ε d,
        ← Real.rpow_add hε.1, ← Real.rpow_add hε.1]
      congr 1
      push_cast
      ring
    have halgebra : ε ^ (3 * d + 2) / kappa d ε *
        (Cs * (C₂ * ε ^ (-(d : ℝ)) * d * 2 * θ ^ 2)) =
        C * radius p ^ 2 * ε ^ d / kappa d ε := by
      rw [hθsq]
      dsimp only [B, C]
      calc
        _ = (8 * (d : ℝ) * Cs * C₂ * C₁ * lam⁻¹ ^ 2) * radius p ^ 2 *
            (ε ^ (3 * d + 2) * ε ^ (-(d : ℝ)) *
              ε ^ (-((d : ℝ) + 2))) / kappa d ε := by ring
        _ = _ := by rw [hexp]
    apply OsBound.mono (Y := fun ω => nnEnergy ε S (D ω)) _ _
      (fun _ => le_rfl) hscaled
    · calc
        _ ≤ ε ^ (3 * d + 2) / kappa d ε *
            (Cs * (C₂ * ε ^ (-(d : ℝ)) * d * 2 * θ ^ 2)) := by
          gcongr
        _ = C * radius p ^ 2 * ε ^ d / kappa d ε := halgebra
        _ ≤ (C + 1) * radius p ^ 2 * ε ^ d / kappa d ε := by
          gcongr
          linarith
    · positivity
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hd hA.one_le_dim).elim

end

end LongRange.Dirichlet
