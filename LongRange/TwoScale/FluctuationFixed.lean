import LongRange.TwoScale.FluctuationCoeff
import LongRange.Dirichlet.Hoeffding

/-!
# Fixed-scale concentration of the smooth fluctuation

Injective incident edges and the square sum of the smooth coefficients give
Hoeffding concentration at each lattice site.
-/

namespace LongRange

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- At one site, the smooth fluctuation has Gaussian stochastic scale `λ⁻¹ B / κ`. -/
theorem smoothFluctuation_osBound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ}
      {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a) (ε : ℝ),
      ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (v : (Fin d → ℝ) → ℝ) (B : ℝ), ContDiff ℝ 2 v → (∀ x, |v x| ≤ B) →
      (∀ x, ‖fderiv ℝ v x‖ ≤ B) → (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ B) →
      ∀ q : Site d,
        Measurable (fun ω =>
          smoothFluctuation ε (a ω) (meanConductance P hA.one_le_dim a) v q) ∧
        OsBound P 2 (C * lam⁻¹ * B / kappa d ε)
          (fun ω => |smoothFluctuation ε (a ω)
            (meanConductance P hA.one_le_dim a) v q|) := by
  classical
  by_cases hd : 1 ≤ d
  · obtain ⟨A, hApos, hcoeff⟩ := fluctuation_coeff_sq_sum_le hd
    refine ⟨2 * Real.sqrt A + 1, by positivity, ?_⟩
    intro Ω _ P lam a hA ε hε v B hv hv0 hv1 hv2 q
    let c : Site d → ℝ := fun w => if w = 0 then 0 else
      ε ^ d / kappa d ε * jumpKernel (physical ε w) *
        smoothRemainder v (physical ε q) (physical ε w)
    let I := {w : Site d // w ≠ 0}
    let e : I → Edge d := fun w => edgeAdd q w.1 w.2
    have he : Function.Injective e := by
      intro w w' h
      have hh := Sym2.eq_iff.mp (congrArg Subtype.val h)
      apply Subtype.ext
      rcases hh with h | h
      · exact add_left_cancel h.2
      · exact (w'.2 (by simpa using h.1.symm)).elim
    obtain ⟨hc, hc2⟩ := hcoeff ε hε v B hv hv0 hv1 hv2 q
    change Summable c at hc
    change (∑' w, c w ^ 2) ≤ _ at hc2
    have hlam := hA.lam_pos
    have hrestrict : (∑' w : I, c w.1 ^ 2) = ∑' w, c w ^ 2 := by
      apply tsum_subtype_eq_of_support_subset
        (f := fun w : Site d => c w ^ 2) (s := {w : Site d | w ≠ 0})
      intro w hw
      by_contra h
      have hw0 : w = 0 := by simpa using h
      simp [Function.mem_support, c, hw0] at hw
    have hrep (ω : Ω) :
        smoothFluctuation ε (a ω) (meanConductance P hA.one_le_dim a) v q =
          ∑' w : I, c w.1 *
            (a ω (e w) - meanConductance P hA.one_le_dim a) := by
      unfold smoothFluctuation
      rw [← tsum_mul_left]
      rw [← tsum_subtype_eq_of_support_subset
        (s := {w : Site d | w ≠ 0}) (by
          intro w hw
          by_contra h
          have hw0 : w = 0 := by simpa using h
          simp [Function.mem_support, hw0] at hw)]
      apply tsum_congr
      intro w
      have hw : (w : Site d) ≠ 0 := w.property
      simp only [c, e, if_neg hw, dif_neg hw]
      ring
    obtain ⟨hm, ho⟩ := hA.osBound_weighted_tsum e he (fun w : I => c w.1)
      (hc.subtype (fun w => w ≠ 0))
    have hB : 0 ≤ B := (abs_nonneg _).trans (hv0 0)
    have hk := kappa_pos hd hε
    have hroot : Real.sqrt (∑' w : I, c w.1 ^ 2) ≤
        Real.sqrt A * B / kappa d ε := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      rw [hrestrict]
      calc
        _ ≤ A * B ^ 2 / kappa d ε ^ 2 := hc2
        _ = _ := by rw [div_pow, mul_pow, Real.sq_sqrt hApos.le]
    have hscale : 2 * lam⁻¹ * Real.sqrt (∑' w : I, c w.1 ^ 2) ≤
        (2 * Real.sqrt A + 1) * lam⁻¹ * B / kappa d ε := by
      calc
        _ ≤ 2 * lam⁻¹ * (Real.sqrt A * B / kappa d ε) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
        _ = (2 * Real.sqrt A + 1) * lam⁻¹ * B / kappa d ε -
            lam⁻¹ * B / kappa d ε := by ring
        _ ≤ _ := sub_le_self _ (by positivity)
    refine ⟨?_, ?_⟩
    · simpa only [hrep] using hm
    · have h := OsBound.mono hscale (by positivity) (fun _ => le_rfl) ho
      simpa only [hrep] using h
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P lam a hA
    exact (hd hA.one_le_dim).elim

end

end LongRange
