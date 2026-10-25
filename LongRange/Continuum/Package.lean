import LongRange.Continuum.Schauder
import LongRange.Continuum.BallExtension
import LongRange.Continuum.NormCompare
import LongRange.Continuum.BoundaryLipschitz
import LongRange.Continuum.OneDimDomain
import LatticeProb.Analysis.Elliptic.OneDimCutoff

/-!
# Continuum extension for the homogenization theorem

The uniform Dirichlet estimate and compactly supported extension give all pointwise
bounds used by Theorem 1.1. In dimension one the estimates follow from the interval proofs.
-/

namespace LongRange

open LatticeProb.Elliptic LatticeProb.Euclidean.Lattice

/-- The continuum Dirichlet solution has a supported extension with uniform value,
derivative and Euclidean Hölder bounds in every positive dimension. -/
theorem continuum_extension
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    {d : ℕ} (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ (∀ x ∈ U, radius x < R) ∧
      ∀ (a₀ μ : ℝ), a₀ ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
      ∀ (f ū : (Fin d → ℝ) → ℝ) (M : ℝ), 0 ≤ M →
      c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M →
      IsClassicalDirichletSolution U μ a₀ f ū →
      ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧ (∀ x, R ≤ radius x → v x = 0) ∧
        Set.EqOn v ū U ∧ (∀ x ∈ frontier U, v x = 0) ∧
        (∀ x, |v x| ≤ C * M) ∧ (∀ x, ‖fderiv ℝ v x‖ ≤ C * M) ∧
        (∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ C * M) ∧
        (∀ x y, ‖iteratedFDeriv ℝ 2 v x - iteratedFDeriv ℝ 2 v y‖ ≤
          C * M * radius (x - y) ^ σ) := by
  have hs : ∃ C : ℝ, 0 < C ∧ ∀ (a μ : ℝ),
      a ∈ Set.Icc Λ⁻¹ Λ → μ ∈ Set.Icc 0 Λ →
      ∀ f u : (Fin d → ℝ) → ℝ, c0HolderNorm σ (closure U) f < ⊤ →
        IsClassicalDirichletSolution U μ a f u →
        c2HolderNorm σ U u ≤ ENNReal.ofReal C * c0HolderNorm σ (closure U) f := by
    by_cases hd2 : 2 ≤ d
    · exact homogenized_c2Holder_bound h619 h66 h37 hd2 hσ hσ1 hU hΛ
    · obtain rfl : d = 1 := by omega
      obtain ⟨α, β, hαβ, rfl⟩ := eq_interval_of_isC2HolderDomain hU
      obtain ⟨C, hC, hb⟩ := c2HolderNorm_le_one_dim_dirichlet hαβ hσ hσ1 hΛ
      exact ⟨C, hC, fun a μ ha hμ f u hf hu =>
        hb μ a f u ha.1 ha.2 hμ.1 hμ.2 hf hu⟩
  have he : ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ (∀ x ∈ U, radius x < R) ∧
      ∀ u : (Fin d → ℝ) → ℝ, ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
        ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧
          (∀ x, R ≤ radius x → v x = 0) ∧ Set.EqOn v u U ∧
          c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C * c2HolderNorm σ U u := by
    by_cases hd2 : 2 ≤ d
    · exact regular_extension_of_gt_ball h637 hd2 hσ hσ1 hU
    · obtain rfl : d = 1 := by omega
      obtain ⟨α, β, hαβ, rfl⟩ := eq_interval_of_isC2HolderDomain hU
      obtain ⟨C, hC, hb⟩ := one_dim_holder_extension_support hαβ hσ hσ1
      let R := max |α - 2| |β + 2| + 1
      have hr (x : Fin 1 → ℝ) : radius x = |x 0| := by
        simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using
          radius_sub_one_dim x 0
      have hleft : -R < α - 2 := by
        have := le_max_left |α - 2| |β + 2|
        have := neg_abs_le (α - 2)
        dsimp [R]
        linarith
      have hright : β + 2 < R := by
        have := le_max_right |α - 2| |β + 2|
        have := le_abs_self (β + 2)
        dsimp [R]
        linarith
      refine ⟨C, R, hC, by dsimp [R]; positivity, ?_, ?_⟩
      · intro x hx
        rw [hr, abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · intro u hu hn
        obtain ⟨v, hv, hz, heq, hn⟩ := hb u hu hn
        refine ⟨v, hv, ?_, heq, hn⟩
        intro x hx
        apply hz x
        rw [hr, le_abs] at hx
        rcases hx with hx | hx
        · right; linarith
        · left; linarith
  obtain ⟨Cs, hCs, hs⟩ := hs
  obtain ⟨Ce, R, hCe, hR, hUR, he⟩ := he
  let K := Ce * Cs
  have hK : 0 < K := mul_pos hCe hCs
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdsq : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  refine ⟨(d : ℝ) ^ 2 * K + 1, R, by positivity, hR, hUR, ?_⟩
  intro a μ ha hμ f u M hM hf hu
  have hn : c2HolderNorm σ U u ≤ ENNReal.ofReal (Cs * M) := by
    calc
      _ ≤ ENNReal.ofReal Cs * c0HolderNorm σ (closure U) f :=
        hs a μ ha hμ f u (hf.trans_lt ENNReal.ofReal_lt_top) hu
      _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal M := mul_le_mul_right hf _
      _ = _ := (ENNReal.ofReal_mul hCs.le).symm
  obtain ⟨v, hv, hz, heq, hvn⟩ := he u hu.1 (hn.trans_lt ENNReal.ofReal_lt_top)
  have hvbound : c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal (K * M) := by
    calc
      _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Cs * M) :=
        hvn.trans (mul_le_mul_right hn _)
      _ = _ := by rw [← ENNReal.ofReal_mul hCe.le]; congr 1; ring
  have hKM : 0 ≤ K * M := mul_nonneg hK.le hM
  have hsecond : (d : ℝ) ^ 2 * (K * M) ≤ ((d : ℝ) ^ 2 * K + 1) * M := by
    nlinarith
  have hvalue : K * M ≤ ((d : ℝ) ^ 2 * K + 1) * M :=
    (le_mul_of_one_le_left hKM hdsq).trans hsecond
  have hfirst : (d : ℝ) * (K * M) ≤ ((d : ℝ) ^ 2 * K + 1) * M :=
    (mul_le_mul_of_nonneg_right hdd hKM).trans hsecond
  refine ⟨v, hv, hz, heq,
    eq_zero_on_frontier_of_eqOn hv.continuous hu.2.1 heq hu.2.2.1,
    fun x => (abs_le_of_c2HolderNorm hKM hvbound x).trans hvalue,
    fun x => (norm_fderiv_le_of_c2HolderNorm hKM hvbound x).trans hfirst,
    fun x => (norm_iteratedFDeriv_two_le_of_c2HolderNorm hKM hvbound x).trans hsecond,
    ?_⟩
  intro x y
  exact (norm_iteratedFDeriv_two_sub_le_of_c2HolderNorm hKM hvbound x y).trans
    (mul_le_mul_of_nonneg_right hsecond (Real.rpow_nonneg (radius_nonneg _) _))

end LongRange
