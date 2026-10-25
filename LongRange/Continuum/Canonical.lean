import LongRange.Dirichlet.Hoeffding
import LatticeProb.Analysis.Elliptic.CanonicalDirichlet

/-!
# Classical continuum solutions at the mean conductance

Assumption (U) makes the paper's effective coefficient strictly positive. The canonical
classical Dirichlet producer therefore applies to every datum with the prescribed Hölder
bound. Uniqueness on the closure also identifies every other classical representative.
These statements concern classical solutions only.
-/

namespace LongRange.Continuum

open MeasureTheory LatticeProb.Elliptic LatticeProb.Euclidean.Lattice
open scoped BigOperators

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Assumption (U) gives positivity with the normalization in the continuum equation. -/
theorem mean_coefficient_pos {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ}
    (hA : AssumptionU P lam a) (hd : 1 ≤ d) :
    0 < meanConductance P hd a / (2 * (d : ℝ)) := by
  have hmean : lam ≤ meanConductance P hd a := hA.mean_mem_Icc.1
  exact div_pos (hA.lam_pos.trans_le hmean)
    (mul_pos (by norm_num) (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)))

/-- Every datum under the uniform Hölder bound has a unique continuous zero-extended
classical solution at the actual mean coefficient, including mass zero. -/
theorem existsUnique_classical_solution
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (hd : 1 ≤ d) {σ μ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {M : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hf : c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M) :
    ∃! ū, IsClassicalDirichletSolution U μ
      (meanConductance P hd a / (2 * d)) f ū ∧ Continuous ū ∧
        ∀ x ∉ U, ū x = 0 := by
  have hfinite : c0HolderNorm σ (closure U) f < ⊤ :=
    hf.trans_lt ENNReal.ofReal_lt_top
  exact existsUnique_zero_extended_classicalDirichletSolution h614 h37 hd hσ.1 hσ.2
    hU hμ (mean_coefficient_pos hA hd) hfinite

/-- Closure uniqueness transfers directly to the lattice samples occurring in the
paper's error norm; no values outside the domain enter that norm. -/
theorem sampled_error_eq
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (hd : 1 ≤ d) {σ μ : ℝ} (hμ : 0 ≤ μ)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {P : Measure Ω} {lam : ℝ} {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {f ū v : (Fin d → ℝ) → ℝ}
    (hū : IsClassicalDirichletSolution U μ (meanConductance P hd a / (2 * d)) f ū)
    (hv : IsClassicalDirichletSolution U μ (meanConductance P hd a / (2 * d)) f v)
    (ε : ℝ) (u : LatticeProb.Site d → ℝ) :
    l2Norm ε U (fun q => u q - v (physical ε q)) =
      l2Norm ε U (fun q => u q - ū (physical ε q)) := by
  have heq := hv.eqOn_closure h37 hd hU hμ (mean_coefficient_pos hA hd) hū
  unfold l2Norm l2NormSq
  congr 2
  apply tsum_congr
  intro q
  dsimp only
  rw [heq (subset_closure (mem_latticeSet.mp q.property))]

/-- In dimension one at mass zero, the constant mean conductance is nonzero forcing.
The produced zero-extended solution on the unit ball has value one at the origin. -/
theorem exists_nonzero_mass_zero_solution
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    {P : Measure Ω} {lam : ℝ} {a : Ω → Edge 1 → ℝ} (hA : AssumptionU P lam a) :
    ∃ ū : (Fin 1 → ℝ) → ℝ,
      IsClassicalDirichletSolution (unitBall 1) 0
        (meanConductance P (by omega) a / (2 * 1))
        (fun _ => meanConductance P (by omega) a) ū ∧
      Continuous ū ∧ (∀ x ∉ unitBall 1, ū x = 0) ∧ ū 0 = 1 ∧
      0 < meanConductance P (by omega) a := by
  let b := meanConductance P (by omega) a / (2 * (1 : ℝ))
  have hdata : (fun x : Fin 1 → ℝ => 0 * (1 - ∑ k, x k ^ 2) + 2 * 1 * b) =
      (fun _ => meanConductance P (by omega) a) := by
    ext x
    dsimp [b]
    ring
  have hfinite := quadratic_datum_c0HolderNorm_lt_top (d := 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) 0 b
  simp only [Nat.cast_one] at hfinite
  rw [hdata] at hfinite
  have hbound := (ENNReal.ofReal_toReal hfinite.ne).ge
  obtain ⟨ū, hū, _⟩ := existsUnique_classical_solution (μ := 0) h614 h37 (by omega)
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioo 0 1) (by norm_num)
    (isC2HolderDomain_unitBall _) hA hbound
  simp only [Nat.cast_one] at hū
  have hquad := quadratic_isClassicalDirichletSolution (d := 1) 0 b
  simp only [Nat.cast_one] at hquad
  rw [hdata] at hquad
  have heq := hū.1.eqOn_closure h37 (by omega) (isC2HolderDomain_unitBall (1 / 2))
    (by norm_num) (show 0 < b by
      simpa only [b, Nat.cast_one] using mean_coefficient_pos hA (by omega)) hquad
  have horigin : (0 : Fin 1 → ℝ) ∈ closure (unitBall 1) := by
    apply subset_closure
    rw [mem_unitBall_iff]
    norm_num
  refine ⟨ū, hū.1, hū.2.1, hū.2.2, ?_, ?_⟩
  · simpa only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, sub_zero] using heq horigin
  · have hmean : lam ≤ meanConductance P (by omega) a := hA.mean_mem_Icc.1
    exact hA.lam_pos.trans_le hmean

end

end LongRange.Continuum
