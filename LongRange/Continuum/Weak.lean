import LongRange.Continuum.Canonical
import LongRange.Continuum.Package
import LatticeProb.Analysis.Elliptic.ClassicalWeakGraph
import LatticeProb.Analysis.Elliptic.WeakDirichletAlgebra

/-!
# Weak continuum solutions from the classical extension

The supported C² extension determines every coordinate of an actual H¹₀ graph.
The cited zero-boundary approximation and homogeneous uniqueness inputs remain explicit.
-/

namespace LongRange.Continuum

open MeasureTheory LatticeProb.Elliptic LatticeProb.Elliptic.WeakDirichlet
open LatticeProb.Euclidean.Lattice
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- Agreement on an open domain identifies the physical Laplacians there. -/
theorem laplacian_eqOn {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {v u : (Fin d → ℝ) → ℝ} (heq : Set.EqOn v u U) :
    Set.EqOn (laplacian v) (laplacian u) U := by
  intro x hx
  have he : v =ᶠ[𝓝 x] u := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq
  have hd := (he.iteratedFDeriv (𝕜 := ℝ) 2).eq_of_nhds
  simp only [laplacian, secondPartial, hd]

/-- Every source classical solution has an actual H¹₀ graph of a global C² extension.
The value and every derivative coordinate, the weak equation, and uniqueness are retained. -/
theorem classical_solution_has_weak_graph
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (h75 : LatticeProb.External.GilbargTrudingerZeroBoundaryApproximation)
    (h82 : LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness)
    (hd : 1 ≤ d) {σ μ a₀ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (hμ : 0 ≤ μ) (ha : 0 < a₀) {U : Set (Fin d → ℝ)}
    (hU : IsC2HolderDomain σ U) {M : ℝ} {f ū : (Fin d → ℝ) → ℝ}
    (hf : c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M)
    (hū : IsClassicalDirichletSolution U μ a₀ f ū) :
    ∃ V : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 V ∧ Set.EqOn V ū U ∧
      (∀ x ∈ frontier U, V x = 0) ∧
      (∀ x ∈ U, μ * V x - a₀ * laplacian V x = f x) ∧
      ∃ w : H10 U, IsWeakSolution U μ a₀ f w ∧
        (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū ∧
        (∀ i : Fin d, (fun x => w.val i.succ x)
          =ᵐ[volume.restrict U] partialDeriv i V) ∧
        (∀ z : H10 U, z = w ↔
          (fun x => z.val 0 x) =ᵐ[volume.restrict U] V ∧
          ∀ i : Fin d, (fun x => z.val i.succ x)
            =ᵐ[volume.restrict U] partialDeriv i V) ∧
        ∀ z : H10 U, IsWeakSolution U μ a₀ f z → z = w := by
  let Λ := max 1 (max a₀ (max a₀⁻¹ μ))
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  have haΛ : a₀ ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have haiΛ : a₀⁻¹ ≤ Λ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hμΛ : μ ≤ Λ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlow : Λ⁻¹ ≤ a₀ := (inv_le_comm₀ ha hΛpos).mp haiΛ
  obtain ⟨C, R, _, _, _, hext⟩ :=
    continuum_extension h619 h66 h37 h637 hd hσ.1 hσ.2 hU hΛ
  obtain ⟨V, hV, _, heq, hz, _⟩ := hext a₀ μ ⟨hlow, haΛ⟩ ⟨hμ, hμΛ⟩
    f ū (max M 0) (le_max_right _ _)
    (hf.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) hū
  have hpde : ∀ x ∈ U, μ * V x - a₀ * laplacian V x = f x := by
    intro x hx
    rw [heq hx, laplacian_eqOn hU.1 heq hx]
    exact hū.2.2.2 x hx
  let w := classicalH10 h75 (by omega) hV hU.2.2.1 hU.1 hU.2.1 hz
  have hw : IsWeakSolution U μ a₀ f w :=
    classicalH10_isWeakSolution h75 (by omega) hV hU.2.2.1 hU.1 hU.2.1 hz μ a₀ f hpde
  have hcoords := (eq_classicalH10_iff h75 (by omega) hV hU.2.2.1 hU.1
    hU.2.1 hz w).mp rfl
  refine ⟨V, hV, heq, hz, hpde, w, hw, ?_, hcoords.2, ?_, ?_⟩
  · apply hcoords.1.trans
    filter_upwards [ae_restrict_mem hU.1.measurableSet] with x hx
    exact heq hx
  · exact fun z => eq_classicalH10_iff h75 (by omega) hV hU.2.2.1 hU.1 hU.2.1 hz z
  · intro z hz
    exact hz.eq_of_same_data h82 (by omega) hU.1 hU.2.1 hU.2.2.1 ha hμ hw

/-- The source data produce both the unique H¹₀ solution and its unique continuous
zero-extended classical representative, at the actual mean coefficient. -/
theorem exists_weak_classical_solution
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (h75 : LatticeProb.External.GilbargTrudingerZeroBoundaryApproximation)
    (h82 : LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness)
    (hd : 1 ≤ d) {σ μ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {lam : ℝ}
    {a : Ω → Edge d → ℝ} (hA : AssumptionU P lam a)
    {M : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hf : c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M) :
    ∃ w : H10 U, ∃ ū : (Fin d → ℝ) → ℝ,
      IsWeakSolution U μ (meanConductance P hd a / (2 * d)) f w ∧
      (∀ z : H10 U, IsWeakSolution U μ (meanConductance P hd a / (2 * d)) f z →
        z = w) ∧
      (IsClassicalDirichletSolution U μ (meanConductance P hd a / (2 * d)) f ū ∧
        Continuous ū ∧ ∀ x ∉ U, ū x = 0) ∧
      (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū ∧
      ∀ v, (IsClassicalDirichletSolution U μ
        (meanConductance P hd a / (2 * d)) f v ∧ Continuous v ∧
          ∀ x ∉ U, v x = 0) → v = ū := by
  obtain ⟨ū, hū, huniq⟩ := existsUnique_classical_solution h614 h37 hd hσ hμ hU hA hf
  obtain ⟨V, _, _, _, _, w, hw, hae, _, _, hwu⟩ :=
    classical_solution_has_weak_graph h619 h66 h37 h637 h75 h82 hd hσ hμ
      (mean_coefficient_pos hA hd) hU hf hū.1
  exact ⟨w, ū, hw, hwu, hū, hae, huniq⟩

end

end LongRange.Continuum
