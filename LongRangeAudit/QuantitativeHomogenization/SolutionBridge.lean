import LongRangeAudit.QuantitativeHomogenization.SolutionBasic
import LongRange.TwoScale.WeakMain

/-!
# Equivalence with the production vocabulary

Explicit two-way transport of test functions, the actual Sobolev closure, the integrable
weak equation and the conductance assumption. All other scalar definitions agree by reduction.
-/

namespace LongRangeAudit.QuantitativeHomogenization

noncomputable section
open MeasureTheory
open LatticeProb LatticeProb.Elliptic LatticeProb.Elliptic.WeakDirichlet

namespace Conversion

variable {d : ℕ} {U : Set (Fin d → ℝ)}

/-- The same smooth function and its support certificates in the production carrier. -/
def testTo (φ : TestFunction U) : _root_.LatticeProb.Elliptic.WeakDirichlet.TestFunction U :=
  ⟨φ.val, φ.smooth, φ.compact, φ.supported⟩

/-- The same production smooth function in the isolated carrier. -/
def testFrom (φ : _root_.LatticeProb.Elliptic.WeakDirichlet.TestFunction U) : TestFunction U :=
  ⟨φ.val, φ.smooth, φ.compact, φ.supported⟩

/-- The smooth graph ranges coincide as subsets of the identical L² product. -/
theorem graph_range_eq : Set.range (TestFunction.graph (U := U)) =
    Set.range (_root_.LatticeProb.Elliptic.WeakDirichlet.TestFunction.graph (U := U)) := by
  ext v
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨testTo φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨testFrom φ, rfl⟩

/-- Transport preserves every L² coordinate, with membership in the literal closure. -/
def h10To (w : H10 U) : _root_.LatticeProb.Elliptic.WeakDirichlet.H10 U :=
  ⟨w.val, by rw [← graph_range_eq]; exact w.property⟩

/-- Reverse transport also preserves all coordinates of the Sobolev graph. -/
def h10From (w : _root_.LatticeProb.Elliptic.WeakDirichlet.H10 U) : H10 U :=
  ⟨w.val, by rw [graph_range_eq]; exact w.property⟩

/-- Reverse transport is a left inverse on the complete Sobolev graph. -/
theorem h10From_to (w : H10 U) : h10From (h10To w) = w := rfl

/-- Forward transport is a left inverse on the production Sobolev graph. -/
theorem h10To_from (w : _root_.LatticeProb.Elliptic.WeakDirichlet.H10 U) :
    h10To (h10From w) = w := rfl

/-- The integral identity and both integrability clauses are equivalent in both carriers. -/
theorem weak_iff (μ a₀ : ℝ) (f : (Fin d → ℝ) → ℝ) (w : H10 U) :
    IsWeakSolution U μ a₀ f w ↔
      _root_.LatticeProb.Elliptic.WeakDirichlet.IsWeakSolution U μ a₀ f (h10To w) := by
  constructor
  · intro h φ
    exact h (testFrom φ)
  · intro h φ
    exact h (testTo φ)

/-- All eight fields of the conductance assumption agree, including the actual iid law. -/
theorem assumption_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ)
    (a : Ω → LongRange.Edge d → ℝ) :
    LongRange.AssumptionU P lam a ↔ _root_.LongRange.AssumptionU P lam a := by
  constructor <;> intro h
  · exact ⟨h.one_le_dim, h.lam_pos, h.lam_le_one, h.isProbabilityMeasure,
      h.measurable, h.iIndep, h.identDistrib, h.bounds⟩
  · exact ⟨h.one_le_dim, h.lam_pos, h.lam_le_one, h.isProbabilityMeasure,
      h.measurable, h.iIndep, h.identDistrib, h.bounds⟩

/-- The cited approximation proposition is equivalent under the smooth test conversion. -/
theorem approximation_iff : LatticeProb.External.GilbargTrudingerZeroBoundaryApproximation ↔
    _root_.LatticeProb.External.GilbargTrudingerZeroBoundaryApproximation := by
  constructor
  · intro h d hd U ho hc hb v hv u hu hz hae
    rw [← graph_range_eq]
    exact h d hd U ho hc hb v (fun ψ i => hv (testTo ψ) i) u hu hz hae
  · intro h d hd U ho hc hb v hv u hu hz hae
    rw [graph_range_eq]
    exact h d hd U ho hc hb v (fun ψ i => hv (testFrom ψ) i) u hu hz hae

/-- The cited uniqueness proposition is equivalent on the entire H¹₀ carrier. -/
theorem uniqueness_iff : LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness ↔
    _root_.LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness := by
  constructor
  · intro h d hd U ho hc hb a₀ μ ha hμ w hw
    exact h d hd U ho hc hb a₀ μ ha hμ (h10From w)
      ((weak_iff μ a₀ (fun _ => 0) (h10From w)).mpr hw)
  · intro h d hd U ho hc hb a₀ μ ha hμ w hw
    exact h d hd U ho hc hb a₀ μ ha hμ (h10To w) ((weak_iff μ a₀ _ w).mp hw)

end Conversion

open LatticeProb.Euclidean.Lattice LongRange

/-- The full source main estimate produces the unique weak solution and representative. -/

theorem main_estimate
    (h614 : LatticeProb.External.GilbargTrudingerExistence)
    (h619 : LatticeProb.External.GilbargTrudingerBoundaryRegularity)
    (h66 : LatticeProb.External.GilbargTrudingerSchauderEstimate)
    (h37 : LatticeProb.External.GilbargTrudingerSupEstimate)
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    (h75 : LatticeProb.External.GilbargTrudingerZeroBoundaryApproximation)
    (h82 : LatticeProb.External.GilbargTrudingerWeakHomogeneousUniqueness)
    (d : ℕ) (hd : 1 ≤ d) (lam σ μ : ℝ) (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) (hμ : 0 ≤ μ)
    (U : Set (Fin d → ℝ)) (hU : IsC2HolderDomain σ U) (M : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ f : (Fin d → ℝ) → ℝ, c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M →
      ∃ w : H10 U, ∃ ū : (Fin d → ℝ) → ℝ,
        IsWeakSolution U μ (meanConductance P hd a / (2 * d)) f w ∧
        (∀ z : H10 U, IsWeakSolution U μ (meanConductance P hd a / (2 * d)) f z →
          z = w) ∧
        (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū ∧
        (IsClassicalDirichletSolution U μ (meanConductance P hd a / (2 * d)) f ū ∧
          Continuous ū ∧ ∀ x ∉ U, ū x = 0) ∧
        (∀ v, (IsClassicalDirichletSolution U μ
          (meanConductance P hd a / (2 * d)) f v ∧ Continuous v ∧
            ∀ x ∉ U, v x = 0) → v = ū) ∧
        ∃ 𝒳 : Ω → ENNReal, Measurable 𝒳 ∧
          (∀ s : ℝ, 1 ≤ s → P {ω | ENNReal.ofReal s < 𝒳 ω} ≤
            ENNReal.ofReal (C * Real.exp (-(c * s)))) ∧
          ∀ v : (Fin d → ℝ) → ℝ, IsClassicalDirichletSolution U μ
              (meanConductance P hd a / (2 * d)) f v →
            ∀ ω, ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
              𝒳 ω ≤ ENNReal.ofReal |Real.log ε| →
              ∀ u : Site d → ℝ, SupportedIn ε U u →
                (∀ q ∈ latticeSet ε U,
                  μ * u q - generator ε (a ω) u q = f (physical ε q)) →
                l2Norm ε U (fun q => u q - v (physical ε q)) ≤
                  C / Real.sqrt |Real.log ε|  := by
  obtain ⟨C, c, hC, hc, hmain⟩ :=
    _root_.LongRange.TwoScale.exists_weak_solution_main_estimate
      h614 h619 h66 h37 h637 (Conversion.approximation_iff.mp h75)
      (Conversion.uniqueness_iff.mp h82) d hd lam σ μ hσ hμ U hU M
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω _ P a hA f hf
  obtain ⟨w, ū, hw, hwu, hae, hclass, huniq, X, hmeas, htail, herr⟩ :=
    hmain P a ((Conversion.assumption_iff P lam a).mp hA) f hf
  refine ⟨Conversion.h10From w, ū,
    (Conversion.weak_iff μ _ f (Conversion.h10From w)).mpr hw, ?_,
    hae, hclass, huniq, X, hmeas, htail, herr⟩
  intro z hz
  apply Subtype.ext
  exact congrArg (fun t : _root_.LatticeProb.Elliptic.WeakDirichlet.H10 U => t.val)
    (hwu (Conversion.h10To z) ((Conversion.weak_iff μ _ f z).mp hz))

end

end LongRangeAudit.QuantitativeHomogenization
