import LongRange.Scaling.WeakObstruction

/-!
# Scaling obstruction for weak source solutions

The full weak source scaling obstruction, including the produced half-domain weak solution.
-/

namespace LongRange.Statements

open Filter MeasureTheory LatticeProb LatticeProb.Elliptic
open LongRange.Scaling
open LatticeProb.Elliptic.WeakDirichlet LatticeProb.Euclidean.Lattice
open scoped Topology

variable {d : ℕ}

/-- The full weak source scaling obstruction, including the produced half-domain weak solution. -/

theorem weak_scaling_obstruction
    (h614 : External.GilbargTrudingerExistence)
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h75 : External.GilbargTrudingerZeroBoundaryApproximation)
    (h82 : External.GilbargTrudingerWeakHomogeneousUniqueness)
    (hd : 1 ≤ d) {σ a₀ lam : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (ha₀ : 0 < a₀) {U : Set (Fin d → ℝ)} (hU : IsC2HolderDomain σ U)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {M : ℝ} (f : (Fin d → ℝ) → ℝ)
    (hf : c0HolderNorm σ (closure U) f ≤ ENNReal.ofReal M)
    (w : H10 U) (hw : IsWeakSolution U 0 a₀ f w) (hn : w.val 0 ≠ 0)
    (u v : ℝ → Site d → ℝ)
    (hu : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε U (u ε))
    (hv : ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      SupportedIn (ε / 2) (halfDomain U) (v ε))
    (heu : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet ε U,
      -generator ε a (u ε) q = f (physical ε q))
    (hev : ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      ∀ q ∈ latticeSet (ε / 2) (halfDomain U),
        -generator (ε / 2) a (v ε) q = 4 * f ((2 : ℝ) • physical (ε / 2) q)) :
    ∃ ū : (Fin d → ℝ) → ℝ,
      (IsClassicalDirichletSolution U 0 a₀ f ū ∧ Continuous ū ∧
        ∀ x ∉ U, ū x = 0) ∧
      (∀ z, (IsClassicalDirichletSolution U 0 a₀ f z ∧ Continuous z ∧
        ∀ x ∉ U, z x = 0) → z = ū) ∧
      (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū ∧
      (∃ x ∈ U, ū x ≠ 0) ∧
      IsOpen (halfDomain U) ∧ IsConnected (halfDomain U) ∧
      Bornology.IsBounded (halfDomain U) ∧
      IsClassicalDirichletSolution (halfDomain U) 0 a₀
        (fun x => 4 * f ((2 : ℝ) • x)) (fun x => ū ((2 : ℝ) • x)) ∧
      (∃ wh : H10 (halfDomain U),
        IsWeakSolution (halfDomain U) 0 a₀ (fun x => 4 * f ((2 : ℝ) • x)) wh ∧
        (fun x => wh.val 0 x) =ᵐ[volume.restrict (halfDomain U)]
          (fun x => ū ((2 : ℝ) • x)) ∧
        ∀ z : H10 (halfDomain U),
          IsWeakSolution (halfDomain U) 0 a₀ (fun x => 4 * f ((2 : ℝ) • x)) z →
          z = wh) ∧
      ¬ (Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
          (fun ε => l2Norm ε U (fun q => u ε q - ū (physical ε q)))
          (fun ε => 1 / |Real.log ε|) ∧
        Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
          (fun ε => l2Norm (ε / 2) (halfDomain U)
            (fun q => v ε q - ū ((2 : ℝ) • physical (ε / 2) q)))
          (fun ε => 1 / |Real.log ε|)) :=

by
  exact LongRange.Scaling.weak_source_scaling_obstruction
    h614 h619 h66 h37 h637 h75 h82 hd hσ ha₀ hU hlam ha f hf w hw hn u v hu hv heu hev

end LongRange.Statements
