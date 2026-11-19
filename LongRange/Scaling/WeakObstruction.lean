import LongRange.Continuum.Weak
import LongRange.Scaling.Obstruction

/-!
# The scaling obstruction for actual weak source solutions

A nonzero H¹₀ value determines a nonzero canonical classical representative.
Its global C² extension produces the weak solution on the actual half-domain.
-/

namespace LongRange.Scaling

open Filter MeasureTheory LatticeProb LatticeProb.Elliptic
open LatticeProb.Elliptic.WeakDirichlet LatticeProb.Euclidean.Lattice
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- A nonzero L² value agreeing almost everywhere with a function has a nonzero
point in the open domain. This uses the actual value coordinate, not its norm as an input. -/
theorem exists_nonzero_of_value_ne_zero {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {w : H10 U} {ū : (Fin d → ℝ) → ℝ} (hn : w.val 0 ≠ 0)
    (hae : (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū) :
    ∃ x ∈ U, ū x ≠ 0 := by
  by_contra h
  push Not at h
  apply hn
  apply Lp.ext
  have hz : ū =ᵐ[volume.restrict U] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact h x hx
  exact (hae.trans hz).trans (Lp.coeFn_zero _ _ _).symm

/-- The original weak source surface produces the canonical representative and its
half-domain weak solution; the two discrete source errors cannot both be little-o. -/
theorem weak_source_scaling_obstruction
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
          (fun ε => 1 / |Real.log ε|)) := by
  obtain ⟨ū, hū, huniq⟩ := existsUnique_zero_extended_classicalDirichletSolution
    h614 h37 hd hσ.1 hσ.2 hU (by norm_num : (0 : ℝ) ≤ 0) ha₀
      (hf.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨V, hV, heq, hz, hpde, z, hzw, hae, _, _, _⟩ :=
    Continuum.classical_solution_has_weak_graph h619 h66 h37 h637 h75 h82 hd hσ
      (by norm_num) ha₀ hU hf hū.1
  have hwz : w = z := hw.eq_of_same_data h82 (by omega) hU.1 hU.2.1
    hU.2.2.1 ha₀ (by norm_num) hzw
  have hwae : (fun x => w.val 0 x) =ᵐ[volume.restrict U] ū := hwz ▸ hae
  have hne := exists_nonzero_of_value_ne_zero hU.1 hn hwae
  have hopen : IsOpen (halfDomain U) := hU.1.preimage (doubleEquiv (d := d)).continuous
  have hconn : IsConnected (halfDomain U) :=
    (doubleEquiv (d := d)).toHomeomorph.isConnected_preimage.mpr hU.2.1
  have hbound := halfDomain_isBounded hU.2.2.1
  have hVh : ContDiff ℝ 2 (fun x => V ((2 : ℝ) • x)) :=
    hV.comp (by fun_prop)
  have hzh : Set.EqOn (fun x => V ((2 : ℝ) • x)) (fun _ => 0)
      (frontier (halfDomain U)) := by
    intro x hx
    apply hz
    have he := (doubleEquiv (d := d)).toHomeomorph.preimage_frontier U
    change x ∈ (doubleEquiv (d := d)).toHomeomorph ⁻¹' frontier U
    rw [he]
    exact hx
  have hpdeh : ∀ x ∈ halfDomain U,
      0 * V ((2 : ℝ) • x) -
        a₀ * laplacian (fun y => V ((2 : ℝ) • y)) x = 4 * f ((2 : ℝ) • x) := by
    intro x hx
    rw [laplacian_double]
    have hh := hpde ((2 : ℝ) • x) hx
    linarith
  let wh := classicalH10 h75 (by omega) hVh hbound hopen hconn hzh
  have hwh : IsWeakSolution (halfDomain U) 0 a₀
      (fun x => 4 * f ((2 : ℝ) • x)) wh :=
    classicalH10_isWeakSolution h75 (by omega) hVh hbound hopen hconn hzh
      0 a₀ _ hpdeh
  have hcoords := (eq_classicalH10_iff h75 (by omega) hVh hbound hopen hconn hzh wh).mp rfl
  obtain ⟨hhalf, hob⟩ := source_scaling_obstruction hd hU.2.2.1 hlam ha f ū
    hū.1 hne u v hu hv heu hev
  refine ⟨ū, hū, huniq, hwae, hne, hopen, hconn, hbound, hhalf, ?_, hob⟩
  refine ⟨wh, hwh, ?_, ?_⟩
  · apply hcoords.1.trans
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    exact heq hx
  · intro z hz
    exact hz.eq_of_same_data h82 (by omega) hopen hconn hbound ha₀ (by norm_num) hwh

end

end LongRange.Scaling
