import LongRange.Walk.ResolventConvergence
import LatticeProb.External.EthierKurtzTrotterKato

/-!
# Convergence of killed semigroups

Resolvent convergence gives graph approximation on the full generator domain.
The cited Trotter–Kato implication then gives uniform convergence on bounded time intervals.
-/

namespace LongRange

open MeasureTheory Filter Topology LatticeProb LatticeProb.ContractionSemigroup

noncomputable section

variable {d : ℕ}

/-- Almost surely, killed evolutions converge uniformly on bounded time intervals. -/
theorem ae_tendsto_killedSemigroup
    (hTK : External.EthierKurtzTrotterKato)
    (h619 : External.GilbargTrudingerBoundaryRegularity)
    (h66 : External.GilbargTrudingerSchauderEstimate)
    (h37 : External.GilbargTrudingerSupEstimate)
    (h637 : External.GilbargTrudingerHolderExtension)
    (h614 : External.GilbargTrudingerExistence)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : Ω → Edge d → ℝ) (ha : AssumptionU P lam a)
    {μB : Measure (BrownianPath d)} (hμB : IsStandardBrownianLaw μB) :
    ∀ᵐ ξ ∂P, ∀ R : ℕ, ∀ hR : 1 ≤ R,
      let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2)
        (show (0 : ℝ) < R by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
      ∀ εn : ℕ → {ε : ℝ // 0 < ε},
        Tendsto (fun n => (εn n).val) atTop (𝓝 0) →
        UniformSemigroupConvergence
          (fun n => cellAverageLp (εn n).property hU.1.measurableSet hU.2.2.1)
          (continuumSemigroup R (meanConductance P hd a / (2 * d)) hμB)
          (fun n => discreteKilledSemigroup hd (εn n).property ha.lam_pos
            (a ξ) (ha.bounds ξ) hU.2.2.1) := by
  filter_upwards [ae_tendsto_resolvent h619 h66 h37 h637 h614 hd P a ha hμB]
    with ξ hξ
  intro R hR
  dsimp only
  intro εn hεn
  let hU := continuumDomain_isC2HolderDomain (d := d) (1 / 2)
    (show (0 : ℝ) < R by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR))
  let π (n : ℕ) := cellAverageLp (εn n).property hU.1.measurableSet hU.2.2.1
  let T := continuumSemigroup R (meanConductance P hd a / (2 * d)) hμB
  let Tn (n : ℕ) := discreteKilledSemigroup hd (εn n).property ha.lam_pos
    (a ξ) (ha.bounds ξ) hU.2.2.1
  have hseq : Tendsto εn atTop (comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    apply tendsto_comap_iff.mpr
    exact tendsto_nhdsWithin_iff.mpr ⟨hεn, Eventually.of_forall (fun n => (εn n).property)⟩
  apply hTK _ _ π ⟨1, fun n => norm_cellAverageLp_le _ _ _⟩ T Tn
    (generatorSubmodule T) (isCore_generatorSubmodule T)
  intro v _ w hvw
  let f (n : ℕ) := resolvent (Tn n) 1 zero_lt_one (π n (v - w))
  let g (n : ℕ) := f n - π n (v - w)
  have hid : resolvent T 1 zero_lt_one (v - w) = v := by
    simpa only [one_smul] using resolvent_of_mem_generatorGraph T zero_lt_one hvw
  have hf : VaryingConverges π f v := by
    have hlim := (hξ R hR (v - w)).comp hseq
    change Tendsto (fun n => ‖f n - π n (resolvent T 1 zero_lt_one (v - w))‖)
      atTop (𝓝 0) at hlim
    rw [hid] at hlim
    exact hlim
  refine ⟨f, g, ?_, hf, ?_⟩
  · intro n
    simpa only [one_smul] using
      resolvent_mem_generatorGraph (Tn n) zero_lt_one (π n (v - w))
  · have heq (n : ℕ) : g n - π n w = f n - π n v := by
      dsimp only [g]
      rw [map_sub]
      abel
    simpa only [VaryingConverges, heq] using hf

end

end LongRange
