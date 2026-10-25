import LongRangeAudit.QuenchedInvariance.SolutionBasic
import LongRange.Walk.InvariancePrinciple

/-! # Identification of the independent QIP vocabulary with the proved providers. -/

namespace LongRangeAudit.QuenchedInvariance

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

/-- Copy a bounded rate matrix, retaining its exact uniformization rate and every row. -/
def ratesCopy {S : Type*} (r : _root_.LatticeProb.JumpChain.BoundedRates S) :
    LatticeProb.JumpChain.BoundedRates S :=
  ⟨r.q, r.q_nonneg, r.q_self, r.summable, r.R, r.R_pos, r.total_le⟩

/-- Copy a strongly continuous contraction semigroup without changing its operators. -/
def semigroupCopy {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    (T : _root_.LatticeProb.ContractionSemigroup.StronglyContinuousContractionSemigroup L) :
    LatticeProb.ContractionSemigroup.StronglyContinuousContractionSemigroup L :=
  ⟨T.operator, T.map_zero, T.map_add, T.norm_le_one, T.continuous_orbit⟩

/-- Copy a locally finite weighted graph with the identical graph and edge weights. -/
def graphCopy {X : Type*} (G : _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph X) :
    LatticeProb.Graph.LongRangeKernel.WeightedGraph X :=
  ⟨G.graph, G.locallyFinite, G.weight, G.symmetric, G.positive_iff⟩

/-- The independently stated Trotter–Kato input implies the production input. -/
theorem trotterKato (h : LatticeProb.External.EthierKurtzTrotterKato) :
    _root_.LatticeProb.External.EthierKurtzTrotterKato := by
  intro L _ _ _ Ln _ _ _ π hπ T Tn D hcore hgraph
  exact h L Ln π hπ (semigroupCopy T) (fun n => semigroupCopy (Tn n)) D hcore hgraph

/-- Iteration of a density agrees at every natural time in the two vocabularies. -/
theorem densityPower_eq {X : Type*} (m : X → ℝ≥0) (k : X → X → ℝ≥0∞) (n : ℕ) :
    LatticeProb.Graph.LongRangeKernel.densityPower m k n =
      _root_.LatticeProb.Graph.LongRangeKernel.densityPower m k n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x y
    change (∑' z, k x z * LatticeProb.Graph.LongRangeKernel.densityPower m k n z y *
      (m z : ℝ≥0∞)) = _
    rw [ih]
    rfl

/-- Graph distances are computed on the identical simple graph. -/
theorem graph_dist_eq {X : Type*}
    (G : _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph X) (x y : X) :
    (graphCopy G).graph.dist x y = G.graph.dist x y := rfl

/-- Vertex masses retain the exact neighbour finset and weights. -/
theorem graph_mass_eq {X : Type*}
    (G : _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph X) :
    (graphCopy G).mass = G.mass := rfl

/-- Graph balls and their mass volumes are unchanged by copying. -/
theorem graph_volume_eq {X : Type*}
    (G : _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph X) :
    (graphCopy G).volume = G.volume := rfl

/-- Reference densities use the identical two vertex masses. -/
theorem graph_reference_eq {X : Type*}
    (G : _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph X) :
    (graphCopy G).referenceDensity = G.referenceDensity := rfl

/-- The jump-scale predicates have the same regular-variation body. -/
theorem jumpScale_iff (φ : ℝ → ℝ) :
    LatticeProb.Graph.LongRangeKernel.IsJumpScale φ ↔
      _root_.LatticeProb.Graph.LongRangeKernel.IsJumpScale φ := Iff.rfl

/-- The inverse-scale predicates have the same integral scale and asymptotic body. -/
theorem inverseScale_iff (γ : ℝ) (φ ζ : ℝ → ℝ) :
    LatticeProb.Graph.LongRangeKernel.IsInverseScale γ φ ζ ↔
      _root_.LatticeProb.Graph.LongRangeKernel.IsInverseScale γ φ ζ := Iff.rfl

/-- The independently stated MSC input implies the production input. -/
theorem muruganSaloffCoste (h : LatticeProb.External.MuruganSaloffCoste) :
    _root_.LatticeProb.External.MuruganSaloffCoste := by
  intro X G hInf hConn V φ γ k hm hV hv hp hγ hu hl hφ hMarkov hSym hk ζ hζ
  have result := h X (graphCopy G) hInf hConn V φ γ k hm hV hv hp hγ
    (by simpa only [LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          densityPower_eq, graph_mass_eq, graph_reference_eq, graph_dist_eq] using hu)
    (by simpa only [LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          _root_.LatticeProb.Graph.LongRangeKernel.WeightedGraph.heat,
          densityPower_eq, graph_mass_eq, graph_reference_eq, graph_dist_eq] using hl)
    hφ hMarkov hSym hk ζ hζ
  simpa only [LatticeProb.Graph.LongRangeKernel.evenKernelSup,
    _root_.LatticeProb.Graph.LongRangeKernel.evenKernelSup, densityPower_eq,
    graph_mass_eq] using result

/-- The independently stated CKKW Nash input implies the production input. -/
theorem chenKimKumagaiWangNash (h : LatticeProb.External.ChenKimKumagaiWangNash) :
    _root_.LatticeProb.External.ChenKimKumagaiWangNash := by
  intro S _ _ _ rates
  exact h S (ratesCopy rates)

/-- The independently stated CKKW Davies input implies the production input. -/
theorem chenKimKumagaiWangDavies (h : LatticeProb.External.ChenKimKumagaiWangDavies) :
    _root_.LatticeProb.External.ChenKimKumagaiWangDavies := by
  intro c₁ c₂ c C h₁ h₂ hc ε hε
  obtain ⟨A, a, hA, ha, h⟩ := h c₁ c₂ c C h₁ h₂ hc ε hε
  refine ⟨A, a, hA, ha, ?_⟩
  intro θ θstar φ hInv hProd hPos hMono hRatio hCompare S _ _ _ rates
  exact h θ θstar φ hInv hProd hPos hMono hRatio hCompare S (ratesCopy rates)

/-- The iid unordered-edge assumptions retain all eight fields. -/
theorem assumption {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {lam : ℝ} {a : Ω → LongRange.Edge d → ℝ}
    (h : LongRange.AssumptionU P lam a) : _root_.LongRange.AssumptionU P lam a :=
  ⟨h.one_le_dim, h.lam_pos, h.lam_le_one, h.isProbabilityMeasure, h.measurable,
    h.iIndep, h.identDistrib, h.bounds⟩

/-- Recover the same bounded rates from the independent copy. -/
def ratesOriginal {S : Type*} (r : LatticeProb.JumpChain.BoundedRates S) :
    _root_.LatticeProb.JumpChain.BoundedRates S :=
  ⟨r.q, r.q_nonneg, r.q_self, r.summable, r.R, r.R_pos, r.total_le⟩

/-- Copying rates in both directions preserves the full structure. -/
theorem rates_roundtrip {S : Type*} (r : LatticeProb.JumpChain.BoundedRates S) :
    ratesCopy (ratesOriginal r) = r := rfl

/-- The independent and production history pushforwards are exactly the same law. -/
theorem pathLaw_eq {S E : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MetricSpace E] [SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] (r : LatticeProb.JumpChain.BoundedRates S)
    (μ : MeasureTheory.Measure S) [MeasureTheory.IsProbabilityMeasure μ] (ι : S → E) :
    LatticeProb.Cadlag.HalfLine.pathLaw r μ ι =
      _root_.LatticeProb.Cadlag.HalfLine.pathLaw (ratesOriginal r) μ ι := rfl

/-- Both constructions use the same Euclidean rescaled rate matrix and clock rate. -/
theorem walkRates_eq {d : ℕ} (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : LongRange.Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) :
    ratesOriginal (LongRange.walkRates hd hε hlam a ha) =
      _root_.LongRange.walkRates hd hε hlam a ha := rfl

/-- Both initial probability laws use the identical full-cell integral weights. -/
theorem initialLaw_eq {d : ℕ} (ε : ℝ) (g : (Fin d → ℝ) → ℝ) (hε : 0 < ε)
    (hg : MeasureTheory.Integrable g MeasureTheory.volume)
    (hg0 : ∀ᵐ x ∂MeasureTheory.volume, 0 ≤ g x) (hg1 : ∫ x, g x = 1) :
    LongRange.initialLaw ε g hε hg hg0 hg1 =
      _root_.LongRange.initialLaw ε g hε hg hg0 hg1 := rfl

/-- Both Brownian predicates retain the coordinate Brownian laws and their independence. -/
theorem brownianLaw_iff {d : ℕ} (μ : MeasureTheory.Measure (LatticeProb.BrownianPath d)) :
    LatticeProb.IsStandardBrownianLaw μ ↔ _root_.LatticeProb.IsStandardBrownianLaw μ :=
  Iff.rfl

/-- The detailed path topology has exactly the production metric, including its infimum. -/
theorem path_metric_eq {E : Type*} [MetricSpace E]
    (x y : LatticeProb.Cadlag.HalfLine.D E) :
    LatticeProb.Cadlag.HalfLine.skorohodDistance x y =
      _root_.LatticeProb.Cadlag.HalfLine.skorohodDistance x y := rfl

/-- The two independent Ethier–Kurtz finite-dimensional inputs are literally equivalent. -/
theorem ethierKurtzFdd_iff : LatticeProb.External.EthierKurtzConvergenceFromFdd ↔
    _root_.LatticeProb.External.EthierKurtzConvergenceFromFdd := Iff.rfl

/-- The two independent Ethier–Kurtz relative compactness inputs are literally equivalent. -/
theorem ethierKurtzRelativeCompactness_iff :
    LatticeProb.External.EthierKurtzRelativeCompactness ↔
      _root_.LatticeProb.External.EthierKurtzRelativeCompactness := Iff.rfl

end
end LongRangeAudit.QuenchedInvariance
