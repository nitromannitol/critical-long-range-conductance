import LongRange.Walk.Tightness

/-!
# tightness of the rescaled walks

A statement-preserving wrapper for Proposition 6.1 (`p.tightness`). The Murugan–Saloff-Coste,
Chen–Kim–Kumagai–Wang, Ethier–Kurtz and Billingsley results are cited inputs taken as explicit
hypotheses.
-/

open MeasureTheory LongRange LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.Cadlag.HalfLine

/-- Proposition 6.1 (`p.tightness`): let `T > 0` and, for each `ε ∈ (0,1)`, let `X^ε` be the
càdlàg Markov process on `εℤ^d` with generator `𝓛^ε` for conductances `λ ≤ a ≤ λ⁻¹`. If the
initial laws `Law(X^ε_0)` are tight, then the family `(X^ε)` is tight in `D([0,T]; ℝ^d)`. -/

theorem LongRange.Statements.tightness
    (hMSC : LatticeProb.External.MuruganSaloffCoste)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hRC : LatticeProb.External.EthierKurtzRelativeCompactness)
    (hPol : LatticeProb.External.BillingsleySkorokhodPolish)
    (d : ℕ) (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (T : ℝ) (hT : 0 < T)
    (μ : Set.Ioo (0 : ℝ) 1 → Measure (Site d)) [∀ ε, IsProbabilityMeasure (μ ε)]
    (hμ : IsTightMeasureSet {Measure.map (walkEmbed ε.1) (μ ε) | (ε : Set.Ioo (0 : ℝ) 1)}) :
    IsTightMeasureSet {(((pathLaw (walkRates hd ε.2.1 hlam a ha) (μ ε) (walkEmbed ε)).map
      (measurable_restrict T).aemeasurable :
        ProbabilityMeasure (LatticeProb.Cadlag.D T (EuclideanSpace ℝ (Fin d)))) :
          Measure (LatticeProb.Cadlag.D T (EuclideanSpace ℝ (Fin d)))) | ε} :=

by exact walk_restrict_isTight hMSC hNash hDavies hRC hPol hd hlam a ha T hT μ hμ
