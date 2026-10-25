import LongRangeAudit.QuenchedInvariance.Vocabulary.GilbargTrudinger

/-! # Independent GilbargTrudingerExistence vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

noncomputable section
namespace LatticeProb.External
open MeasureTheory LatticeProb.Elliptic
variable {d : ℕ}

/-- Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
in Mathematics (Springer, 2001; reprint of the 1998 edition), Theorem 6.14, printed p. 107,
for operator `a₀ Δ − μ`, right side `−f` and zero boundary data. The conclusion retains
existence and finite interior coordinate norm; no uniqueness of total extensions is claimed. -/
def GilbargTrudingerExistence : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (U : Set (Fin d → ℝ)), IsC2HolderDomain σ U →
      ∀ (a₀ μ : ℝ), 0 < a₀ → 0 ≤ μ →
        ∀ (f : (Fin d → ℝ) → ℝ), c0HolderNorm σ (closure U) f < ⊤ →
          ∃ u : (Fin d → ℝ) → ℝ,
            IsClassicalDirichletSolution U μ a₀ f u ∧ c2HolderNorm σ U u < ⊤

end LatticeProb.External
end

end LongRangeAudit.QuenchedInvariance
