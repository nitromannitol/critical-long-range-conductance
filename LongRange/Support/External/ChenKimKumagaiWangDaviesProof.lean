import LongRange.Support.Analysis.Davies.DaviesFinite
import LongRange.Support.Analysis.Davies.KilledBound

/-!
# Davies heat kernel bound for bounded-rate chains

The finite-form Davies estimate passes to a countable state space by exhaustion
with finite killed chains.
-/

namespace LatticeProb.External

open scoped NNReal ENNReal

/-- The discrete Davies heat kernel estimate of Chen–Kim–Kumagai–Wang. -/
theorem chenKimKumagaiWangDavies_holds : ChenKimKumagaiWangDavies := by
  classical
  intro c₁ c₂ c C hc₁ hc₂ hdata ε hε
  obtain ⟨A, a, hA, ha, hfinite⟩ :=
    Davies.FiniteJumpForm.davies c₁ c₂ c C hc₁ hc₂ hdata ε hε
  refine ⟨A, a, hA, ha, ?_⟩
  intro θ θstar φ hinv hprofile hpos hmono hratio hcompare S _ _ _ rates hs
    δ hδ hN ψ _ hΛ t ht i j
  apply Davies.ckkwKernel_le_of_semigroup_bound_at rates hs t i j
  intro U hi hj
  exact hfinite θ θstar φ hinv hprofile hpos hmono hratio hcompare U
    (Davies.killedForm rates hs U) δ hδ (Davies.killedForm_nash rates hs U θ δ hN)
    (ψ ∘ (↑)) (ckkwLambdaSq rates ψ).toReal
    (Davies.killedForm_lambdaBound rates hs U ψ hΛ) t (by exact_mod_cast ht)
    ⟨i, hi⟩ ⟨j, hj⟩

end LatticeProb.External
