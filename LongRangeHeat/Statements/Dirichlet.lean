import LongRangeHeat.Dirichlet

/-!
# Lemma 2.1: properties of the Dirichlet form

Statement of Lemma 2.1 (`lem:Dirichlet`) of the heat-kernel version: integration by parts
`⟨L^ε v₁, v₂⟩ = -B_a(v₁, v₂)` on `L²(εℤ^d)` and the coercivity bound
`B_a(v, v) ≥ (c / κ_ε) ‖D v‖²`, with `c` depending only on `d` and `λ`.
-/

namespace LongRangeHeat.Statements

open LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (generator kappa jumpKernel bilinForm Edge edgeAdd)

/-- **Lemma 2.1** (`lem:Dirichlet`, properties of the Dirichlet form). There is `c > 0`,
depending only on `d` and `λ`, such that for every `ε ∈ (0, 1/2)` and every realization `a` of
the conductances with values in `[λ, λ⁻¹]`:
(i) for all `v₁, v₂ ∈ L²(εℤ^d)`, `L^ε v₁ ∈ L²(εℤ^d)`, the series of `⟨L^ε v₁, v₂⟩` and the
double series (2.2) of `B_a(v₁, v₂)` converge absolutely, and `⟨L^ε v₁, v₂⟩ = -B_a(v₁, v₂)`
(2.5);
(ii) for every `v ∈ L²(εℤ^d)`, each `D_i v` lies in `L²(εℤ^d)` and
`B_a(v, v) ≥ (c / κ_ε) ‖D v‖²`. -/
theorem dirichlet_form {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      (∀ v₁ v₂ : Site d → ℝ, MemL2 v₁ → MemL2 v₂ →
        MemL2 (generator ε a v₁) ∧
        Summable (fun q => generator ε a v₁ q * v₂ q) ∧
        Summable (fun p : Site d × Site d => if hw : p.2 = 0 then 0 else
          a (edgeAdd p.1 p.2 hw) * jumpKernel (physical ε p.2) *
            (v₁ (p.1 + p.2) - v₁ p.1) * (v₂ (p.1 + p.2) - v₂ p.1)) ∧
        latticeInner ε (generator ε a v₁) v₂ = -bilinForm ε a v₁ v₂) ∧
      (∀ v : Site d → ℝ, MemL2 v →
        (∀ i, MemL2 (discreteDeriv ε i v)) ∧
        c / kappa d ε * gradNormSq ε v ≤ bilinForm ε a v v) := by
  refine ⟨lam / 2, half_pos hlam.1, fun ε hε a ha => ⟨fun v₁ v₂ h₁ h₂ => ?_, fun v hv => ?_⟩⟩
  · have hg := memL2_generator hd hε.1 hlam.1 ha h₁
    exact ⟨hg, summable_mul_of_memL2 hg h₂,
      summable_bilinForm_summand hd hε.1 hlam.1 ha h₁ h₂,
      latticeInner_generator_eq_neg_bilinForm (summable_generatorPair hd hε.1 hlam.1 ha h₁ h₂)⟩
  · exact ⟨fun i => memL2_discreteDeriv hv ε i, bilinForm_self_ge hd hε.1 hlam.1 ha hv⟩

end LongRangeHeat.Statements
