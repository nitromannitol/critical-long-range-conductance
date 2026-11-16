import LongRangeHeat.FddExpectation
import LongRangeHeat.Annealed
import LongRangeHeat.WalkMarkov

/-!
# Products of observations under the quenched and annealed laws

For observables `g_i` on `ℝ^d` and times `t_0 ≤ ⋯ ≤ t_k`, the expectation of
`∏ g_i(X^ε_{t_i})` under the quenched law is the backward recursion `chainExp`
(Markov property), and under the annealed law it is the average over the conductances of this
quantity, which is a measurable function of the environment.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Cadlag.HalfLine
  LatticeProb.JumpChain LatticeProb.Euclidean.Lattice Set Filter
open scoped NNReal ENNReal Topology
open LongRange (Edge walkRates walkEmbed)

noncomputable section

section Bind

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]

/-- The integral against a mixture of probability measures is the mixture of the integrals. -/
theorem integral_bind_of_integrable (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure β)
    (hμ : Measurable μ) [∀ r, IsProbabilityMeasure (μ r)] {f : β → ℝ}
    (hf : Integrable f (P.bind μ)) : ∫ x, f x ∂(P.bind μ) = ∫ r, ∫ x, f x ∂(μ r) ∂P := by
  let κ : Kernel Ω β := ⟨μ, hμ⟩
  have hbind : P.bind μ = (κ ∘ₖ Kernel.const Unit P) () := by
    rw [← Measure.comp_eq_comp_const_apply]
    rfl
  rw [hbind] at hf ⊢
  rw [Kernel.integral_comp hf]
  simp [κ]

end Bind

section Quenched

variable {d : ℕ}

/-- The observable `∏ g_i(x_i)` of the observations of a path. -/
def pathProd {k : ℕ} (t : Fin k → ℝ≥0) (g : Fin k → (Fin d → ℝ) → ℝ) (X : PathSpace d) : ℝ :=
  ∏ i, g i (WithLp.ofLp (X.1 (t i)))

theorem measurable_pathProd {k : ℕ} (t : Fin k → ℝ≥0) {g : Fin k → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, Continuous (g i)) : Measurable (pathProd t g) :=
  Finset.measurable_prod _ fun i _ =>
    ((hg i).measurable.comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable).comp
      (measurable_eval (t i))

theorem abs_pathProd_le {k : ℕ} (t : Fin k → ℝ≥0) {g : Fin k → (Fin d → ℝ) → ℝ} {M : ℝ}
    (hg : ∀ i x, |g i x| ≤ M) (X : PathSpace d) : |pathProd t g X| ≤ M ^ k := by
  unfold pathProd
  calc |∏ i, g i (WithLp.ofLp (X.1 (t i)))| = ∏ i, |g i (WithLp.ofLp (X.1 (t i)))| :=
        Finset.abs_prod _ _
    _ ≤ ∏ _i : Fin k, M := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hg i _
    _ = M ^ k := by simp

/-- Markov property for the quenched law: the expectation of a product of observations of the walk
started at the origin is the backward recursion `chainExp`. -/
theorem integral_quenchedLaw_pathProd (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {lam : ℝ}
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {k : ℕ}
    (t : Fin k → ℝ≥0) (ht : Monotone t) {g : Fin k → (Fin d → ℝ) → ℝ}
    (hgc : ∀ i, Continuous (g i)) {M : ℝ} (hM : 0 ≤ M) (hg : ∀ i x, |g i x| ≤ M) :
    ∫ X, pathProd t g X ∂(quenchedLaw hd hε hlam a ha 0 : Measure (PathSpace d)) =
      chainExp (walkRates hd hε hlam a ha) k (timeIncr t) (fun i => restrict ε (g i)) 0 := by
  have hmeas := measurable_pathProd t hgc
  have hmap : (quenchedLaw hd hε hlam a ha 0 : Measure (PathSpace d)) =
      Measure.map (RegularHistory.halfLinePath (walkEmbed ε))
        ((walkRates hd hε hlam a ha).regularLaw (Measure.dirac 0)) := rfl
  rw [hmap, integral_map (measurable_halfLinePath _).aemeasurable hmeas.aestronglyMeasurable,
    ← integral_regularLaw_prod_position (walkRates hd hε hlam a ha) 0 t ht hM
      (fun i => restrict ε (g i)) (fun i y => hg i _)]
  rfl

end Quenched

end

end LongRangeHeat
