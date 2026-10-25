import LongRangeAudit.QuenchedInvariance.Vocabulary.MuruganSaloffCoste

/-! # Independent ChenKimKumagaiWang vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# Chen–Kim–Kumagai–Wang heat kernel upper bounds (discrete form)

Z.-Q. Chen, P. Kim, T. Kumagai and J. Wang, *Heat kernel upper bounds for symmetric Markov
semigroups*, J. Funct. Anal. 281 (2021), no. 4, 109074 (arXiv:2010.05414v1): Theorem 4.4 with
Example 4.3 (the Davies-type off-diagonal bound) and Proposition 3.1(ii) (ultracontractivity
implies a Nash inequality), restricted to symmetric bounded-rate chains on a countable set with
counting measure. The two propositions are stated here so that a formalization citing these
results can carry them as explicit hypotheses; they are not proved. Transition probabilities are
the singleton values of the Poisson-mixture transition kernel of the chain.
-/

namespace LatticeProb.External

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

noncomputable section

/-- Counting-measure squared L² norm, used only for square-summable functions. -/
def ckkwNormSq {S : Type*} (f : S → ℝ) : ℝ := ∑' i, (f i) ^ 2

/-- The bounded symmetric jump form, with the source normalization. -/
def ckkwEnergy {S : Type*} (rates : JumpChain.BoundedRates S) (f : S → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' i, ∑' j, rates.q i j * (f j - f i) ^ 2

/-- The squared Davies functional; extended values prevent divergent suprema becoming zero. -/
def ckkwLambdaSq {S : Type*} (rates : JumpChain.BoundedRates S)
    (ψ : S → ℝ) : ℝ≥0∞ :=
  max (⨆ i, ∑' j, ENNReal.ofReal
    ((1 / 2 : ℝ) * rates.q i j * (Real.exp (ψ j - ψ i) - 1) ^ 2))
    (⨆ i, ∑' j, ENNReal.ofReal
      ((1 / 2 : ℝ) * rates.q i j * (Real.exp (ψ i - ψ j) - 1) ^ 2))

/-- The source infinite product, with natural index zero representing source index one. -/
def ckkwProductBound (φ : ℝ → ℝ) (l c C : ℝ) : Prop :=
  ∀ t > 0, ∃ P : ℝ,
    HasProd (fun n : ℕ ↦ Real.rpow (φ ((l - 1) * l ^ (-(n + 2 : ℤ)) * t))
      ((2 : ℝ) ^ (-(n + 1 : ℤ)))) P ∧ P ≤ C * φ (c * t)

/-- Product witnesses are zero outside their range of validity; positivity records that range. -/
def ckkwProductData (c C : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, 2 < L ∧ ∀ l > L, 0 < c l ∧ 0 < C l

/-- The product inequality at every parameter where its witnesses are positive. -/
def ckkwProductProfile (φ c C : ℝ → ℝ) : Prop :=
  ∀ l > 2, 0 < c l → 0 < C l → ckkwProductBound φ l (c l) (C l)

/-- Definition 1.1, including both endpoint limits and all derivative conditions. -/
def ckkwRegular (φ : ℝ → ℝ) : Prop :=
  (∀ t > 0, 0 < φ t) ∧ StrictAntiOn φ (Set.Ioi 0) ∧
  ContDiffOn ℝ 1 φ (Set.Ioi 0) ∧
  Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) atTop ∧ Tendsto φ atTop (𝓝 0) ∧
  (∃ (c c₀ : ℝ) (N : ℝ → ℝ), 1 ≤ c ∧ 0 < c₀ ∧
    (∀ t > 0, 0 < N t) ∧ AntitoneOn N (Set.Ioi 0) ∧
    (∀ t > 0, c⁻¹ * N t ≤ deriv (fun u ↦ -Real.log (φ u)) t ∧
      deriv (fun u ↦ -Real.log (φ u)) t ≤ c * N t) ∧
    ∀ t > 0, ∀ a ∈ Set.Icc (1 : ℝ) 2,
      deriv (fun u ↦ -Real.log (φ u)) t ≤
        c₀ * deriv (fun u ↦ -Real.log (φ u)) (a * t)) ∧
  ∃ c C : ℝ → ℝ, ckkwProductData c C ∧ ckkwProductProfile φ c C

/-- The tail integral uses a nonnegative integral, so finiteness is separately visible. -/
def ckkwTail (θ : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioi r, ENNReal.ofReal ((θ s)⁻¹)

/-- The inverse in Theorem 4.4 is supplied with both inverse identities, never chosen. -/
def ckkwInverseProfile (θ φ : ℝ → ℝ) : Prop :=
  (∀ r > 0, 0 < θ r ∧ ckkwTail θ r ≠ ∞) ∧
  (∀ t > 0, 0 < φ t ∧ (ckkwTail θ (φ t)).toReal = t) ∧
  ∀ r > 0, φ (ckkwTail θ r).toReal = r

/-- The Nash hypothesis of Theorem 4.4, on the full counting-measure form domain. -/
def ckkwNashInequality {S : Type*} (rates : JumpChain.BoundedRates S)
    (θ : ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ f : S → ℝ, Summable (fun i ↦ (f i) ^ 2) →
    Summable (fun i ↦ |f i|) → (∑' i, |f i|) ≤ 1 →
    0 < ckkwNormSq f → θ (ckkwNormSq f) ≤ ckkwEnergy rates f + δ * ckkwNormSq f

/-- The supremum in Proposition 3.1(ii), in an extended carrier to retain infinity. -/
def ckkwNashProfile (φ : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ t : Set.Ioi (0 : ℝ), ENNReal.ofReal (r / t * Real.log (r / φ t))

/-- The real singleton transition density with respect to counting measure. -/
def ckkwKernel {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (rates : JumpChain.BoundedRates S)
    (t : ℝ≥0) (i j : S) : ℝ := (rates.transitionKernel t i {j}).toReal

/-- Singleton masses of the Poisson kernel are at most one. -/
theorem ckkwKernel_le_one {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (rates : JumpChain.BoundedRates S)
    (t : ℝ≥0) (i j : S) : ckkwKernel rates t i j ≤ 1 := by
  have hmass : rates.transitionKernel t i {j} ≤ 1 := by
    calc
      rates.transitionKernel t i {j} ≤ rates.transitionKernel t i Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  simpa only [ckkwKernel, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top hmass

/-- **CKKW Theorem 4.4 with Example 4.3** (discrete form), at the fixed choice `s = 1/2`.
Constants depend only on comparison and product witnesses and epsilon, before any chain.
The product functions include their validity range through their positivity sets. -/
def ChenKimKumagaiWangDavies : Prop :=
  ∀ (c₁ c₂ : ℝ) (c C : ℝ → ℝ), 1 ≤ c₁ → 1 ≤ c₂ → ckkwProductData c C →
  ∀ ε > 0, ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
  ∀ θ θstar φ : ℝ → ℝ,
    ckkwInverseProfile θ φ → ckkwProductProfile φ c C →
    (∀ r > 0, 0 < θstar r) → MonotoneOn θstar (Set.Ioi 0) →
    MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0) →
    (∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) →
  ∀ (S : Type) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (rates : JumpChain.BoundedRates S),
    (∀ i j, rates.q i j = rates.q j i) →
  ∀ δ : ℝ, 0 ≤ δ → ckkwNashInequality rates θ δ →
  ∀ ψ : S → ℝ, (Function.support ψ).Finite → ckkwLambdaSq rates ψ ≠ ∞ →
  ∀ (t : ℝ≥0), 0 < t → ∀ i j : S,
    ckkwKernel rates t i j ≤ A * φ (a * t) * Real.exp (δ * t) *
      Real.exp (-|ψ j - ψ i| + (1 + ε) * (ckkwLambdaSq rates ψ).toReal * t)

/-- **CKKW Proposition 3.1(ii)** (discrete form), with its literal supremum Nash profile. -/
def ChenKimKumagaiWangNash : Prop :=
  ∀ (S : Type) [Countable S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (rates : JumpChain.BoundedRates S),
    (∀ i j, rates.q i j = rates.q j i) →
  ∀ (δ : ℝ) (φ : ℝ → ℝ), 0 ≤ δ → (∀ t > 0, 0 < φ t) →
    AntitoneOn φ (Set.Ioi 0) →
    (∀ (t : ℝ≥0), 0 < t → ∀ i j : S,
      ckkwKernel rates t i j ≤ φ t * Real.exp (δ * t)) →
  ∀ f : S → ℝ, Summable (fun i ↦ (f i) ^ 2) →
    Summable (fun i ↦ |f i|) → (∑' i, |f i|) ≤ 1 → 0 < ckkwNormSq f →
    ckkwNashProfile φ (ckkwNormSq f) ≤
      ENNReal.ofReal (ckkwEnergy rates f + δ * ckkwNormSq f)

end
end LatticeProb.External

end LongRangeAudit.QuenchedInvariance
