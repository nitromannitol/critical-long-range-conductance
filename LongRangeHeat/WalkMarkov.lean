import LongRangeHeat.WalkSemigroup

/-!
# Iterated expectations along a Markov chain

For the transition kernels of a bounded-rate walk, the chain mass of a path `y : Fin k → S`
started at `z` with time increments `s : Fin k → ℝ≥0` is the product of the one-step
transition probabilities. Sums of bounded products `∏ g_i (y_i)` against the chain mass
are evaluated by the backward recursion
`F_k = g_k`, `F_i = g_i · e^{(s_{i+1}) L} F_{i+1}`, which is the Markov property for products.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
open scoped NNReal ENNReal

noncomputable section

section Chain

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The mass of the path `y = (y_1, …, y_k)` for the chain started at `z` and observed after the
time increments `s_1, …, s_k`: the product of the one-step transition probabilities. -/
def chainMass (rates : BoundedRates S) : (k : ℕ) → (Fin k → ℝ≥0) → S → (Fin k → S) → ℝ
  | 0, _, _, _ => 1
  | k + 1, s, z, y =>
      (rates.transitionKernel (s 0) z).real {y 0} * chainMass rates k (Fin.tail s) (y 0) (Fin.tail y)

/-- The backward recursion `F_k = g_k`, `F_i = g_i · e^{s_{i+1} L} F_{i+1}` evaluated at the
starting point, with the convention that the empty product is `1`. -/
def chainExp (rates : BoundedRates S) : (k : ℕ) → (Fin k → ℝ≥0) → (Fin k → S → ℝ) → S → ℝ
  | 0, _, _, _ => 1
  | k + 1, s, g, z =>
      walkOp rates (s 0) (fun y => g 0 y * chainExp rates k (Fin.tail s) (Fin.tail g) y) z

/-- Splitting off the first coordinate of a path. -/
def consEquiv (k : ℕ) (S : Type*) : S × (Fin k → S) ≃ (Fin (k + 1) → S) where
  toFun p := Fin.cons p.1 p.2
  invFun y := (y 0, Fin.tail y)
  left_inv p := by simp
  right_inv y := by simp

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
@[simp] theorem consEquiv_apply (k : ℕ) (p : S × (Fin k → S)) :
    consEquiv k S p = Fin.cons p.1 p.2 := rfl

theorem chainMass_nonneg (rates : BoundedRates S) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (z : S) (y : Fin k → S), 0 ≤ chainMass rates k s z y
  | 0, _, _, _ => zero_le_one
  | k + 1, s, _, y =>
      mul_nonneg measureReal_nonneg (chainMass_nonneg rates k (Fin.tail s) (y 0) (Fin.tail y))

theorem chainMass_cons (rates : BoundedRates S) (k : ℕ) (s : Fin (k + 1) → ℝ≥0) (z y₀ : S)
    (y : Fin k → S) :
    chainMass rates (k + 1) s z (Fin.cons y₀ y) =
      (rates.transitionKernel (s 0) z).real {y₀} * chainMass rates k (Fin.tail s) y₀ y := by
  simp [chainMass]

/-- The chain masses of all paths sum to one. -/
theorem hasSum_chainMass (rates : BoundedRates S) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (z : S), HasSum (chainMass rates k s z) 1
  | 0, s, z => by
      have := hasSum_single (f := chainMass rates 0 s z) (default : Fin 0 → S)
        (fun b hb => absurd (Subsingleton.elim b _) hb)
      simp only [chainMass] at this
      exact this
  | k + 1, s, z => by
      have hIH := hasSum_chainMass rates k (Fin.tail s)
      obtain ⟨f, hf⟩ : ∃ f : S × (Fin k → S) → ℝ, ∀ p, f p =
          (rates.transitionKernel (s 0) z).real {p.1} *
            chainMass rates k (Fin.tail s) p.1 p.2 := ⟨_, fun _ => rfl⟩
      have hnn : ∀ p, 0 ≤ f p := fun p => by
        rw [hf]
        exact mul_nonneg measureReal_nonneg (chainMass_nonneg rates k _ _ _)
      have hfib : ∀ x : S, HasSum (fun c => f (x, c))
          ((rates.transitionKernel (s 0) z).real {x}) := fun x => by
        have := (hIH x).mul_left ((rates.transitionKernel (s 0) z).real {x})
        simpa only [hf, mul_one] using this
      have hsum : Summable f := by
        refine (summable_prod_of_nonneg hnn).mpr ⟨fun x => (hfib x).summable, ?_⟩
        simp only [fun x => (hfib x).tsum_eq]
        exact (hasSum_measureReal_singleton _).summable
      have htsum : ∑' p, f p = 1 := by
        rw [hsum.tsum_prod' (fun x => (hfib x).summable)]
        simp only [fun x => (hfib x).tsum_eq]
        exact (hasSum_measureReal_singleton _).tsum_eq
      have h1 : HasSum f 1 := htsum ▸ hsum.hasSum
      refine (Equiv.hasSum_iff (consEquiv k S)).mp ?_
      convert h1 using 1
      funext p
      rw [Function.comp_apply, consEquiv_apply, chainMass_cons, hf]

/-- The backward recursion is bounded by the product of the bounds. -/
theorem abs_chainExp_le (rates : BoundedRates S) {M : ℝ} (hM0 : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin k → S → ℝ), (∀ i y, |g i y| ≤ M) → ∀ z : S,
      |chainExp rates k s g z| ≤ M ^ k
  | 0, s, g, _, z => by simp [chainExp]
  | k + 1, s, g, hg, z => by
      have hIH := abs_chainExp_le rates hM0 k (Fin.tail s) (Fin.tail g) (fun i => hg i.succ)
      refine abs_integral_le _ _ fun y => ?_
      rw [abs_mul, pow_succ']
      exact mul_le_mul (hg 0 y) (hIH y) (abs_nonneg _) hM0

/-- The Markov property for products: the chain-mass-weighted sum of a bounded product is the
backward recursion `e^{s_1 L}(g_1 e^{s_2 L}(g_2 ⋯))(z)`. -/
theorem hasSum_chainMass_mul_prod (rates : BoundedRates S) {M : ℝ} (hM0 : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin k → S → ℝ), (∀ i y, |g i y| ≤ M) → ∀ z : S,
      HasSum (fun y : Fin k → S => chainMass rates k s z y * ∏ i, g i (y i))
        (chainExp rates k s g z)
  | 0, s, g, _, z => by
      have := hasSum_single (f := fun y : Fin 0 → S => chainMass rates 0 s z y * ∏ i, g i (y i))
        (default : Fin 0 → S) (fun b hb => absurd (Subsingleton.elim b _) hb)
      simpa only [chainMass, chainExp, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
        using this
  | k + 1, s, g, hg, z => by
      have hIH := hasSum_chainMass_mul_prod rates hM0 k (Fin.tail s) (Fin.tail g)
        (fun i => hg i.succ)
      have hbd : ∀ y : Fin (k + 1) → S, ‖chainMass rates (k + 1) s z y * ∏ i, g i (y i)‖ ≤
          M ^ (k + 1) * chainMass rates (k + 1) s z y := fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chainMass_nonneg rates _ _ _ _), mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (chainMass_nonneg rates _ _ _ _)
        calc |∏ i, g i (y i)| = ∏ i, |g i (y i)| := Finset.abs_prod _ _
          _ ≤ ∏ _i : Fin (k + 1), M :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hg i (y i)
          _ = M ^ (k + 1) := by simp
      have hsum : Summable (fun y : Fin (k + 1) → S =>
          chainMass rates (k + 1) s z y * ∏ i, g i (y i)) :=
        Summable.of_norm_bounded ((hasSum_chainMass rates (k + 1) s z).summable.mul_left _) hbd
      have hsume := (Equiv.summable_iff (consEquiv k S)).mpr hsum
      have hfib : ∀ x : S, HasSum (fun c : Fin k → S =>
          chainMass rates (k + 1) s z (consEquiv k S (x, c)) *
            ∏ i, g i (consEquiv k S (x, c) i))
          ((rates.transitionKernel (s 0) z).real {x} * g 0 x *
            chainExp rates k (Fin.tail s) (Fin.tail g) x) := fun x => by
        have := (hIH x).mul_left ((rates.transitionKernel (s 0) z).real {x} * g 0 x)
        convert this using 2 with c
        simp only [consEquiv_apply, chainMass_cons, Fin.prod_univ_succ, Fin.cons_zero,
          Fin.cons_succ]
        simp only [Fin.tail]
        ring
      have hval : ∑' x : S, (rates.transitionKernel (s 0) z).real {x} * g 0 x *
          chainExp rates k (Fin.tail s) (Fin.tail g) x =
          chainExp rates (k + 1) s g z := by
        have hb : ∀ y, |g 0 y * chainExp rates k (Fin.tail s) (Fin.tail g) y| ≤ M * M ^ k :=
          fun y => by
            rw [abs_mul]
            exact mul_le_mul (hg 0 y) (abs_chainExp_le rates hM0 k (Fin.tail s) (Fin.tail g)
              (fun i => hg i.succ) y) (abs_nonneg _) hM0
        change ∑' x, _ = ∫ y, g 0 y * chainExp rates k (Fin.tail s) (Fin.tail g) y
          ∂rates.transitionKernel (s 0) z
        rw [integral_eq_tsum_real_singleton _ hb]
        exact tsum_congr fun x => by ring
      have hfib' : ∀ x : S, ∑' c : Fin k → S,
          ((fun y : Fin (k + 1) → S => chainMass rates (k + 1) s z y * ∏ i, g i (y i)) ∘
            consEquiv k S) (x, c) =
          (rates.transitionKernel (s 0) z).real {x} * g 0 x *
            chainExp rates k (Fin.tail s) (Fin.tail g) x := fun x => (hfib x).tsum_eq
      have htot : ∑' p : S × (Fin k → S),
          ((fun y : Fin (k + 1) → S => chainMass rates (k + 1) s z y * ∏ i, g i (y i)) ∘
            consEquiv k S) p = chainExp rates (k + 1) s g z := by
        rw [hsume.tsum_prod' (fun x => hsume.prod_factor x)]
        simp only [hfib']
        exact hval
      refine (Equiv.hasSum_iff (consEquiv k S)).mp ?_
      rw [← htot]
      exact hsume.hasSum

end Chain

end

end LongRangeHeat
