import LongRangeHeat.GaussianTails
import LongRangeHeat.SecondMoment
import LongRangeHeat.Sampling

/-!
# The forcing field of the sampled continuum solution

The sampled solution `ū_s = restrict ε (continuumHeat f s)` is square summable and satisfies the
increment bound (2.6) along the lattice jumps, uniformly in `ε ∈ (0, 1/2)` and `s ≥ 0`
(`exists_sampled_bounds`). Proposition 3.2 and Lemma 3.3 for `ū_s` follow from their versions for
a general square-summable function with an increment bound:

* `forcing_representation_sampled`: the representation of `(L̄ - L^ε) ū_s` by the field `G(s, ·)`
  of (3.3), with an error `C / κ_ε ‖v‖`;
* `forcingField_gaussian_tails_sampled`: the Gaussian tails of `‖G(s, ·)‖`.
-/

namespace LongRangeHeat

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (generator kappa Edge)
open scoped ContDiff

variable {d : ℕ}

theorem multiDeriv_zero (g : (Fin d → ℝ) → ℝ) : multiDeriv (0 : Fin d → ℕ) g = g := by
  unfold multiDeriv
  induction List.finRange d with
  | nil => rfl
  | cons i l _ => simp

/-- The sampled continuum solution `ū_s` is square summable and satisfies the increment bound
(2.6) along the lattice jumps, with a constant `K > 0` depending only on `d` and `f`. -/
theorem exists_sampled_bounds (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ K > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s →
      MemL2 (restrict ε (continuumHeat f s)) ∧
      ∀ w : Site d, latticeNorm ε (fun q => restrict ε (continuumHeat f s) (q + w) -
        restrict ε (continuumHeat f s) q) ≤ K * min (radius (physical ε w)) 1 := by
  obtain ⟨C₀, hC₀⟩ := sampling_bound hd hf hfc 0
  obtain ⟨C₁, hC₁⟩ := increment_bound hd hf hfc
  refine ⟨max C₁ 1, lt_max_of_lt_right one_pos, fun ε hε s hs => ⟨?_, fun w => ?_⟩⟩
  · have h := (hC₀ ε hε s hs 0).1
    simp only [multiDeriv_zero, add_zero, sq_abs] at h
    exact h
  · have h := (hC₁ ε hε s hs (physical ε w)).2
    simp only [restrict, physical_add]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (le_min (radius_nonneg _) zero_le_one))

/-- Proposition 3.2 for `g = ū_s`. -/
theorem forcing_representation_sampled (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ s : ℝ, 0 ≤ s →
      MemL2 (fun q => meanGenerator ε (restrict ε (continuumHeat f s)) q -
        generator ε a (restrict ε (continuumHeat f s)) q) ∧
      (∀ i, MemL2 (forcingField ε a (restrict ε (continuumHeat f s)) i)) ∧
      ∀ v : Site d → ℝ, MemL2 v →
        |latticeInner ε (fun q => meanGenerator ε (restrict ε (continuumHeat f s)) q -
            generator ε a (restrict ε (continuumHeat f s)) q) v -
          (kappa d ε)⁻¹ * ∑ i, latticeInner ε
            (forcingField ε a (restrict ε (continuumHeat f s)) i) (discreteDeriv ε i v)| ≤
          C / kappa d ε * latticeNorm ε v := by
  obtain ⟨C₀, -, h₀⟩ := forcing_representation_of_increment hd hlam
  obtain ⟨K, -, hK⟩ := exists_sampled_bounds hd hf hfc
  refine ⟨C₀ * K, fun ε hε a ha s hs => ?_⟩
  obtain ⟨hg, hinc⟩ := hK ε hε s hs
  exact h₀ ε hε a ha K _ hg hinc

/-- Lemma 3.3 for `g = ū_s`. -/
theorem forcingField_gaussian_tails_sampled (hd : 1 ≤ d) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ),
      ConductanceLaw P lam a → ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ s : ℝ, 0 ≤ s →
      (∀ r i, MemL2 (forcingField ε (a r) (restrict ε (continuumHeat f s)) i)) ∧
      IsOq P 2 (fun r => Real.sqrt (∑ i, latticeNormSq ε
        (forcingField ε (a r) (restrict ε (continuumHeat f s)) i))) C := by
  obtain ⟨C₀, hC₀, h₀⟩ := forcingField_gaussian_tails_of_increment hd hlam
  obtain ⟨K, hKpos, hK⟩ := exists_sampled_bounds hd hf hfc
  refine ⟨C₀ * K, mul_pos hC₀ hKpos, fun Ω _ P a hA ε hε s hs => ?_⟩
  obtain ⟨hg, hinc⟩ := hK ε hε s hs
  exact h₀ Ω P a hA ε hε K hKpos _ hg hinc

end LongRangeHeat
