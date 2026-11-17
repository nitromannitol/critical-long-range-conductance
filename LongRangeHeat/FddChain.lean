import LongRangeHeat.FddStep
import LongRangeHeat.WalkMarkov
import LongRangeHeat.Forcing

/-!
# The backward recursion for the finite-dimensional marginals

For observables `g_1, …, g_{k+1} ∈ C_c^∞(ℝ^d)` and time increments `s_1, …, s_k`, the functions
`F^ε_j = g_j e^{s_j L^ε} F^ε_{j+1}` on `εℤ^d` and `F̄_j = g_j P̄_{s_j} F̄_{j+1}` on `ℝ^d` of the proof
of Proposition 4.3 are `latticeChain` and `continuumChain`. The `ℓ²(εℤ^d)` distance between
`F^ε_j` and the restriction of `F̄_j` is bounded by `chainDefect`, the weighted sum of the one-step
errors `‖e^{s L^ε} F - P̄_s F‖` of Theorem 1.1, because `e^{sL^ε}` contracts `ℓ²(εℤ^d)`
(`chain_sub_le`).
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
  LatticeProb.Euclidean.Lattice LatticeProb.Heat LatticeProb.WhiteNoise Set
open scoped NNReal ENNReal ContDiff

noncomputable section

section Norm

variable {d : ℕ}

theorem latticeNorm_nonneg (ε : ℝ) (v : Site d → ℝ) : 0 ≤ latticeNorm ε v :=
  Real.sqrt_nonneg _

theorem latticeNorm_sq {ε : ℝ} (hε : 0 ≤ ε) (v : Site d → ℝ) :
    latticeNorm ε v ^ 2 = ε ^ d * ∑' q, v q ^ 2 :=
  Real.sq_sqrt (mul_nonneg (pow_nonneg hε d) (tsum_nonneg fun _ => sq_nonneg _))

/-- The triangle inequality for `‖·‖_{L²(εℤ^d)}`. -/
theorem latticeNorm_add_le {ε : ℝ} (hε : 0 ≤ ε) {f g : Site d → ℝ} (hf : MemL2 f)
    (hg : MemL2 g) : latticeNorm ε (fun q => f q + g q) ≤ latticeNorm ε f + latticeNorm ε g := by
  have he : 0 ≤ ε ^ d := pow_nonneg hε d
  have hfg : Summable fun q => f q * g q := summable_mul_of_memL2 hf hg
  have hfg' : Summable fun q => |f q| * |g q| := by simpa [abs_mul] using hfg.abs
  have h1 : ∑' q, f q * g q ≤ ∑' q, |f q| * |g q| :=
    hfg.tsum_le_tsum (fun q => (le_abs_self _).trans (abs_mul _ _).le) hfg'
  have hsq : ∑' q, (f q + g q) ^ 2 = ∑' q, f q ^ 2 + 2 * ∑' q, f q * g q + ∑' q, g q ^ 2 := by
    have : (fun q => (f q + g q) ^ 2) = fun q => (f q ^ 2 + 2 * (f q * g q)) + g q ^ 2 := by
      funext q
      ring
    rw [this, (hf.add (hfg.mul_left 2)).tsum_add hg, hf.tsum_add (hfg.mul_left 2), tsum_mul_left]
  have hCS := pow_mul_tsum_abs_mul_le hε hf hg
  have hA := latticeNorm_sq hε f
  have hB := latticeNorm_sq hε g
  have h2 : ε ^ d * ∑' q, f q * g q ≤ ε ^ d * ∑' q, |f q| * |g q| :=
    mul_le_mul_of_nonneg_left h1 he
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg (latticeNorm_nonneg _ _) (latticeNorm_nonneg _ _), ?_⟩
  rw [latticeNormSq, hsq]
  nlinarith

/-- A bounded multiplier `b` with `|b| ≤ M` multiplies the norm by at most `M`. -/
theorem latticeNorm_mul_le {ε : ℝ} (hε : 0 ≤ ε) {b f : Site d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ q, |b q| ≤ M) (hf : MemL2 f) :
    latticeNorm ε (fun q => b q * f q) ≤ M * latticeNorm ε f := by
  have he : 0 ≤ ε ^ d := pow_nonneg hε d
  have hbf := memL2_mul_of_abs_le hb hf
  have hle : ∑' q, (b q * f q) ^ 2 ≤ M ^ 2 * ∑' q, f q ^ 2 := by
    rw [← tsum_mul_left]
    refine hbf.tsum_le_tsum (fun q => ?_) (hf.mul_left _)
    rw [mul_pow]
    have : b q ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb q) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  calc latticeNorm ε (fun q => b q * f q)
      ≤ Real.sqrt (M ^ 2 * (ε ^ d * ∑' q, f q ^ 2)) := by
        apply Real.sqrt_le_sqrt
        change ε ^ d * ∑' q, (b q * f q) ^ 2 ≤ _
        nlinarith [mul_le_mul_of_nonneg_left hle he]
    _ = M * latticeNorm ε f := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
        rfl

/-- The semigroup of the walk contracts `L²(εℤ^d)`. -/
theorem memL2_walkOp_and_latticeNorm_le (rates : BoundedRates (Site d))
    (hs : ∀ i j, rates.q i j = rates.q j i) (t : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) {v : Site d → ℝ}
    (hv : MemL2 v) :
    MemL2 (walkOp rates t v) ∧ latticeNorm ε (walkOp rates t v) ≤ latticeNorm ε v := by
  obtain ⟨h1, h2⟩ := summable_sq_walkOp_and_tsum_sq_walkOp_le rates hs t hv
  refine ⟨h1, Real.sqrt_le_sqrt ?_⟩
  exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hε d)

end Norm

section Lattice

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- The functions `F^ε_j = g_j e^{s_j L^ε} F^ε_{j+1}`, `F^ε_{k+1} = g_{k+1}`, of the proof of
Proposition 4.3, for the increments `s_1, …, s_k` and the observables `g_1, …, g_{k+1}`. -/
def latticeChain (rates : BoundedRates S) :
    (k : ℕ) → (Fin k → ℝ≥0) → (Fin (k + 1) → S → ℝ) → S → ℝ
  | 0, _, g => g 0
  | k + 1, s, g => fun y =>
      g 0 y * walkOp rates (s 0) (latticeChain rates k (Fin.tail s) (Fin.tail g)) y

/-- The Markov property for the product of `k + 1` observations, when the first observation time
is `s_0`: `E_z[∏ g_i(X_{t_i})] = e^{s_0 L} F_1(z)`. -/
theorem chainExp_succ_eq (rates : BoundedRates S) :
    ∀ (k : ℕ) (s : Fin (k + 1) → ℝ≥0) (g : Fin (k + 1) → S → ℝ) (z : S),
      chainExp rates (k + 1) s g z = walkOp rates (s 0) (latticeChain rates k (Fin.tail s) g) z
  | 0, s, g, z => by simp [chainExp, latticeChain]
  | k + 1, s, g, z => by
      rw [chainExp]
      congr 1
      funext y
      rw [chainExp_succ_eq rates k (Fin.tail s) (Fin.tail g) y]
      rfl

theorem abs_latticeChain_le (rates : BoundedRates S) {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin (k + 1) → S → ℝ), (∀ i y, |g i y| ≤ M) →
      ∀ y, |latticeChain rates k s g y| ≤ M ^ (k + 1)
  | 0, s, g, hg, y => by simpa [latticeChain] using hg 0 y
  | k + 1, s, g, hg, y => by
      have ih := abs_latticeChain_le rates hM k (Fin.tail s) (Fin.tail g) (fun i => hg i.succ)
      have := abs_walkOp_le rates (s 0) ih y
      change |g 0 y * walkOp rates (s 0) (latticeChain rates k (Fin.tail s) (Fin.tail g)) y| ≤ _
      rw [abs_mul, pow_succ' M (k + 1)]
      exact mul_le_mul (hg 0 y) this (abs_nonneg _) hM

end Lattice

section Continuum

variable {d : ℕ}

/-- The functions `F̄_j = g_j P̄_{s_j} F̄_{j+1}`, `F̄_{k+1} = g_{k+1}`, of the proof of
Proposition 4.3. -/
def continuumChain {d : ℕ} :
    (k : ℕ) → (Fin k → ℝ≥0) → (Fin (k + 1) → (Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | 0, _, g => g 0
  | k + 1, s, g => fun y =>
      g 0 y * continuumHeat (continuumChain k (Fin.tail s) (Fin.tail g)) ((s 0 : ℝ≥0) : ℝ) y

theorem continuumChain_testFunction (hd : 1 ≤ d) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin (k + 1) → (Fin d → ℝ) → ℝ),
      (∀ i, ContDiff ℝ ∞ (g i)) → (∀ i, HasCompactSupport (g i)) →
        ContDiff ℝ ∞ (continuumChain k s g) ∧ HasCompactSupport (continuumChain k s g)
  | 0, s, g, hg, hgc => ⟨hg 0, hgc 0⟩
  | k + 1, s, g, hg, hgc => by
      obtain ⟨h1, h2⟩ := continuumChain_testFunction hd k (Fin.tail s) (Fin.tail g)
        (fun i => hg i.succ) (fun i => hgc i.succ)
      exact ⟨(hg 0).mul (contDiff_continuumHeat hd h1 h2 (s 0).2), (hgc 0).mul_right⟩

theorem abs_continuumChain_le (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin (k + 1) → (Fin d → ℝ) → ℝ),
      (∀ i, ContDiff ℝ ∞ (g i)) → (∀ i, HasCompactSupport (g i)) → (∀ i x, |g i x| ≤ M) →
        ∀ y, |continuumChain k s g y| ≤ M ^ (k + 1)
  | 0, s, g, _, _, hg, y => by simpa [continuumChain] using hg 0 y
  | k + 1, s, g, hg, hgc, hgM, y => by
      have ih := abs_continuumChain_le hd hM k (Fin.tail s) (Fin.tail g) (fun i => hg i.succ)
        (fun i => hgc i.succ) (fun i => hgM i.succ)
      have hc := (continuumChain_testFunction hd k (Fin.tail s) (Fin.tail g)
        (fun i => hg i.succ) (fun i => hgc i.succ)).1.continuous
      have := abs_continuumHeat_le hd hc ih (s 0).2 y
      change |g 0 y * continuumHeat (continuumChain k (Fin.tail s) (Fin.tail g))
        ((s 0 : ℝ≥0) : ℝ) y| ≤ _
      rw [abs_mul, pow_succ' M (k + 1)]
      exact mul_le_mul (hgM 0 y) this (abs_nonneg _) hM

/-- A function in `C_c^∞(ℝ^d)` is bounded, as are its gradient and the operator `(2d)⁻¹ Δ`
applied to it. -/
theorem exists_bounds_of_testFunction {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) :
    ∃ M L M₂ : ℝ, (∀ y, |F y| ≤ M) ∧ (∀ y, ‖fderiv ℝ F y‖ ≤ L) ∧ (∀ y, |contOp d F y| ≤ M₂) := by
  obtain ⟨M, hM⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨L, hL⟩ := (hF.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨M₂, hM₂⟩ := (contDiff_contOp hF).continuous.bounded_above_of_compact_support
    (hasCompactSupport_contOp hF hFc)
  exact ⟨M, L, M₂, fun y => by simpa using hM y, hL, fun y => by simpa using hM₂ y⟩

end Continuum

section Comparison

variable {d : ℕ} {ε lam : ℝ} {a : LongRange.Edge d → ℝ}

/-- The one-step error `‖e^{tL^ε} F - P̄_t F‖_{L²(εℤ^d)}` of Theorem 1.1. -/
def stepError (ε : ℝ) (a : LongRange.Edge d → ℝ) (F : (Fin d → ℝ) → ℝ) (t : ℝ≥0) : ℝ :=
  latticeNorm ε fun q => latticeHeat ε a F (t : ℝ) q - restrict ε (continuumHeat F (t : ℝ)) q

/-- The bound for `‖F^ε_1 - F̄_1‖_{L²(εℤ^d)}`: the sum of the one-step errors along the chain,
weighted by the powers of the bound `M` of the observables. -/
def chainDefect (ε : ℝ) (a : LongRange.Edge d → ℝ) (M : ℝ) :
    (k : ℕ) → (Fin k → ℝ≥0) → (Fin (k + 1) → (Fin d → ℝ) → ℝ) → ℝ
  | 0, _, _ => 0
  | k + 1, s, g =>
      M * (chainDefect ε a M k (Fin.tail s) (Fin.tail g) +
        stepError ε a (continuumChain k (Fin.tail s) (Fin.tail g)) (s 0))

/-- The one-step errors along the chain are square summable. -/
def ChainSummable (ε : ℝ) (a : LongRange.Edge d → ℝ) :
    (k : ℕ) → (Fin k → ℝ≥0) → (Fin (k + 1) → (Fin d → ℝ) → ℝ) → Prop
  | 0, _, _ => True
  | k + 1, s, g =>
      (MemL2 fun q => latticeHeat ε a (continuumChain k (Fin.tail s) (Fin.tail g)) ((s 0 : ℝ≥0) : ℝ) q -
        restrict ε (continuumHeat (continuumChain k (Fin.tail s) (Fin.tail g)) ((s 0 : ℝ≥0) : ℝ)) q) ∧
      ChainSummable ε a k (Fin.tail s) (Fin.tail g)

theorem chainDefect_nonneg {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin (k + 1) → (Fin d → ℝ) → ℝ),
      0 ≤ chainDefect ε a M k s g
  | 0, _, _ => le_rfl
  | k + 1, _, _ =>
      mul_nonneg hM (add_nonneg (chainDefect_nonneg hM k _ _) (latticeNorm_nonneg _ _))

/-- Backward induction of the proof of Proposition 4.3: for every realization of the
conductances, `F^ε_1 - F̄_1` is square summable on `εℤ^d` with norm at most `chainDefect`, since
`e^{sL^ε}` contracts `L²(εℤ^d)` and the observables are bounded by `M`. -/
theorem chain_sub_le (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin (k + 1) → (Fin d → ℝ) → ℝ),
      (∀ i, ContDiff ℝ ∞ (g i)) → (∀ i, HasCompactSupport (g i)) → (∀ i x, |g i x| ≤ M) →
      ChainSummable ε a k s g →
      MemL2 (fun q => latticeChain (LongRange.walkRates hd hε hlam a ha) k s
          (fun i => restrict ε (g i)) q - restrict ε (continuumChain k s g) q) ∧
        latticeNorm ε (fun q => latticeChain (LongRange.walkRates hd hε hlam a ha) k s
          (fun i => restrict ε (g i)) q - restrict ε (continuumChain k s g) q) ≤
          chainDefect ε a M k s g
  | 0, s, g, _, _, _, _ => by
      simp only [latticeChain, continuumChain, sub_self, chainDefect]
      refine ⟨by simp [MemL2], ?_⟩
      simp [latticeNorm, latticeNormSq]
  | k + 1, s, g, hg, hgc, hgM, hsum => by
      set rates := LongRange.walkRates hd hε hlam a ha with hrates
      have hsym := walkRates_q_symm hd hε hlam ha
      set τ : ℝ≥0 := s 0 with hτ
      set G := continuumChain k (Fin.tail s) (Fin.tail g) with hG
      set U := latticeChain rates k (Fin.tail s) (fun i => restrict ε (Fin.tail g i)) with hU
      obtain ⟨hD2, hDn⟩ := chain_sub_le hd hε hlam ha hM k (Fin.tail s) (Fin.tail g)
        (fun i => hg i.succ) (fun i => hgc i.succ) (fun i => hgM i.succ) hsum.2
      obtain ⟨hGs, hGc⟩ := continuumChain_testFunction hd k (Fin.tail s) (Fin.tail g)
        (fun i => hg i.succ) (fun i => hgc i.succ)
      have hGb : ∀ y, |G y| ≤ M ^ (k + 1) := abs_continuumChain_le hd hM k (Fin.tail s)
        (Fin.tail g) (fun i => hg i.succ) (fun i => hgc i.succ) (fun i => hgM i.succ)
      have hGq : ∀ q : Site d, |restrict ε G q| ≤ M ^ (k + 1) := fun q => hGb _
      have hUb : ∀ q, |U q| ≤ M ^ (k + 1) :=
        abs_latticeChain_le rates hM k (Fin.tail s) _ (fun i y => hgM i.succ _)
      have hheat : ∀ q, latticeHeat ε a G (τ : ℝ) q = walkOp rates τ (restrict ε G) q :=
        fun q => latticeHeat_eq_integral hd hε hlam ha hGq τ q
      have hid : ∀ q, latticeChain rates (k + 1) s (fun i => restrict ε (g i)) q -
          restrict ε (continuumChain (k + 1) s g) q =
          restrict ε (g 0) q * (walkOp rates τ (fun q => U q - restrict ε G q) q +
            (latticeHeat ε a G (τ : ℝ) q - restrict ε (continuumHeat G (τ : ℝ)) q)) := by
        intro q
        rw [walkOp_sub rates τ hUb hGq, hheat]
        change restrict ε (g 0) q * walkOp rates τ U q -
          restrict ε (g 0) q * continuumHeat G (τ : ℝ) (physical ε q) = _
        simp only [restrict]
        ring
      obtain ⟨hW2, hWn⟩ := memL2_walkOp_and_latticeNorm_le rates hsym τ hε.le hD2
      have hE2 := hsum.1
      have hin := memL2_add hW2 hE2
      have hgb : ∀ q, |restrict ε (g 0) q| ≤ M := fun q => hgM 0 _
      have hfun : (fun q => latticeChain rates (k + 1) s (fun i => restrict ε (g i)) q -
          restrict ε (continuumChain (k + 1) s g) q) = fun q => restrict ε (g 0) q *
          (walkOp rates τ (fun q => U q - restrict ε G q) q +
            (latticeHeat ε a G (τ : ℝ) q - restrict ε (continuumHeat G (τ : ℝ)) q)) :=
        funext hid
      rw [hfun]
      refine ⟨memL2_mul_of_abs_le hgb hin, ?_⟩
      refine (latticeNorm_mul_le hε.le hM hgb hin).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hM
      refine (latticeNorm_add_le hε.le hW2 hE2).trans ?_
      change _ ≤ chainDefect ε a M k (Fin.tail s) (Fin.tail g) + stepError ε a G τ
      exact add_le_add (hWn.trans hDn) le_rfl

/-- **Step 2 for one realization** of the conductances: if the first observation takes place at a
time `τ > h`, the expectation `e^{τ L^ε} F^ε_1 (0)` of the product of the observations differs
from `P̄_τ F̄_1(0)` by at most
`√(C (2h)^{-d/2}) (‖F^ε_1 - F̄_1‖ + ‖e^{(τ-h)L^ε} F̄_1 - P̄_{τ-h} F̄_1‖) + (L + 4 M C) h^{1/3} + M₂ h`,
with the bound `chainDefect` for the first norm. -/
theorem abs_walkOp_chain_sub_le (hd : 1 ≤ d) (hε : 0 < ε) (hlam : 0 < lam)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {C : ℝ} (hC : 0 ≤ C)
    (hdiag : OnDiagonalBound hd hε hlam ha C) (hdisp : DisplacementBound hd hε hlam ha C)
    {M : ℝ} (hM : 0 ≤ M) {k : ℕ} {s : Fin k → ℝ≥0} {g : Fin (k + 1) → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hgc : ∀ i, HasCompactSupport (g i))
    (hgM : ∀ i x, |g i x| ≤ M) (hsum : ChainSummable ε a k s g)
    {M' L M₂ : ℝ} (hM' : ∀ y, |continuumChain k s g y| ≤ M')
    (hL : ∀ y, ‖fderiv ℝ (continuumChain k s g) y‖ ≤ L)
    (hM₂ : ∀ y, |contOp d (continuumChain k s g) y| ≤ M₂)
    {τ h : ℝ≥0} (hh : 0 < h) (hh1 : h ≤ 1) (hhτ : h < τ) (hεh : ε ≤ h + h)
    (hεR : ε ≤ (h : ℝ) ^ ((1 : ℝ) / 3))
    (hmem : MemL2 fun q => latticeHeat ε a (continuumChain k s g) ((τ - h : ℝ≥0) : ℝ) q -
      restrict ε (continuumHeat (continuumChain k s g) ((τ - h : ℝ≥0) : ℝ)) q) :
    |walkOp (LongRange.walkRates hd hε hlam a ha) τ
        (latticeChain (LongRange.walkRates hd hε hlam a ha) k s (fun i => restrict ε (g i))) 0 -
        continuumHeat (continuumChain k s g) (τ : ℝ) 0| ≤
      Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) *
        (chainDefect ε a M k s g + stepError ε a (continuumChain k s g) (τ - h)) +
      (L + 4 * M' * C) * (h : ℝ) ^ ((1 : ℝ) / 3) + M₂ * h := by
  set rates := LongRange.walkRates hd hε hlam a ha with hrates
  set F := continuumChain k s g with hF
  set U := latticeChain rates k s (fun i => restrict ε (g i)) with hU
  obtain ⟨hFs, hFc⟩ := continuumChain_testFunction hd k s g hg hgc
  obtain ⟨hD2, hDn⟩ := chain_sub_le hd hε hlam ha hM k s g hg hgc hgM hsum
  have hUb : ∀ q, |U q| ≤ M ^ (k + 1) :=
    abs_latticeChain_le rates hM k s _ (fun i y => hgM i _)
  have hFq : ∀ q : Site d, |restrict ε F q| ≤ M' := fun q => hM' _
  have hUb' : ∀ q, |U q| ≤ max (M ^ (k + 1)) M' := fun q => (hUb q).trans (le_max_left _ _)
  have hFb' : ∀ q : Site d, |restrict ε F q| ≤ max (M ^ (k + 1)) M' := fun q =>
    (hFq q).trans (le_max_right _ _)
  have h1 := abs_walkOp_sub_le_of_onDiagonal hd hε hlam ha hC hdiag hhτ.le hεh hD2
  rw [walkOp_sub rates τ hUb' hFb'] at h1
  have h2 := abs_latticeHeat_sub_continuumHeat_le hd hε hlam ha hC hdiag hdisp hFs hFc hM' hL hM₂
    hh hh1 hhτ hεh hεR hmem
  have hheat : latticeHeat ε a F (τ : ℝ) 0 = walkOp rates τ (restrict ε F) 0 :=
    latticeHeat_eq_integral hd hε hlam ha hFq τ 0
  rw [hheat] at h2
  have hK : 0 ≤ Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) := Real.sqrt_nonneg _
  have h3 : Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) * latticeNorm ε
      (fun q => U q - restrict ε F q) ≤
      Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) * chainDefect ε a M k s g :=
    mul_le_mul_of_nonneg_left hDn hK
  calc _ = |(walkOp rates τ U 0 - walkOp rates τ (restrict ε F) 0) +
        (walkOp rates τ (restrict ε F) 0 - continuumHeat F (τ : ℝ) 0)| := by ring_nf
    _ ≤ |walkOp rates τ U 0 - walkOp rates τ (restrict ε F) 0| +
        |walkOp rates τ (restrict ε F) 0 - continuumHeat F (τ : ℝ) 0| := abs_add_le _ _
    _ ≤ _ := by
        have : stepError ε a F (τ - h) = latticeNorm ε (fun q =>
          latticeHeat ε a F ((τ - h : ℝ≥0) : ℝ) q -
            restrict ε (continuumHeat F ((τ - h : ℝ≥0) : ℝ)) q) := rfl
        rw [this, mul_add]
        linarith

end Comparison

end

end LongRangeHeat
