import LongRangeHeat.FddChain
import LongRangeHeat.Statements.MainTheorem
import LongRangeHeat.Statements.StochasticO

/-!
# The one-step errors in expectation

For `F ∈ C_c^∞(ℝ^d)` and `T ≥ 0`, Theorem 1.1 and Lemma 2.3 (ii) give (4.8): the expectation of
`‖e^{s L^ε} F - P̄_s F‖_{L²(εℤ^d)}` is at most `C (1 + s) |ln ε|^{-1/2}`, uniformly over the
times `s ≤ T`. Here the error at all times `s ≤ T` is dominated by one integrable random variable
(`exists_integral_stepError_le`), and the same holds for the bound `chainDefect` of the backward
recursion (`exists_integral_chainDefect_le`), by induction on the number of observation times.
-/

namespace LongRangeHeat

open MeasureTheory Set Filter
open scoped NNReal ContDiff

noncomputable section

section Expectation

variable {d : ℕ}

/-- The inequality (4.8) of the proof of Proposition 4.3, uniformly over the times `s ≤ T`. -/
theorem exists_integral_stepError_le (hd : 1 ≤ d) {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → LongRange.Edge d → ℝ), ConductanceLaw P lam a →
      ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∃ S : Ω → ℝ, (∀ r, 0 ≤ S r) ∧ Integrable S P ∧
        ∫ r, S r ∂P ≤ K / Real.sqrt |Real.log ε| ∧
        ∀ r, ∀ t : ℝ≥0, t ≤ T → stepError ε (a r) F t ≤ S r ∧
          MemL2 fun q => latticeHeat ε (a r) F (t : ℝ) q - restrict ε (continuumHeat F (t : ℝ)) q := by
  obtain ⟨C, hC, hmain⟩ := Statements.main_theorem hd hF hFc hlam
  refine ⟨2 * (C * (1 + T)), by positivity, fun Ω _ P a hP ε hε => ?_⟩
  have := hP.isProbabilityMeasure
  obtain ⟨hbdd, hOq⟩ := hmain Ω P a hP (T : ℝ) T.2 ε hε
  set S : Ω → ℝ := fun r => sSup ((fun t => latticeNorm ε (fun q => latticeHeat ε (a r) F t q -
    restrict ε (continuumHeat F t) q)) '' Icc 0 (T : ℝ)) with hS
  have hlog : 0 < |Real.log ε| := by
    rw [abs_pos]
    exact (Real.log_neg hε.1 (by linarith [hε.2])).ne
  have hA : 0 < C * (1 + T) / Real.sqrt |Real.log ε| := by positivity
  have hS0 : ∀ r, 0 ≤ S r := fun r =>
    Real.sSup_nonneg (by rintro _ ⟨t, -, rfl⟩; exact latticeNorm_nonneg _ _)
  obtain ⟨hint, hle⟩ := Statements.O_expectation P hA hOq
  have hmax : (fun r => max (S r) 0) = S := funext fun r => max_eq_left (hS0 r)
  rw [hmax] at hint hle
  refine ⟨S, hS0, hint, ?_, fun r t ht => ⟨?_, (hbdd r).2 t ⟨t.2, ht⟩⟩⟩
  · calc ∫ r, S r ∂P ≤ 2 * (C * (1 + T) / Real.sqrt |Real.log ε|) := hle
      _ = _ := by ring
  · exact le_csSup (hbdd r).1 ⟨(t : ℝ), ⟨t.2, ht⟩, rfl⟩

/-- The bound `chainDefect` of the backward recursion has an integrable majorant of order
`|ln ε|^{-1/2}`. -/
theorem exists_integral_chainDefect_le (hd : 1 ≤ d) {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1)
    {M : ℝ} (hM : 0 ≤ M) (T : ℝ≥0) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin (k + 1) → (Fin d → ℝ) → ℝ),
      (∀ i, ContDiff ℝ ∞ (g i)) → (∀ i, HasCompactSupport (g i)) → (∀ i, s i ≤ T) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (a : Ω → LongRange.Edge d → ℝ), ConductanceLaw P lam a →
        ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), ∃ S : Ω → ℝ, (∀ r, 0 ≤ S r) ∧ Integrable S P ∧
          ∫ r, S r ∂P ≤ K / Real.sqrt |Real.log ε| ∧
          ∀ r, ChainSummable ε (a r) k s g ∧ chainDefect ε (a r) M k s g ≤ S r
  | 0, s, g, _, _, _ => by
      refine ⟨0, le_rfl, fun Ω _ P a hP ε hε => ⟨fun _ => 0, fun _ => le_rfl, integrable_zero _ _ _,
        by simp, fun r => ⟨trivial, le_rfl⟩⟩⟩
  | k + 1, s, g, hg, hgc, hs => by
      obtain ⟨K₁, hK₁, h₁⟩ := exists_integral_chainDefect_le hd hlam hM T k (Fin.tail s)
        (Fin.tail g) (fun i => hg i.succ) (fun i => hgc i.succ) (fun i => hs i.succ)
      obtain ⟨hFs, hFc⟩ := continuumChain_testFunction hd k (Fin.tail s) (Fin.tail g)
        (fun i => hg i.succ) (fun i => hgc i.succ)
      obtain ⟨K₂, hK₂, h₂⟩ := exists_integral_stepError_le hd hFs hFc hlam T
      refine ⟨M * (K₁ + K₂), by positivity, fun Ω _ P a hP ε hε => ?_⟩
      obtain ⟨S₁, hS₁0, hS₁i, hS₁, hS₁c⟩ := h₁ Ω P a hP ε hε
      obtain ⟨S₂, hS₂0, hS₂i, hS₂, hS₂c⟩ := h₂ Ω P a hP ε hε
      refine ⟨fun r => M * (S₁ r + S₂ r), fun r => by have := hS₁0 r; have := hS₂0 r; positivity,
        (hS₁i.add hS₂i).const_mul M, ?_, fun r => ⟨⟨(hS₂c r (s 0) (hs 0)).2, (hS₁c r).1⟩, ?_⟩⟩
      · rw [integral_const_mul, integral_add hS₁i hS₂i]
        calc M * (∫ r, S₁ r ∂P + ∫ r, S₂ r ∂P) ≤ M * (K₁ / Real.sqrt |Real.log ε| +
            K₂ / Real.sqrt |Real.log ε|) := mul_le_mul_of_nonneg_left (add_le_add hS₁ hS₂) hM
          _ = _ := by ring
      · exact mul_le_mul_of_nonneg_left (add_le_add (hS₁c r).2 (hS₂c r (s 0) (hs 0)).1) hM

end Expectation

end

end LongRangeHeat
