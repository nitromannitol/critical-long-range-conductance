import LongRange.Dirichlet.NearestNeighbour
import LongRange.Dirichlet.Coefficients
import LatticeProb.Prob.StochasticO

/-!
# Random flux defects

The deterministic coefficient series splits the flux defect into short and long
physical displacements. Coordinatewise measurable conductances give measurable defects.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Nonnegative scalar multiplication preserves the stochastic bound and scales its size. -/
theorem osBound_const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {s θ c : ℝ} {X : Ω → ℝ} (hX : OsBound P s θ X) (hc : 0 ≤ c) :
    OsBound P s (c * θ) (fun ω => c * X ω) := by
  by_cases hzero : c = 0
  · subst c
    intro t ht
    simp only [zero_mul, mul_zero, max_self, lt_self_iff_false, Set.setOf_false,
      measure_empty]
    exact bot_le
  · have hpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hzero)
    intro t ht
    have hevent : {ω | t * (c * θ) < max (c * X ω) 0} =
        {ω | t * θ < max (X ω) 0} := by
      ext ω
      change t * (c * θ) < max (c * X ω) 0 ↔ t * θ < max (X ω) 0
      rw [show t * (c * θ) = c * (t * θ) by ring,
        show max (c * X ω) 0 = c * max (X ω) 0 by
          rw [mul_max_of_nonneg _ _ hc, mul_zero]]
      exact mul_lt_mul_iff_right₀ hpos
    rw [hevent]
    exact hX t ht

namespace Dirichlet

/-- The canonical cycle representatives give distinct unordered edges. -/
theorem reprEdge_injective (ε : ℝ) (U : Set (Fin d → ℝ)) :
    Function.Injective
      (fun r : Cycle.indexSet ε U => edgeAdd r.1.1 r.1.2 r.2.2.1) := by
  intro r s h
  exact indexSet_edge_injective ε U r s (congrArg Subtype.val h)

/-- The short displacement part of the centred flux defect. -/
noncomputable def shortDefect (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ)
    (m : ℝ) (p : Fin d → ℝ) (x z : Site d) : ℝ :=
  ∑' r : Cycle.indexSet ε U,
    shortCoeff ε U p x z r * (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m)

/-- The long displacement part of the centred flux defect. -/
noncomputable def longDefect (ε : ℝ) (U : Set (Fin d → ℝ)) (a : Edge d → ℝ)
    (m : ℝ) (p : Fin d → ℝ) (x z : Site d) : ℝ :=
  ∑' r : Cycle.indexSet ε U,
    longCoeff ε U p x z r * (a (edgeAdd r.1.1 r.1.2 r.2.2.1) - m)

/-- Multiplying summable coefficients by bounded centred conductances preserves summability. -/
private theorem summable_centered_mul {ι : Type*} {f : ι → ℝ} (hf : Summable f)
    {b : ι → ℝ} {A : ℝ} (hb : ∀ i, |b i| ≤ A) (m : ℝ) :
    Summable (fun i => f i * (b i - m)) := by
  apply (hf.abs.mul_right (A + |m|)).of_norm_bounded
  intro i
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub (b i) m).trans
    (add_le_add (hb i) (le_refl |m|))) (abs_nonneg _)

/-- The flux defect splits into its short and long displacement series. -/
theorem fluxDefect_eq_short_add_long (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {a : Edge d → ℝ} {A : ℝ}
    (ha : ∀ e, |a e| ≤ A) (m : ℝ) (p : Fin d → ℝ) {x z : Site d}
    (hx : x ∈ latticeSet ε U) (hz : z ≠ 0) :
    fluxDefect ε U a m p x z =
      shortDefect ε U a m p x z + longDefect ε U a m p x z := by
  rw [fluxDefect, dif_neg hz, gpField_sub_eq_tsum_defectCoeff hd hε hU ha m p hx hz]
  have hs := summable_centered_mul (summable_shortCoeff hd hε hU p x z)
    (fun r => ha (edgeAdd r.1.1 r.1.2 r.2.2.1)) m
  have hl := summable_centered_mul (summable_longCoeff hd hε hU p x z)
    (fun r => ha (edgeAdd r.1.1 r.1.2 r.2.2.1)) m
  unfold shortDefect longDefect
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro r
  rw [defectCoeff_eq_short_add_long, add_mul]

/-- Short defects are measurable for coordinatewise measurable conductances. -/
theorem measurable_shortDefect {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → Edge d → ℝ} (ha : ∀ e, Measurable (fun ω => a ω e))
    (ε : ℝ) (U : Set (Fin d → ℝ)) (m : ℝ) (p : Fin d → ℝ) (x z : Site d) :
    Measurable (fun ω => shortDefect ε U (a ω) m p x z) := by
  unfold shortDefect
  exact Measurable.tsum (fun r => measurable_const.mul ((ha _).sub measurable_const))

/-- Long defects are measurable for coordinatewise measurable conductances. -/
theorem measurable_longDefect {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → Edge d → ℝ} (ha : ∀ e, Measurable (fun ω => a ω e))
    (ε : ℝ) (U : Set (Fin d → ℝ)) (m : ℝ) (p : Fin d → ℝ) (x z : Site d) :
    Measurable (fun ω => longDefect ε U (a ω) m p x z) := by
  unfold longDefect
  exact Measurable.tsum (fun r => measurable_const.mul ((ha _).sub measurable_const))

/-- Flux defects are measurable without a boundedness assumption on the conductances. -/
theorem measurable_fluxDefect {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → Edge d → ℝ} (ha : ∀ e, Measurable (fun ω => a ω e))
    (ε : ℝ) (U : Set (Fin d → ℝ)) (m : ℝ) (p : Fin d → ℝ) (x z : Site d) :
    Measurable (fun ω => fluxDefect ε U (a ω) m p x z) := by
  classical
  unfold fluxDefect
  split_ifs with hz
  · exact measurable_const
  · unfold gpField
    apply Measurable.sub
    · apply measurable_const.add
      exact Measurable.tsum (fun r => (((ha _).sub measurable_const).mul
        measurable_const |>.mul measurable_const).mul measurable_const)
    · exact ((ha _).mul measurable_const).mul measurable_const

/-- The square of a sum is bounded by twice the sum of the squares. -/
theorem sq_add_le_two_mul (s l : ℝ) : (s + l) ^ 2 ≤ 2 * s ^ 2 + 2 * l ^ 2 := by
  nlinarith [sq_nonneg (s - l)]

end Dirichlet
end
end LongRange
