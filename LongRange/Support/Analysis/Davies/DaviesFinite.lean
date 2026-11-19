import LongRange.Support.Analysis.Davies.DaviesBound

/-!
# Davies estimate for finite jump forms

The finite kernel estimate with the absolute perturbation difference.
-/

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- Undo conjugation in a twisted-kernel bound. -/
theorem semigroup_le_of_twistKernel_le (ψ : ι → ℝ) (t B : ℝ) (i j : ι)
    (h : F.twistKernel ψ t i j ≤ B) :
    F.semigroup t i j ≤ B * Real.exp (ψ j - ψ i) := by
  have he : Real.exp (ψ i) * Real.exp (-ψ j) * Real.exp (ψ j - ψ i) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have ha : ψ i + -ψ j + (ψ j - ψ i) = 0 := by ring
    rw [ha, Real.exp_zero]
  have hid : F.twistKernel ψ t i j * Real.exp (ψ j - ψ i) = F.semigroup t i j := by
    dsimp [twistKernel]
    calc
      _ = (Real.exp (ψ i) * Real.exp (-ψ j) * Real.exp (ψ j - ψ i)) *
          F.semigroup t i j := by ring
      _ = _ := by rw [he, one_mul]
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (ψ j - ψ i)).le
  rwa [hid] at hh

/-- Bounds for both perturbation signs produce the absolute difference. -/
theorem semigroup_le_of_twistKernel_le_abs (ψ : ι → ℝ) (t B : ℝ) (i j : ι)
    (h : F.twistKernel ψ t i j ≤ B) (hneg : F.twistKernel (-ψ) t i j ≤ B) :
    F.semigroup t i j ≤ B * Real.exp (-|ψ j - ψ i|) := by
  by_cases hd : 0 ≤ ψ j - ψ i
  · have hh := F.semigroup_le_of_twistKernel_le (-ψ) t B i j hneg
    rw [abs_of_nonneg hd]
    have he : -(ψ j - ψ i) = ψ i - ψ j := by ring
    rw [he]
    simpa only [Pi.neg_apply, neg_sub_neg] using hh
  · have hh := F.semigroup_le_of_twistKernel_le ψ t B i j h
    have hd' : ψ j - ψ i ≤ 0 := le_of_not_ge hd
    rw [abs_of_nonpos hd', neg_neg]
    exact hh

/-- The finite Davies estimate for a specified geometric parameter. -/
theorem semigroup_le_davies {ψ : ι → ℝ} {Λsq δ c₁ c₂ l t c C ε : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (hN : F.Nash θ δ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (hl : 2 < l) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hchoice : 2 + 6 / ε ≤ l)
    (hprofile : External.ckkwProductBound φ l c C) (i j : ι) :
    F.semigroup t i j ≤ c₂ ^ 2 * C * φ (c * ((t / 2) / (c₁ * c₂) ^ 2)) *
      Real.exp (δ * t) * Real.exp (-|ψ j - ψ i| + (1 + ε) * Λsq * t) := by
  let B := c₂ ^ 2 * C * φ (c * ((t / 2) / (c₁ * c₂) ^ 2)) *
    Real.exp (t * ((1 + ε) * Λsq + δ))
  have h := F.twistKernel_le hΛ hδ hN hc₁ hc₂ hinv hpos hm hratio hcompare hl ht
    hc hC hε hchoice hprofile i j
  have hn := F.twistKernel_le (LambdaBound.neg F hΛ) hδ hN hc₁ hc₂ hinv hpos hm hratio
    hcompare hl ht hc hC hε hchoice hprofile i j
  have hb : F.semigroup t i j ≤ B * Real.exp (-|ψ j - ψ i|) :=
    F.semigroup_le_of_twistKernel_le_abs ψ t B i j h hn
  have he : Real.exp (t * ((1 + ε) * Λsq + δ)) * Real.exp (-|ψ j - ψ i|) =
      Real.exp (δ * t) * Real.exp (-|ψ j - ψ i| + (1 + ε) * Λsq * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    F.semigroup t i j ≤ B * Real.exp (-|ψ j - ψ i|) := hb
    _ = _ := by
      dsimp [B]
      rw [mul_assoc (c₂ ^ 2 * C * φ (c * ((t / 2) / (c₁ * c₂) ^ 2))), he]
      ring

/-- The finite Davies estimate with constants independent of the jump form and profile. -/
theorem davies (c₁ c₂ : ℝ) (c C : ℝ → ℝ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hdata : External.ckkwProductData c C) (ε : ℝ) (hε : 0 < ε) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
    ∀ θ θstar φ : ℝ → ℝ,
      External.ckkwInverseProfile θ φ → External.ckkwProductProfile φ c C →
      (∀ r > 0, 0 < θstar r) → MonotoneOn θstar (Set.Ioi 0) →
      MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0) →
      (∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
        θ r ≤ c₁ * θstar (c₂ * r)) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)
      (δ : ℝ), 0 ≤ δ → F.Nash θ δ →
    ∀ (ψ : ι → ℝ) (Λsq : ℝ), F.LambdaBound ψ Λsq →
    ∀ t > 0, ∀ i j : ι,
      F.semigroup t i j ≤ A * φ (a * t) * Real.exp (δ * t) *
        Real.exp (-|ψ j - ψ i| + (1 + ε) * Λsq * t) := by
  obtain ⟨L, hL, hdata⟩ := hdata
  let l := max (L + 1) (2 + 6 / ε)
  have hlL : L < l := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hl : 2 < l := lt_trans hL hlL
  have hchoice : 2 + 6 / ε ≤ l := le_max_right _ _
  obtain ⟨hc, hC⟩ := hdata l hlL
  refine ⟨c₂ ^ 2 * C l, c l / (2 * (c₁ * c₂) ^ 2), by positivity, by positivity, ?_⟩
  intro θ θstar φ hinv hprofile hpos hm hratio hcompare ι _ _ F δ hδ hN ψ Λsq hΛ t ht i j
  have hprod := hprofile l hl hc hC
  have h := F.semigroup_le_davies hΛ hδ hN hc₁ hc₂ hinv hpos hm hratio hcompare hl ht
    hc hC hε hchoice hprod i j
  have hc₁0 : c₁ ≠ 0 := by linarith
  have hc₂0 : c₂ ≠ 0 := by linarith
  have harg : c l * (t / 2 / (c₁ * c₂) ^ 2) =
      c l / (2 * (c₁ * c₂) ^ 2) * t := by field_simp
  simpa only [harg] using h

end
end LatticeProb.Davies.FiniteJumpForm
