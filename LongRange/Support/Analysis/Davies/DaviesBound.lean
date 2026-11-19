import LongRange.Support.Analysis.Davies.KernelBound

/-!
# Davies bounds for finite jump forms

Kernel bounds obtained by squaring the finite twisted-semigroup estimate.
-/

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- The twisted kernel satisfies the squared two-to-infinity bound. -/
theorem twistKernel_le {ψ : ι → ℝ} {Λsq δ c₁ c₂ l t c C ε : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (hN : F.Nash θ δ) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Set.Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Set.Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) (hl : 2 < l) (ht : 0 < t)
    (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hchoice : 2 + 6 / ε ≤ l)
    (hprofile : External.ckkwProductBound φ l c C) (i j : ι) :
    F.twistKernel ψ t i j ≤
      c₂ ^ 2 * C * φ (c * ((t / 2) / (c₁ * c₂) ^ 2)) *
        Real.exp (t * ((1 + ε) * Λsq + δ)) := by
  let s : ℝ := t / 2
  let v : ℝ := C * φ (c * (s / (c₁ * c₂) ^ 2))
  let e : ℝ := (1 + ε) * Λsq + δ
  let K : ℝ := c₂ * v ^ (1 / 2 : ℝ) * Real.exp (s * e)
  have hs : 0 < s := by dsimp [s]; positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    exact mul_nonneg hC.le (hinv.2.1 _ (by positivity)).1.le
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hv _))
    (Real.exp_pos _).le
  have hbound (ψ' : ι → ℝ) (hΛ' : F.LambdaBound ψ' Λsq) (f : ι → ℝ)
      (hf : ∀ i, 0 ≤ f i) (i : ι) :
      F.twist ψ' f s i ≤ K * Real.sqrt (∑ j, f j ^ 2) := by
    simpa only [Real.sqrt_eq_rpow] using F.twist_le hΛ' hδ f hf hN hc₁ hc₂ hinv hpos hm
      hratio hcompare hl hs hc hC hε hchoice hprofile i
  have hsq := F.twistKernel_le_sq hs.le hK (hbound ψ hΛ) (hbound (-ψ) (LambdaBound.neg F hΛ)) i j
  have hs2 : s + s = t := by dsimp [s]; ring
  rw [hs2] at hsq
  have hv2 : (v ^ (1 / 2 : ℝ)) ^ 2 = v := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hv]
  have he2 : (Real.exp (s * e)) ^ 2 = Real.exp (t * e) := by
    rw [sq, ← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  have hK2 : K ^ 2 = c₂ ^ 2 * v * Real.exp (t * e) := by
    dsimp only [K]
    rw [mul_pow, mul_pow, hv2, he2]
  calc
    F.twistKernel ψ t i j ≤ K ^ 2 := hsq
    _ = c₂ ^ 2 * v * Real.exp (t * e) := hK2
    _ = _ := by dsimp [v, s, e]; ring

end
end LatticeProb.Davies.FiniteJumpForm
