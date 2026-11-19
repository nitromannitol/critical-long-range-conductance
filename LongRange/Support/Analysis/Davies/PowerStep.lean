import LongRange.Support.Analysis.Davies.NashDerivative
import LongRange.Support.Analysis.Davies.Comparison

/-!
# Normalized power sums for the Davies iteration

Positivity and monotonicity of the finite power sums used in the Nash comparison.
-/

namespace LatticeProb.Davies.FiniteJumpForm

open Set

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- A nonzero nonnegative initial vector has positive twisted power sums. -/
theorem twist_powSum_pos (ψ f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (p : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 < ∑ i, (F.twist ψ f t i) ^ p := by
  have hnonneg : ∀ i, 0 ≤ F.twist ψ f t i := F.twist_nonneg ψ f hf ht
  have hne := F.twist_ne_zero ψ f hf0 t
  have hex : ∃ i, 0 < F.twist ψ f t i := by
    by_contra h
    apply hne
    funext i
    exact le_antisymm (le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)) (hnonneg i)
  obtain ⟨j, hj⟩ := hex
  exact Finset.sum_pos' (fun i _ ↦ pow_nonneg (hnonneg i) p)
    ⟨j, Finset.mem_univ _, pow_pos hj p⟩

/-- A stronger exponential compensation preserves decay of an even power sum. -/
theorem antitoneOn_compensated_powSum {ψ : ι → ℝ} {Λsq δ : ℝ}
    (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (q : ℕ) (hq : 1 ≤ q) :
    let p : ℕ := 2 * q
    let c : ℝ := (2 * (p : ℝ) + 1) * Λsq + δ / p
    AntitoneOn (fun t ↦ Real.exp (-(p : ℝ) * c * t) *
      ∑ i, (F.twist ψ f t i) ^ p) (Ici 0) := by
  let p : ℕ := 2 * q
  let c : ℝ := (2 * (p : ℝ) + 1) * Λsq + δ / p
  let r : ℝ := levelRate Λsq q
  let d : ℝ := (p : ℝ) * (c - r)
  let N : ℝ → ℝ := fun t ↦ ∑ i, (F.twist ψ f t i) ^ p
  have hp : 0 < (p : ℝ) := by dsimp [p]; positivity
  have hrle : r ≤ (2 * (p : ℝ) + 1) * Λsq := by
    dsimp only [r, levelRate]
    split_ifs with hq1
    · have hq0 : 0 ≤ (p : ℝ) := hp.le
      nlinarith [mul_nonneg hq0 hΛ.1]
    · have hqp : (q : ℝ) ≤ p := by
        exact_mod_cast (show q ≤ 2 * q by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hqp) hΛ.1]
  have hd0 : 0 ≤ d := by
    dsimp [d, c]
    apply mul_nonneg hp.le
    have hdiv : 0 ≤ δ / (p : ℝ) := div_nonneg hδ hp.le
    linarith
  have hbase := F.antitoneOn_level hΛ f hf q hq
  have hbase' : AntitoneOn (fun t ↦ Real.exp (-(p : ℝ) * r * t) * N t) (Ici 0) := by
    simpa only [p, r, N, Nat.cast_mul, Nat.cast_ofNat, neg_mul] using hbase
  have heq (t : ℝ) : Real.exp (-(p : ℝ) * c * t) * N t =
      Real.exp (-d * t) * (Real.exp (-(p : ℝ) * r * t) * N t) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [d]
    ring
  change AntitoneOn (fun t ↦ Real.exp (-(p : ℝ) * c * t) * N t) (Ici 0)
  intro x hx y hy hxy
  dsimp only
  rw [heq x, heq y]
  have hE : Real.exp (-d * y) ≤ Real.exp (-d * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hxy)]
  have hN : 0 ≤ Real.exp (-(p : ℝ) * r * y) * N y := by
    apply mul_nonneg (Real.exp_pos _).le
    exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (F.twist_nonneg ψ f hf hy i) p
  exact mul_le_mul hE (hbase' hx hy hxy) hN (Real.exp_pos _).le

/-- The Nash comparison advances a finite power sum across a positive time interval. -/
theorem powSum_step {ψ : ι → ℝ} {Λsq δ c₁ c₂ : ℝ}
    {θ θstar φ : ℝ → ℝ} (hΛ : F.LambdaBound ψ Λsq) (hδ : 0 ≤ δ)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (q : ℕ) (hq : 1 ≤ q) (hN : F.Nash θ δ)
    (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂) (hinv : External.ckkwInverseProfile θ φ)
    (hpos : ∀ r > 0, 0 < θstar r) (hm : MonotoneOn θstar (Ioi 0))
    (hratio : MonotoneOn (fun r ↦ θstar r / r) (Ioi 0))
    (hcompare : ∀ r > 0, c₁⁻¹ * θstar (c₂⁻¹ * r) ≤ θ r ∧
      θ r ≤ c₁ * θstar (c₂ * r)) {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ < t₁) :
    let p : ℕ := 2 * q
    (∑ i, (F.twist ψ f t₁ i) ^ (2 * p)) ≤
      c₂ ^ 2 * φ ((t₁ - t₀) / (c₁ * c₂) ^ 2) *
      Real.exp ((2 * (p : ℝ) * ((2 * (p : ℝ) + 1) * Λsq) + 2 * δ) * (t₁ - t₀)) *
      (∑ i, (F.twist ψ f t₀ i) ^ p) ^ 2 := by
  let p : ℕ := 2 * q
  let c : ℝ := (2 * (p : ℝ) + 1) * Λsq + δ / p
  let κ : ℝ := (p : ℝ) * c
  let n : ℝ → ℝ := fun t ↦ ∑ i, (F.twist ψ f t i) ^ p
  let m : ℝ → ℝ := fun t ↦ ∑ i, (F.twist ψ f t i) ^ (2 * p)
  let b : ℝ → ℝ := fun t ↦ Real.exp (-(2 * κ) * t) * m t
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hnorm (t : ℝ) (k : ℕ) :
      (∑ i, (Real.exp (-c * t) * F.twist ψ f t i) ^ k) =
        Real.exp (-(k : ℝ) * c * t) * ∑ i, (F.twist ψ f t i) ^ k := by
    simp only [mul_pow, ← Finset.mul_sum, ← Real.exp_nat_mul]
    congr 2
    ring
  have hfun : (fun t ↦ ∑ i, (Real.exp (-c * t) * F.twist ψ f t i) ^ (2 * p)) = b := by
    funext t
    rw [hnorm]
    dsimp only [b, m, κ]
    congr 2
    push_cast
    ring
  have hsingle (t : ℝ) : (∑ i, (Real.exp (-c * t) * F.twist ψ f t i) ^ p) =
      Real.exp (-κ * t) * n t := by
    rw [hnorm]
    dsimp [κ, n]
    congr 2
    ring
  have hbder (t : ℝ) : DifferentiableAt ℝ b t := by
    have h := F.hasDerivAt_rescaled_powSum ψ f p c t
    apply h.differentiableAt.congr_of_eventuallyEq
    filter_upwards with s
    dsimp [b, m, κ]
    congr 2
    ring
  have hd (u : ℝ) (hu : u ∈ Icc t₀ t₁) : HasDerivAt b (deriv b u) u :=
    (hbder u).hasDerivAt
  have hder (u : ℝ) (hu : u ∈ Icc t₀ t₁) : deriv b u ≤
      -(Real.exp (-κ * u) * n u) ^ 2 * thetaLow c₁ c₂ θstar
        (b u / (Real.exp (-κ * u) * n u) ^ 2) := by
    have hu0 : 0 ≤ u := le_trans ht₀ hu.1
    have h := F.deriv_le_nash hΛ f hf hf0 p hp hδ hN
      (fun r hr ↦ thetaLow_le hcompare hr) u hu0
    dsimp only at h
    change deriv (fun t ↦ ∑ i, (Real.exp (-c * t) * F.twist ψ f t i) ^ (2 * p)) u ≤ _ at h
    rw [hfun, hsingle, hnorm] at h
    have htwo : Real.exp (-(↑(2 * p) : ℝ) * c * u) *
        (∑ i, F.twist ψ f u i ^ (2 * p)) = b u := by
      dsimp [b, m, κ]
      congr 2
      push_cast
      ring
    rw [htwo] at h
    exact h
  have hn : ∀ u ∈ Icc t₀ t₁, 0 < n u := fun u hu ↦
    F.twist_powSum_pos ψ f hf hf0 p (le_trans ht₀ hu.1)
  have hmpos : ∀ u ∈ Icc t₀ t₁, 0 < m u := fun u hu ↦
    F.twist_powSum_pos ψ f hf hf0 (2 * p) (le_trans ht₀ hu.1)
  have hanti : AntitoneOn (fun u ↦ Real.exp (-κ * u) * n u) (Icc t₀ t₁) := by
    have h := F.antitoneOn_compensated_powSum hΛ hδ f hf q hq
    have heq : (fun u ↦ Real.exp (-κ * u) * n u) =
        (fun u ↦ Real.exp (-(p : ℝ) * c * u) * n u) := by
      funext u
      dsimp only [κ]
      congr 2
      ring
    rw [heq]
    apply h.mono
    intro u hu
    exact le_trans ht₀ hu.1
  have h := le_exp_mul_phi_of_nash_deriv hc₁ hc₂ hinv hpos hm hratio hcompare ht
    hn hmpos hanti hd hder
  change m t₁ ≤ _
  have hk : 2 * κ = 2 * (p : ℝ) * ((2 * (p : ℝ) + 1) * Λsq) + 2 * δ := by
    dsimp [κ, c]
    field_simp
  rw [hk] at h
  exact h

end
end LatticeProb.Davies.FiniteJumpForm
