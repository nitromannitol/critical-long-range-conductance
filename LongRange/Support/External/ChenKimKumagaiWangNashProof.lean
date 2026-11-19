import LongRange.Support.External.ChenKimKumagaiWang
import LongRange.Support.Analysis.Semigroup.EnergyDecay

/-!
# Ultracontractivity implies a Nash inequality

Proof of `ChenKimKumagaiWangNash`, the discrete form of Chen–Kim–Kumagai–Wang (2021),
Proposition 3.1(ii), following Coulhon's argument (Proposition II.2 of *Ultracontractivity and
Nash type inequalities*, J. Funct. Anal. 141 (1996)) for the semigroup `e^{-δt} P_t`.

Let `r = ‖f‖₂²` and `a(t) = ⟨f, P_t f⟩`. The transition bound `p_t ≤ φ(t) e^{δt}` and
`‖f‖₁ ≤ 1` give `a(t) ≤ φ(t) e^{δt}`. Midpoint log-convexity of `a` and its first-order
expansion at zero give `a(t) ≥ r e^{-t E(f) / r}`. Taking logarithms,
`(r / t) log(r / φ(t)) ≤ E(f) + δ r` for every `t > 0`.
-/

namespace LatticeProb.External

open JumpChain
open scoped NNReal ENNReal

/-- The kernel of the statement is the real transition probability. -/
theorem ckkwKernel_eq_heatKernel {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (rates : JumpChain.BoundedRates S) (t : ℝ≥0) (i j : S) :
    ckkwKernel rates t i j = rates.heatKernel t i j :=
  rfl

/-- The energy of the statement is the Dirichlet energy of the chain. -/
theorem ckkwEnergy_eq_energy {S : Type*} (rates : JumpChain.BoundedRates S) (f : S → ℝ) :
    ckkwEnergy rates f = rates.energy f :=
  rfl

/-- **CKKW Proposition 3.1(ii)** (discrete form): an on-diagonal upper bound
`p_t(i, j) ≤ φ(t) e^{δt}` implies the Nash inequality with the supremum profile. -/
theorem chenKimKumagaiWangNash_holds : ChenKimKumagaiWangNash := by
  intro S _ _ _ rates hs δ φ hδ hφ _ hbound f hf2 hf1 hf1le hr
  rw [ckkwNashProfile]
  refine iSup_le fun t ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨t, ht⟩ := t
  have ht0 : 0 < t := ht
  change ckkwNormSq f / t * Real.log (ckkwNormSq f / φ t) ≤ _
  rw [ckkwEnergy_eq_energy]
  have hrdef : ckkwNormSq f = ∑' i, f i ^ 2 := rfl
  rw [hrdef] at hr ⊢
  set r := ∑' i, f i ^ 2
  set E := rates.energy f
  set τ : ℝ≥0 := ⟨t, ht0.le⟩ with hτ
  have hτt : (τ : ℝ) = t := rfl
  have hτpos : 0 < τ := ht0
  have hlow := rates.mul_exp_le_heatForm hs hf2 hr τ
  have hup := rates.heatForm_le_of_heatKernel_le hf1 (t := τ)
    (fun i j ↦ (ckkwKernel_eq_heatKernel rates τ i j) ▸ hbound τ hτpos i j)
  rw [hτt] at hlow hup
  have hF : (∑' i, |f i|) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ ∑' i, |f i| := tsum_nonneg fun i ↦ abs_nonneg _
    nlinarith
  have hφt := hφ t ht0
  have hB : 0 ≤ φ t * Real.exp (δ * t) := by positivity
  have key : r * Real.exp (-(t * E / r)) ≤ φ t * Real.exp (δ * t) :=
    hlow.trans (hup.trans (mul_le_of_le_one_right hB hF))
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul hφt.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [Real.log_div hr.ne' hφt.ne']
  have hle : Real.log r - Real.log (φ t) ≤ t * (E + δ * r) / r := by
    have h : t * (E + δ * r) / r = t * E / r + δ * t := by
      field_simp
    linarith
  calc
    r / t * (Real.log r - Real.log (φ t)) ≤ r / t * (t * (E + δ * r) / r) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _ = E + δ * r := by
      field_simp

end LatticeProb.External
