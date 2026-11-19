import LongRange.Support.Analysis.Davies.Nash
import LongRange.Support.Analysis.Davies.RescaledPower

/-!
# Nash bound for rescaled power sums

The finite Nash inequality bounds the derivative used in Davies iteration.
-/

namespace LatticeProb.Davies.FiniteJumpForm

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : FiniteJumpForm ι)

/-- A Nash differential inequality for the rescaled twisted semigroup. -/
theorem deriv_le_nash {ψ : ι → ℝ} {Λsq : ℝ} (hΛ : F.LambdaBound ψ Λsq)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hf0 : f ≠ 0)
    (p : ℕ) (hp : 2 ≤ p) {θ θlow : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hN : F.Nash θ δ) (hθ : ∀ r > 0, θlow r ≤ θ r) (t : ℝ) (ht : 0 ≤ t) :
    let c := (2 * (p : ℝ) + 1) * Λsq + δ / p
    let g := fun s i ↦ Real.exp (-c * s) * F.twist ψ f s i
    deriv (fun s ↦ ∑ i, (g s i) ^ (2 * p)) t ≤
      -(∑ i, (g t i) ^ p) ^ 2 *
        θlow ((∑ i, (g t i) ^ (2 * p)) / (∑ i, (g t i) ^ p) ^ 2) := by
  let c : ℝ := (2 * (p : ℝ) + 1) * Λsq + δ / p
  let u : ι → ℝ := F.twist ψ f t
  let S : ℝ := ∑ i, (u i) ^ p
  let B : ℝ := ∑ i, (u i) ^ (2 * p)
  let k : ℝ := Real.exp (-(p : ℝ) * c * t)
  have hpu : 1 ≤ p := by omega
  have hu : ∀ i, 0 ≤ u i := fun i ↦ F.twist_nonneg ψ f hf ht i
  have hune : u ≠ 0 := F.twist_ne_zero ψ f hf0 t
  have hex : ∃ i, 0 < u i := by
    by_contra h
    apply hune
    funext i
    have hle : u i ≤ 0 := le_of_not_gt (fun hi ↦ h ⟨i, hi⟩)
    exact le_antisymm hle (hu i)
  obtain ⟨j, hj⟩ := hex
  have hS : 0 < S := by
    apply Finset.sum_pos' (fun i _ ↦ pow_nonneg (hu i) p)
    exact ⟨j, Finset.mem_univ _, pow_pos hj _⟩
  have hB : 0 < B := by
    apply Finset.sum_pos' (fun i _ ↦ pow_nonneg (hu i) (2 * p))
    exact ⟨j, Finset.mem_univ _, pow_pos hj _⟩
  have hw1 : (∑ i, |(fun i ↦ u i ^ p) i|) = S := by
    simp only [abs_of_nonneg (pow_nonneg (hu _) _)]
    rfl
  have hw2 : (∑ i, ((fun i ↦ u i ^ p) i) ^ 2) = B := by
    simp only [← pow_mul]
    congr 1
    funext i
    congr 1
    omega
  have hn := F.nash_scaled hN (fun i ↦ u i ^ p) (by rwa [hw1]) (by rwa [hw2])
  rw [hw1, hw2] at hn
  have hcomp := hθ (B / S ^ 2) (div_pos hB (sq_pos_of_pos hS))
  have hbound : S ^ 2 * θlow (B / S ^ 2) ≤
      F.form (fun i ↦ u i ^ p) (fun i ↦ u i ^ p) + δ * B :=
    (mul_le_mul_of_nonneg_left hcomp (sq_nonneg S)).trans hn
  have heven (s : ℝ) : Real.exp (-(2 * (p : ℝ) * c) * s) =
      Real.exp (-c * s) ^ (2 * p) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpExp : Real.exp (-c * t) ^ p = k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hfun : (fun s ↦ ∑ i, (Real.exp (-c * s) * F.twist ψ f s i) ^ (2 * p)) =
      (fun s ↦ Real.exp (-(2 * (p : ℝ) * c) * s) *
        ∑ i, (F.twist ψ f s i) ^ (2 * p)) := by
    funext s
    rw [heven, Finset.mul_sum]
    simp only [mul_pow]
  have hs : (∑ i, (Real.exp (-c * t) * u i) ^ p) = k * S := by
    simp only [mul_pow, ← Finset.mul_sum, hpExp]
    rfl
  have hb : (∑ i, (Real.exp (-c * t) * u i) ^ (2 * p)) = k ^ 2 * B := by
    simp only [mul_pow, ← Finset.mul_sum]
    rw [show 2 * p = p * 2 by omega, pow_mul, hpExp]
    simp only [Nat.mul_comm p 2]
    rfl
  have hek : Real.exp (-(2 * (p : ℝ) * c) * t) = k ^ 2 := by
    rw [heven, show 2 * p = p * 2 by omega, pow_mul, hpExp]
  have hk : 0 < k := Real.exp_pos _
  have hratio : k ^ 2 * B / (k * S) ^ 2 = B / S ^ 2 := by
    field_simp
  have hd := F.rescaled_powSum_deriv_le_form hΛ f hf p hpu δ t ht
  change deriv (fun s ↦ Real.exp (-(2 * (p : ℝ) * c) * s) *
      ∑ i, (F.twist ψ f s i) ^ (2 * p)) t ≤ _ at hd
  rw [hek] at hd
  dsimp only
  rw [hfun, hs, hb, hratio]
  have hδB : 0 ≤ δ * B := mul_nonneg hδ hB.le
  have hm := mul_le_mul_of_nonneg_left hbound (sq_nonneg k)
  nlinarith [sq_nonneg (k * S)]

end
end LatticeProb.Davies.FiniteJumpForm
