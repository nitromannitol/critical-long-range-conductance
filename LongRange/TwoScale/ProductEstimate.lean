import LongRange.TwoScale.KernelSums
import LongRange.Calculus.BilinForm
import LongRange.Corrector.Support

/-!
# Multiplication in the critical discrete seminorm

The discrete Leibniz rule bounds multiplication by a bounded function whose increments
are controlled by the truncated Euclidean distance. The kernel second moment and its
exterior tail make the resulting bound uniform in the lattice scale.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The truncated second-moment kernel is summable. -/
lemma summable_kernel_min_sq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun w : Site d =>
      jumpKernel (physical ε w) * min (radius (physical ε w)) 1 ^ 2) := by
  apply (summable_jumpKernel hd hε).of_nonneg_of_le
  · intro w
    exact mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)
  · intro w
    apply mul_le_of_le_one_right (jumpKernel_nonneg _)
    exact (sq_le_one_iff_abs_le_one _).mpr
      (by rw [abs_of_nonneg (le_min (radius_nonneg _) zero_le_one)]; exact min_le_right _ _)

/-- The normalized truncated second moment is uniformly bounded in the scale. -/
lemma kernel_min_sq_bound (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ε ^ d / kappa d ε * ∑' w : Site d,
        jumpKernel (physical ε w) * min (radius (physical ε w)) 1 ^ 2 ≤ K := by
  classical
  obtain ⟨T, hT, htail⟩ := kernel_tail_sum_bound d
  refine ⟨1 + T, by linarith, ?_⟩
  intro ε hε
  let s := unitBallIndices d ε
  let f := fun w : Site d =>
    jumpKernel (physical ε w) * min (radius (physical ε w)) 1 ^ 2
  let a := fun w : Site d =>
    if w ∈ s then jumpKernel (physical ε w) * radius (physical ε w) ^ 2 else 0
  let t := fun w : Site d => if 1 < radius (physical ε w) then
    jumpKernel (physical ε w) * (1 + radius (physical ε w)) else 0
  have ha : Summable a := summable_of_ne_finset_zero (s := s) (by
    intro w hw; exact if_neg hw)
  have ht : Summable t := (htail ε hε).1
  have hf : Summable f := summable_kernel_min_sq hd hε.1
  have hpoint : ∀ w, f w ≤ a w + t w := by
    intro w
    by_cases hw : w ∈ s
    · have hr := ((mem_unitBallIndices hε.1 w).mp hw).2
      simp only [f, a, t, if_pos hw, min_eq_left hr, if_neg (not_lt.mpr hr), add_zero]
      exact le_rfl
    · by_cases hz : w = 0
      · subst w
        norm_num [f, a, t, physical, radius]
      · have hr : 1 < radius (physical ε w) := by
          by_contra hn
          exact hw ((mem_unitBallIndices hε.1 w).mpr ⟨hz, le_of_not_gt hn⟩)
        simp only [f, a, t, if_neg hw, if_pos hr, min_eq_right hr.le,
          one_pow, mul_one, zero_add]
        exact le_mul_of_one_le_right (jumpKernel_nonneg _) (by
          linarith [radius_nonneg (physical ε w)])
  have hsum : (∑' w, a w) = ∑ w ∈ s,
      jumpKernel (physical ε w) * radius (physical ε w) ^ 2 := by
    rw [tsum_eq_sum (s := s) (fun w hw => by exact if_neg hw)]
    exact Finset.sum_congr rfl (fun w hw => if_pos hw)
  have hsmall : ε ^ d / kappa d ε * ∑' w, a w = 1 := by
    rw [hsum]
    change ε ^ d / kappa d ε * ∑ w ∈ unitBallIndices d ε,
      jumpKernel (physical ε w) * radius (physical ε w) ^ 2 = 1
    rw [div_mul_eq_mul_div, ← kappa_eq_radial_sum hε.1,
      div_self (kappa_pos hd hε).ne']
  have hlarge : ε ^ d / kappa d ε * ∑' w, t w ≤ T := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (kappa_pos hd hε)).mpr
    exact ((htail ε hε).2).trans
      (le_mul_of_one_le_right hT.le (one_le_kappa hd hε))
  calc
    _ ≤ ε ^ d / kappa d ε * ∑' w, (a w + t w) :=
      mul_le_mul_of_nonneg_left (hf.tsum_le_tsum hpoint (ha.add ht))
        (div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le)
    _ = 1 + ε ^ d / kappa d ε * ∑' w, t w := by
      rw [ha.tsum_add ht, mul_add, hsmall]
    _ ≤ 1 + T := add_le_add le_rfl hlarge

/-- The scalar discrete Leibniz rule bounds the square of a product increment. -/
lemma mul_increment_sq_le {a b u v B r : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    (ha : |a| ≤ B) (hab : |a - b| ≤ B * r) :
    (a * u - b * v) ^ 2 ≤ 2 * B ^ 2 * (u - v) ^ 2 +
      2 * B ^ 2 * r ^ 2 * v ^ 2 := by
  have ha2 : a ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hB).mpr ha
  have hab2 : (a - b) ^ 2 ≤ B ^ 2 * r ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (a - b)) (mul_nonneg hB hr)).mpr hab
    simpa only [sq_abs, mul_pow] using h
  have hfirst := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (u - v))
  have hsecond := mul_le_mul_of_nonneg_right hab2 (sq_nonneg v)
  nlinarith only [hfirst, hsecond, sq_nonneg (a * (u - v) - (a - b) * v)]

/-- Bounded multipliers with truncated Lipschitz increments preserve the critical seminorm. -/
theorem h1CritSq_mul_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (U : Set (Fin d → ℝ)), Bornology.IsBounded U →
      ∀ (b ψ : Site d → ℝ) (B : ℝ), 0 ≤ B → (∀ q, |b q| ≤ B) →
      (∀ q w, |b (q + w) - b q| ≤ B * min (radius (physical ε w)) 1) →
      SupportedIn ε U ψ →
        h1CritSq ε (fun x => b x * ψ x) ≤
          C * B ^ 2 * (h1CritSq ε ψ + l2NormSq ε U ψ) := by
  obtain ⟨K, hK, hkernel⟩ := kernel_min_sq_bound hd
  refine ⟨2 + 2 * K, by linarith, ?_⟩
  intro ε hε U hU b ψ B hB hb hinc hψ
  have hfin := hψ.hasFiniteSupport hε.1 hU
  have hmul : Function.HasFiniteSupport (fun x => b x * ψ x) :=
    Function.HasFiniteSupport.mul_right b hfin
  have hsψ := summable_h1CritSq hd hε.1 hfin
  have hsmul := summable_h1CritSq hd hε.1 hmul
  let k := fun w : Site d =>
    jumpKernel (physical ε w) * min (radius (physical ε w)) 1 ^ 2
  have hsk : Summable k := summable_kernel_min_sq hd hε.1
  have hsquare : Summable (fun x => ψ x ^ 2) := by
    have hf : Function.HasFiniteSupport (fun x : Site d => ψ x * ψ x) :=
      Function.HasFiniteSupport.mul_right ψ hfin
    simpa only [pow_two] using (summable_of_hasFiniteSupport hf)
  have hsprod : Summable (fun p : Site d × Site d => ψ p.1 ^ 2 * k p.2) :=
    hsquare.mul_of_nonneg hsk (fun x => sq_nonneg _) (fun w =>
      mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _))
  have hmajor := (hsψ.mul_left (2 * B ^ 2)).add (hsprod.mul_left (2 * B ^ 2))
  have hpoint (p : Site d × Site d) :
      jumpKernel (physical ε p.2) *
          (b (p.1 + p.2) * ψ (p.1 + p.2) - b p.1 * ψ p.1) ^ 2 ≤
        2 * B ^ 2 * (jumpKernel (physical ε p.2) *
          (ψ (p.1 + p.2) - ψ p.1) ^ 2) +
        2 * B ^ 2 * (ψ p.1 ^ 2 * k p.2) := by
    have h := mul_le_mul_of_nonneg_left
      (mul_increment_sq_le (u := ψ (p.1 + p.2)) (v := ψ p.1) hB
        (le_min (radius_nonneg _) zero_le_one)
        (hb (p.1 + p.2)) (hinc p.1 p.2)) (jumpKernel_nonneg (physical ε p.2))
    calc
      _ ≤ jumpKernel (physical ε p.2) *
          (2 * B ^ 2 * (ψ (p.1 + p.2) - ψ p.1) ^ 2 +
            2 * B ^ 2 * min (radius (physical ε p.2)) 1 ^ 2 * ψ p.1 ^ 2) := h
      _ = _ := by dsimp only [k]; ring
  have hsum := hsmul.tsum_le_tsum hpoint hmajor
  rw [Summable.tsum_add (hsψ.mul_left (2 * B ^ 2))
    (hsprod.mul_left (2 * B ^ 2)), tsum_mul_left, tsum_mul_left,
    ← hsquare.tsum_mul_tsum hsk hsprod] at hsum
  have hl2 : ε ^ d * ∑' x, ψ x ^ 2 = l2NormSq ε U ψ := by
    unfold l2NormSq
    congr 1
    symm
    apply tsum_subtype_eq_of_support_subset (f := fun x : Site d => ψ x ^ 2)
      (s := latticeSet ε U)
    intro x hx
    by_contra hn
    apply hx
    change ψ x ^ 2 = 0
    rw [hψ x hn]
    norm_num
  have hc : 0 ≤ ε ^ (2 * d) / kappa d ε :=
    div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le
  have hscaled := mul_le_mul_of_nonneg_left hsum hc
  have hfactor : ε ^ (2 * d) / kappa d ε *
      (2 * B ^ 2 * (∑' x, ψ x ^ 2) * ∑' w, k w) =
      2 * B ^ 2 * (ε ^ d * ∑' x, ψ x ^ 2) *
        (ε ^ d / kappa d ε * ∑' w, k w) := by
    rw [show 2 * d = d + d by omega, pow_add]
    ring
  have hmass : 0 ≤ l2NormSq ε U ψ := by
    rw [← hl2]
    exact mul_nonneg (pow_nonneg hε.1.le _) (tsum_nonneg (fun x => sq_nonneg _))
  have hbound : h1CritSq ε (fun x => b x * ψ x) ≤
      2 * B ^ 2 * h1CritSq ε ψ +
        2 * B ^ 2 * l2NormSq ε U ψ * K := by
    calc
      _ ≤ ε ^ (2 * d) / kappa d ε *
          (2 * B ^ 2 * ∑' p : Site d × Site d,
            jumpKernel (physical ε p.2) * (ψ (p.1 + p.2) - ψ p.1) ^ 2) +
          ε ^ (2 * d) / kappa d ε *
            (2 * B ^ 2 * (∑' x, ψ x ^ 2) * ∑' w, k w) := by
        simpa only [h1CritSq, mul_add, mul_assoc] using hscaled
      _ = 2 * B ^ 2 * h1CritSq ε ψ +
          2 * B ^ 2 * l2NormSq ε U ψ *
            (ε ^ d / kappa d ε * ∑' w, k w) := by
        rw [hfactor, hl2]
        unfold h1CritSq
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hkernel ε hε)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hmass))
  have henergy : 0 ≤ h1CritSq ε ψ := mul_nonneg hc
    (tsum_nonneg (fun p => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))
  have hnonneg := mul_nonneg (mul_nonneg (sq_nonneg B) henergy) hK.le
  have hnonneg' := mul_nonneg (sq_nonneg B) hmass
  nlinarith only [hbound, hnonneg, hnonneg']

end
end LongRange
