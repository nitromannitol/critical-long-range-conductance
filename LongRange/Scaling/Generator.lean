import LongRange.TwoScale.Scaling
import LongRange.Calculus.Linearity

/-!
# Generator scaling under halving of physical coordinates

The same integer site labels both physical lattices. Kernel homogeneity gives the exact
factor in the introduction's deterministic change of scale, for the same conductances.
-/

namespace LongRange.Scaling

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- The microscopic series separates the two powers of the spacing from the normalization. -/
theorem generator_eq_microscopic {ε : ℝ} (hε : 0 < ε) (a : Edge d → ℝ)
    (u : Site d → ℝ) (q : Site d) :
    generator ε a u q = (ε ^ 2 * kappa d ε)⁻¹ *
      ∑' w : Site d, if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (u (q + w) - u q) * jumpKernel (physical 1 w) := by
  have hterm (w : Site d) :
      (if hw : w = 0 then 0 else a (edgeAdd q w hw) *
        (u (q + w) - u q) * jumpKernel (physical ε w)) =
      (ε ^ (d + 2))⁻¹ * (if hw : w = 0 then 0 else
        a (edgeAdd q w hw) * (u (q + w) - u q) * jumpKernel (physical 1 w)) := by
    split
    · simp only [mul_zero]
    · rw [jumpKernel_physical_scaling hε]
      ring
  unfold generator
  simp_rw [hterm]
  rw [tsum_mul_left, ← mul_assoc]
  congr 1
  rw [pow_add]
  by_cases hk : kappa d ε = 0
  · simp only [hk, div_zero, zero_mul, mul_zero, inv_zero]
  · field_simp [hε.ne', hk]

/-- Halving the physical spacing multiplies the generator by the exact normalization ratio. -/
theorem generator_half (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (a : Edge d → ℝ) (u : Site d → ℝ) (q : Site d) :
    generator (ε / 2) a u q =
      (4 * kappa d ε / kappa d (ε / 2)) * generator ε a u q := by
  have hh : ε / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  rw [generator_eq_microscopic hh.1, generator_eq_microscopic hε.1]
  rw [← mul_assoc]
  congr 1
  field_simp [hε.1.ne', (kappa_pos hd hε).ne', (kappa_pos hd hh).ne']
  ring

/-- Multiplying the rescaled solution by the normalization ratio gives four times the forcing. -/
theorem generator_half_normalized (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (a : Edge d → ℝ)
    (u : Site d → ℝ) (q : Site d) :
    generator (ε / 2) a (fun z => kappa d (ε / 2) / kappa d ε * u z) q =
      4 * generator ε a u q := by
  have hh : ε / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  rw [generator_const_mul, generator_half hd hε]
  field_simp [(kappa_pos hd hε).ne', (kappa_pos hd hh).ne']

/-- Bounded-error logarithmic growth forces fixed positive halving increments arbitrarily
close to zero. This suffices for the printed not-both-little-o obstruction. -/
theorem kappa_half_increment_frequently_pos (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) (min δ 1) ∧ c ≤ kappa d (ε / 2) - kappa d ε := by
  obtain ⟨K, hK, hbound⟩ := kappa_asymptotic hd
  let A : ℝ := (d : ℝ) *
    (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1))
  have hA : 0 < A := by
    dsimp only [A]
    rw [← Euclidean.Shell.unitBallVolume_eq_pi_div_gamma]
    exact mul_pos (Nat.cast_pos.mpr (by omega)) (Euclidean.Shell.unitBallVolume_pos d)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := A * Real.log 2 / 2
  have hc : 0 < c := div_pos (mul_pos hA hlog2) (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro δ hδ
  by_contra hnot
  have hinc : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) (min δ 1) →
      kappa d (ε / 2) < kappa d ε + c := by
    intro ε hε
    have hn : ¬ c ≤ kappa d (ε / 2) - kappa d ε := by
      intro h
      exact hnot ⟨ε, hε, h⟩
    linarith [lt_of_not_ge hn]
  let t := min δ 1 / 2
  have ht : 0 < t := div_pos (lt_min hδ zero_lt_one) (by norm_num)
  have htδ : t < min δ 1 := by dsimp only [t]; linarith [lt_min hδ zero_lt_one]
  have ht1 : t ≤ 1 / 2 := by
    dsimp only [t]
    linarith [min_le_right δ (1 : ℝ)]
  let e : ℕ → ℝ := fun n => t / 2 ^ n
  have he (n : ℕ) : e n ∈ Set.Ioo (0 : ℝ) (min δ 1) := by
    have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    exact ⟨div_pos ht (pow_pos (by norm_num) n),
      (div_le_self ht.le hp).trans_lt htδ⟩
  have hehalf (n : ℕ) : e (n + 1) = e n / 2 := by
    dsimp only [e]
    rw [pow_succ, div_mul_eq_div_div]
  have hupper (n : ℕ) : kappa d (e n) ≤ kappa d t + n * c := by
    induction n with
    | zero => simp only [e, pow_zero, div_one, Nat.cast_zero, zero_mul, add_zero, le_refl]
    | succ n ih =>
      rw [hehalf]
      have hi := hinc (e n) (he n)
      push_cast
      nlinarith only [hi, ih]
  have hlog (n : ℕ) : |Real.log (e n)| = -Real.log t + n * Real.log 2 := by
    rw [abs_of_neg (Real.log_neg (he n).1 ((he n).2.trans_le (min_le_right _ _)))]
    dsimp only [e]
    rw [Real.log_div ht.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
    ring
  have hlinear (n : ℕ) : (n : ℝ) * c ≤ kappa d t + A * Real.log t + K := by
    have hen : e n ≤ 1 / 2 :=
      (div_le_self ht.le (one_le_pow₀ (by norm_num))).trans ht1
    have hl := (abs_le.mp (hbound (e n) ⟨(he n).1, hen⟩)).1
    change -K ≤ kappa d (e n) - A * |Real.log (e n)| at hl
    rw [hlog] at hl
    have hu := hupper n
    dsimp only [c] at *
    nlinarith only [hl, hu]
  obtain ⟨n, hn⟩ := exists_nat_gt ((kappa d t + A * Real.log t + K) / c)
  have hn' := (div_lt_iff₀ hc).mp hn
  have hle := hlinear n
  nlinarith only [hn', hle]

end

end LongRange.Scaling
