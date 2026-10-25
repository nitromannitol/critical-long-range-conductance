import LongRange.Poincare.Assembly

/-!
# Poincaré inequality for the critical Euclidean kernel

The single-scale argument with diameter bound `max R 1` applies at every scale below size
one. Summing those disjoint shells supplies the logarithmic factor in `κ`, uniformly for all
bounded open domains of diameter at most `R`, including domains smaller than the spacing.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice Poincare

noncomputable section

/-- Proposition 4.1: the normalized critical energy controls the supported square norm. -/
theorem poincare (d : ℕ) (hd : 1 ≤ d) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Fin d → ℝ), IsOpen U → Bornology.IsBounded U →
      euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ h : Site d → ℝ, SupportedIn ε U h → l2NormSq ε U h ≤ C * h1CritSq ε h := by
  cases d with
  | zero => omega
  | succ d =>
    obtain ⟨K, hK, hkappa⟩ := kappa_le (d + 1)
    let B : ℝ := max R 1
    let A : ℝ := 9 * (3 * (d + 1 : ℕ)) ^ (d + 3) * B ^ 2
    have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hA : 0 < A := by dsimp only [A]; positivity
    have hlog : 0 < 1 + Real.log 3 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
      linarith
    refine ⟨A * K * (1 + Real.log 3), mul_pos (mul_pos hA hK) hlog, ?_⟩
    intro U _ hU hdiam ε hε h hh
    obtain ⟨m, hm, hscale, hcount⟩ := exists_shell_count hε
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hsingle (k : ℕ) (hk : k ∈ Finset.range m) :
        l2NormSq ε U h ≤ A * ε ^ (2 * (d + 1)) * ∑' p, shellTerm ε k h p :=
      single_scale_bound d hε hU (hdiam.trans (le_max_left _ _)) k
        ((hscale k (Finset.mem_range.mp hk)).trans (le_max_right _ _)) hh
    have hsum := Finset.sum_le_sum hsingle
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have he := sum_shell_energy_le (by omega : 1 ≤ d + 1) hε hU hh m
    have hnorm : 0 ≤ h1CritSq ε h := by
      unfold h1CritSq
      exact mul_nonneg (div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le)
        (tsum_nonneg (fun _ => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))
    have henergy : ε ^ (2 * (d + 1)) *
        (∑' p : Site (d + 1) × Site (d + 1), jumpKernel (physical ε p.2) *
          (h (p.1 + p.2) - h p.1) ^ 2) = kappa (d + 1) ε * h1CritSq ε h := by
      unfold h1CritSq
      field_simp [(kappa_pos hd hε).ne']
    have ht : (m : ℝ) * l2NormSq ε U h ≤ A * kappa (d + 1) ε * h1CritSq ε h := by
      calc
        _ ≤ A * ε ^ (2 * (d + 1)) * ∑ k ∈ Finset.range m, ∑' p, shellTerm ε k h p := by
          exact hsum
        _ ≤ A * ε ^ (2 * (d + 1)) *
            ∑' p : Site (d + 1) × Site (d + 1), jumpKernel (physical ε p.2) *
              (h (p.1 + p.2) - h p.1) ^ 2 :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hA.le (pow_nonneg hε.1.le _))
        _ = _ := by rw [mul_assoc, henergy, ← mul_assoc]
    have hk : kappa (d + 1) ε ≤ K * (1 + Real.log 3) * m := by
      calc
        _ ≤ K * (1 + |Real.log ε|) := hkappa ε hε
        _ ≤ K * ((1 + Real.log 3) * m) := mul_le_mul_of_nonneg_left hcount hK.le
        _ = _ := by ring
    refine le_of_mul_le_mul_left (a := (m : ℝ)) ?_ hmpos
    calc
      _ ≤ A * kappa (d + 1) ε * h1CritSq ε h := ht
      _ ≤ A * (K * (1 + Real.log 3) * m) * h1CritSq ε h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hA.le) hnorm
      _ = _ := by ring

end

end LongRange
