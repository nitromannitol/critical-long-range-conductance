import LongRange.Poincare.Shell
import LongRange.Poincare.Translation

/-!
# The single-scale estimate

Fixed-displacement telescoping, summed with the Euclidean kernel weights on a half-slab,
gives the scale-independent estimate. The powers of the physical slab scale cancel against
the kernel mass and the exact lattice cardinality.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- Cancellation of the physical scale in the weighted telescoping bound. -/
theorem scale_coefficient (n : ℕ) (e t D R : ℝ) (he : e ≠ 0) (ht : t ≠ 0) :
    e ^ n * (9 * (R / (e * t)) ^ 2 /
      (t ^ n * ((D * (e * t)) ^ (n + 2))⁻¹)) =
        9 * D ^ (n + 2) * R ^ 2 * e ^ (2 * n) := by
  rw [Nat.mul_comm 2 n, pow_mul]
  simp only [pow_add, mul_pow]
  field_simp [he, ht]

/-- The shell estimate also holds with any larger positive bound for the physical diameter. -/
theorem single_scale_bound (d : ℕ) {R ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin (d + 1) → ℝ)}
    (hU : Bornology.IsBounded U) (hdiam : euclideanDiam U ≤ R)
    (k : ℕ) (hscale : ε * 3 ^ k ≤ R) {h : Site (d + 1) → ℝ}
    (hh : SupportedIn ε U h) :
    l2NormSq ε U h ≤ 9 * (3 * (d + 1 : ℕ)) ^ (d + 3) * R ^ 2 *
      ε ^ (2 * (d + 1)) * ∑' p, shellTerm ε k h p := by
  have he : 0 < ε := hε.1
  let S := forwardBox d k
  let w : Site (d + 1) → ℝ := fun z => jumpKernel (physical ε z)
  let c : ℝ := (3 ^ k : ℝ) ^ (d + 1) *
    ((3 * (d + 1 : ℕ) * (ε * 3 ^ k)) ^ (d + 3))⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  have hweighted := weighted_sq_sum_le (h := h) S w (fun _ _ => jumpKernel_nonneg _)
    (9 * (R / (ε * 3 ^ k)) ^ 2) (fun z hz =>
      sq_sum_le_of_forward_shift_bound hε.1 (by positivity) hU hdiam hscale hh
        0 z (mul_le_mul_of_nonneg_left
          (by exact_mod_cast (mem_forwardBox.mp hz).1) hε.1.le))
  have hmass : c ≤ ∑ z ∈ S, w z := forwardBox_mass_lower d k hε.1
  have henergy := forwardBox_energy_le hε hU hh (k := k)
  have hbound : c * (∑' x, h x ^ 2) ≤
      (9 * (R / (ε * 3 ^ k)) ^ 2) * ∑' p, shellTerm ε k h p := by
    calc
      _ ≤ (∑ z ∈ S, w z) * (∑' x, h x ^ 2) :=
        mul_le_mul_of_nonneg_right hmass (tsum_nonneg (fun _ => sq_nonneg _))
      _ ≤ _ := hweighted.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hnorm : l2NormSq ε U h = ε ^ (d + 1) * ∑' x, h x ^ 2 := by
    unfold l2NormSq
    congr 1
    apply tsum_subtype_eq_of_support_subset (f := fun q : Site (d + 1) => h q ^ 2)
      (s := latticeSet ε U)
    intro x hx
    by_contra hout
    apply hx
    change h x ^ 2 = 0
    rw [hh x hout, zero_pow (by decide : 2 ≠ 0)]
  rw [hnorm]
  calc
    _ ≤ ε ^ (d + 1) *
        ((9 * (R / (ε * 3 ^ k)) ^ 2) * (∑' p, shellTerm ε k h p) / c) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hc).mpr
        (by simpa only [mul_comm] using hbound)) (pow_nonneg hε.1.le _)
    _ = (ε ^ (d + 1) * (9 * (R / (ε * 3 ^ k)) ^ 2 / c)) *
        (∑' p, shellTerm ε k h p) := by ring
    _ = _ := by
      dsimp only [c]
      rw [scale_coefficient (d + 1) ε (3 ^ k) (3 * (d + 1 : ℕ)) R
        hε.1.ne' (pow_ne_zero _ (by norm_num))]


end

end LongRange.Poincare

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice Poincare

/-- Lemma 4.2: each triadic shell controls the supported discrete square norm uniformly. -/
theorem single_scale_estimate (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Fin d → ℝ), IsOpen U → Bornology.IsBounded U →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ k : ℕ, ε * 3 ^ k ≤ euclideanDiam U →
      ∀ h : Site d → ℝ, SupportedIn ε U h →
        l2NormSq ε U h ≤ C * euclideanDiam U ^ 2 * ε ^ (2 * d) *
          ∑' x : Site d × Site d,
            if ε * 3 ^ k ≤ ‖physical ε x.2‖ ∧ ‖physical ε x.2‖ < ε * 3 ^ (k + 1) then
              jumpKernel (physical ε x.2) * (h (x.1 + x.2) - h x.1) ^ 2
            else 0 := by
  cases d with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro U _ _ ε hε k hscale h hh
    have hdiam : euclideanDiam U = 0 := by
      apply le_antisymm _ (euclideanDiam_nonneg U)
      exact le_of_eq (Metric.diam_subsingleton Set.subsingleton_of_subsingleton)
    rw [hdiam] at hscale
    exact False.elim ((not_le_of_gt (mul_pos hε.1 (pow_pos (by norm_num) k))) hscale)
  | succ d =>
    refine ⟨9 * (3 * (d + 1 : ℕ)) ^ (d + 3), by positivity, ?_⟩
    intro U _ hU ε hε k hscale h hh
    exact single_scale_bound d hε hU le_rfl k hscale hh

end LongRange
