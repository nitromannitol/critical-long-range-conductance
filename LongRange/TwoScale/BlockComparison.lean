import LongRange.TwoScale.Blocks
import LongRange.TwoScale.Scaling
import LongRange.Corrector.MonotonicityLemma

/-!
# Corrector comparison on a logarithmic block

Domain monotonicity and microscopic rescaling compare every corrector on the domain
with the representative corrector on an enlarged cube. The representative physical
cube is independent of the block index.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice TwoScale

variable {d : ℕ}

/-- The representative scale cancels the block index in the enlarged physical cube. -/
theorem cube_representative_eq (w : ℝ) (m L : ℕ) :
    cube (d := d) (w / 3 ^ m) (m + L) = cube w L := by
  have hside : w / (3 : ℝ) ^ m * 3 ^ (m + L) = w * 3 ^ L := by
    rw [pow_add]
    field_simp
  simp only [cube, hside]

/-- Correctors on a bounded open domain are controlled uniformly within each block
by the representative corrector on its enlarged cube. -/
theorem block_corrector_comparison (hd : 1 ≤ d) {U : Set (Fin d → ℝ)} (hUo : IsOpen U)
    (hU : Bornology.IsBounded U) (hne : U.Nonempty) (lam : ℝ) (hlam : 0 < lam) :
    ∃ (A : ℝ) (L : ℕ), 0 < A ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
      ∀ a : Edge d → ℝ, (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) →
      ∀ (p : Fin d → ℝ) (φ Φ : Site d → ℝ),
      IsCorrectorSolution ε U a p φ →
      IsCorrectorSolution (cubeSide U / 3 ^ blockIndex U ε hε.1)
        (cube (cubeSide U / 3 ^ blockIndex U ε hε.1)
          (blockIndex U ε hε.1 + L)) a p Φ →
      h1CritSq ε φ + l2NormSq ε U φ ≤
        A * (h1CritSq (cubeSide U / 3 ^ blockIndex U ε hε.1) Φ +
          l2NormSq (cubeSide U / 3 ^ blockIndex U ε hε.1)
            (cube (cubeSide U / 3 ^ blockIndex U ε hε.1)
              (blockIndex U ε hε.1 + L)) Φ) := by
  have hw := (cubeSide_pos_and_fits hd hU hUo hne).1
  obtain ⟨L, _, hcontain⟩ := exists_enlarged_cube hU hw
  have hupper : cubeSide U ≤ blockUpper U := by
    exact (by linarith : cubeSide U ≤ 3 * cubeSide U).trans (le_max_right _ _)
  have hratio : 1 ≤ blockUpper U / cubeSide U :=
    (le_div_iff₀ hw).mpr (by simpa only [one_mul] using hupper)
  obtain ⟨B, hB, hmono⟩ := corrector_monotonicity d hd lam (euclideanDiam U) hlam
  obtain ⟨D, hD, hscale⟩ := corrector_cube_norms_comparable hd hratio
  refine ⟨B * D, L, mul_pos hB hD, ?_⟩
  intro ε hε a ha p φ Φ hφ hΦ
  let m := blockIndex U ε hε.1
  obtain ⟨hrep, hindex⟩ := representative_mem_block hw hε
  have hUV : U ⊆ cube ε (m + L) := by
    intro x hx i
    have hi := hcontain ε hε.1 hx i
    change |x i - 0| < ε * 3 ^ (m + L - 1) / 2 at hi
    rw [sub_zero] at hi
    have hp : (3 : ℝ) ^ (m + L - 1) ≤ 3 ^ (m + L) :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact hi.trans_le (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hε.1.le) (by norm_num))
  obtain ⟨Ψ, hΨmin, _⟩ :=
    (corrector_wellDefined hd hε (cube_isBounded ε (m + L)) hlam ha p).1
  have hΨ := (corrector_wellDefined hd hε
    (cube_isBounded ε (m + L)) hlam ha p).2 Ψ |>.mp hΨmin
  have hfirst := (hmono U (cube ε (m + L)) hUo hU (cube_isBounded ε (m + L))
    hUV le_rfl ε hε a ha p φ Ψ hφ hΨ).2
  have hsecond := hscale ε (cubeSide U / 3 ^ m) hε hrep
    (block_scale_ratio hw hε hrep hindex.symm) lam hlam a ha p (m + L)
    Ψ Φ hΨ.1 hΨ.2 hΦ.1 hΦ.2
  exact hfirst.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsecond hB.le)

end LongRange
