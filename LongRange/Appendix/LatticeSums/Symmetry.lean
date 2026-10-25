import LongRange.Model.Kernel

/-!
# Finite symmetries of the critical lattice moments

Coordinate exchanges equate the diagonal moments of the critical jump kernel, and coordinate
reflection cancels the mixed moments. All sums use integer indices of the physical Euclidean ball.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

namespace LatticeSums

/-- Exchanging two coordinates of an integer index preserves its physical Euclidean radius. -/
lemma radius_swap {d : ℕ} (ε : ℝ) (i j : Fin d) (q : Site d) :
    radius (physical ε (q ∘ Equiv.swap i j)) = radius (physical ε q) := by
  unfold radius physical
  congr 1
  exact Equiv.sum_comp (Equiv.swap i j) (fun k => (ε * (q k : ℝ)) ^ 2)

/-- Exchanging coordinates preserves the nonzero integer indices in the physical unit ball. -/
lemma swap_mem {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i j : Fin d) (q : Site d) :
    q ∘ Equiv.swap i j ∈ unitBallIndices d ε ↔ q ∈ unitBallIndices d ε := by
  have hz : q ∘ Equiv.swap i j = 0 ↔ q = 0 := by
    constructor
    · intro h
      funext k
      have := congrFun h (Equiv.swap i j k)
      simpa only [Function.comp_apply, Equiv.swap_apply_self, Pi.zero_apply] using this
    · intro h
      simp only [h, Pi.zero_comp]
  rw [mem_unitBallIndices hε, mem_unitBallIndices hε, radius_swap]
  simp only [ne_eq, hz]

/-- Coordinate exchange leaves the critical jump kernel invariant at physical points. -/
lemma kernel_swap {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i j : Fin d) (q : Site d) :
    jumpKernel (physical ε (q ∘ Equiv.swap i j)) = jumpKernel (physical ε q) := by
  have hz : q ∘ Equiv.swap i j = 0 ↔ q = 0 := by
    constructor
    · intro h
      funext k
      have := congrFun h (Equiv.swap i j k)
      simpa only [Function.comp_apply, Equiv.swap_apply_self, Pi.zero_apply] using this
    · intro h
      simp only [h, Pi.zero_comp]
  simp only [jumpKernel, physical_eq_zero_iff hε, radius_swap, hz]

/-- The finite diagonal moments are equal by coordinate exchange. -/
lemma diagonal_sum_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i j : Fin d) :
    ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i ^ 2 =
      ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q j ^ 2 := by
  have hs : ∀ F : Site d → ℝ,
      ∑ q ∈ unitBallIndices d ε, F (q ∘ Equiv.swap i j) =
        ∑ q ∈ unitBallIndices d ε, F q := by
    intro F
    refine Finset.sum_nbij' (fun q => q ∘ Equiv.swap i j)
      (fun q => q ∘ Equiv.swap i j) ?_ ?_ ?_ ?_ ?_
    · exact fun q hq => (swap_mem hε i j q).mpr hq
    · exact fun q hq => (swap_mem hε i j q).mpr hq
    · intro q _
      ext k
      simp only [Function.comp_apply, Equiv.swap_apply_self]
    · intro q _
      ext k
      simp only [Function.comp_apply, Equiv.swap_apply_self]
    · intro q _
      rfl
  rw [← hs (fun q => jumpKernel (physical ε q) * physical ε q i ^ 2)]
  apply Finset.sum_congr rfl
  intro q _
  rw [kernel_swap hε]
  simp only [physical, Function.comp_apply, Equiv.swap_apply_left]

/-- Summing all equal diagonal moments gives the radial second moment. -/
lemma radial_sum_eq {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * radius (physical ε q) ^ 2 =
      (d : ℝ) * ∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * physical ε q i ^ 2 := by
  have hs : ∑ q ∈ unitBallIndices d ε,
      jumpKernel (physical ε q) * radius (physical ε q) ^ 2 =
        ∑ k, ∑ q ∈ unitBallIndices d ε,
          jumpKernel (physical ε q) * physical ε q k ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [radius_sq, Finset.mul_sum]
  rw [hs, Finset.sum_congr rfl (fun k _ => diagonal_sum_eq hε k i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The normalized diagonal moment is one dimensionth of the normalized radial moment. -/
lemma diagonal_identity {d : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    ε ^ d / |Real.log ε| *
        ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * physical ε q i ^ 2 =
      ε ^ d / (d * |Real.log ε|) *
        ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * radius (physical ε q) ^ 2 := by
  rw [radial_sum_eq hε i]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos i).ne'
  by_cases hL : |Real.log ε| = 0
  · simp only [hL, mul_zero, div_zero, zero_mul]
  · field_simp

/-- Reflecting coordinate `i` cancels each mixed moment with a distinct coordinate `j`. -/
lemma mixed_sum_eq_zero {d : ℕ} {ε : ℝ} (hε : 0 < ε) {i j : Fin d} (hij : i ≠ j) :
    ∑ q ∈ unitBallIndices d ε,
      jumpKernel (physical ε q) * physical ε q i * physical ε q j = 0 := by
  have hs : ∀ F : Site d → ℝ,
      ∑ q ∈ unitBallIndices d ε, F (reflect i q) =
        ∑ q ∈ unitBallIndices d ε, F q := by
    intro F
    refine Finset.sum_nbij' (reflect i) (reflect i) ?_ ?_ ?_ ?_ ?_
    · exact fun q hq => (reflect_mem_unitBallIndices hε i q).mpr hq
    · exact fun q hq => (reflect_mem_unitBallIndices hε i q).mpr hq
    · exact fun q _ => reflect_involutive i q
    · exact fun q _ => reflect_involutive i q
    · intro q _
      rfl
  have hk (q : Site d) : jumpKernel (physical ε (reflect i q)) =
      jumpKernel (physical ε q) := by
    have hz := not_congr (reflect_ne_zero i q)
    simp only [not_not] at hz
    simp only [jumpKernel, physical_eq_zero_iff hε, radius_reflect, hz]
  have he := hs (fun q => jumpKernel (physical ε q) * physical ε q i * physical ε q j)
  have hn : ∑ q ∈ unitBallIndices d ε,
      jumpKernel (physical ε (reflect i q)) * physical ε (reflect i q) i *
        physical ε (reflect i q) j =
      -∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * physical ε q i * physical ε q j := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [hk]
    simp only [physical, reflect, ite_true, if_neg hij.symm, Int.cast_neg]
    ring
  linarith

end LatticeSums
end
end LongRange
