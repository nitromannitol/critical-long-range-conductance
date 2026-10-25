import LongRange.Model.Lattice
import LongRange.Model.Geometry

/-!
# Counting physical lattice points in bounded sets

Bounded sets contain finitely many points of a lattice at positive spacing.
A Euclidean diameter bound controls coordinate differences from a chosen lattice point,
so a translated integer box gives a count uniform in the position of the set.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- Physical coordinate differences bounded by `R` place indices in a translated integer box. -/
lemma latticeSet_subset_box {d : ℕ} {ε R : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (q₀ : Site d)
    (hR : ∀ q ∈ latticeSet ε U, ∀ i, |ε * ((q i : ℝ) - q₀ i)| ≤ R) :
    latticeSet ε U ⊆ (Fintype.piFinset (fun i =>
      Finset.Icc (q₀ i - ⌈R / ε⌉) (q₀ i + ⌈R / ε⌉)) : Set (Site d)) := by
  intro q hq
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  have hi := hR q hq i
  rw [abs_mul, abs_of_pos hε] at hi
  have hb : |(q i : ℝ) - q₀ i| ≤ (⌈R / ε⌉ : ℝ) :=
    ((le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hi)).trans (Int.le_ceil _)
  have hb' : |q i - q₀ i| ≤ ⌈R / ε⌉ := by
    exact_mod_cast hb
  rw [Finset.mem_Icc]
  have := abs_le.mp hb'
  omega

/-- A bounded set has finitely many indices at every strictly positive lattice spacing. -/
theorem latticeSet_finite {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) : (latticeSet ε U).Finite := by
  obtain ⟨R, hR⟩ := hU.exists_norm_le
  apply (Finset.finite_toSet (Fintype.piFinset (fun _ : Fin d =>
    Finset.Icc (-⌈R / ε⌉) ⌈R / ε⌉))).subset
  have hcoords : ∀ q ∈ latticeSet ε U, ∀ i : Fin d,
      |ε * ((q i : ℝ) - (0 : Site d) i)| ≤ R := by
    intro q hq i
    have hi := norm_le_pi_norm (physical ε q) i
    have hr := hR (physical ε q) hq
    simpa only [Pi.zero_apply, Int.cast_zero, sub_zero, physical, Real.norm_eq_abs]
      using hi.trans hr
  simpa only [Pi.zero_apply, zero_sub, zero_add] using
    latticeSet_subset_box hε (0 : Site d) hcoords

/-- A fixed Euclidean diameter bounds the count by a dimension-dependent multiple of `ε⁻ᵈ`. -/
theorem ncard_latticeSet_le (d : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U →
      euclideanDiam U ≤ R → ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
        ((latticeSet ε U).ncard : ℝ) ≤ C * ε ^ (-(d : ℝ)) := by
  classical
  refine ⟨(2 * max R 0 + 3) ^ d, pow_pos (by positivity) _, ?_⟩
  intro U hU hdiam ε hε
  by_cases hempty : (latticeSet ε U).Nonempty
  · obtain ⟨q₀, hq₀⟩ := hempty
    have hR0 : 0 ≤ R := (euclideanDiam_nonneg U).trans hdiam
    have hcoords : ∀ q ∈ latticeSet ε U, ∀ i : Fin d,
        |ε * ((q i : ℝ) - q₀ i)| ≤ R := by
      intro q hq i
      have hr := (abs_coord_le_radius (physical ε q - physical ε q₀) i).trans
        ((radius_sub_le_euclideanDiam hU hq hq₀).trans hdiam)
      simpa only [Pi.sub_apply, physical, mul_sub] using hr
    have hsub := latticeSet_subset_box hε.1 q₀ hcoords
    let N : ℤ := ⌈R / ε⌉
    have hN : 0 ≤ N := Int.ceil_nonneg (div_nonneg hR0 hε.1.le)
    have hcard : (Fintype.piFinset (fun i : Fin d =>
        Finset.Icc (q₀ i - N) (q₀ i + N))).card = (2 * N + 1).toNat ^ d := by
      simp only [Fintype.card_piFinset, Int.card_Icc]
      have he (i : Fin d) : q₀ i + N + 1 - (q₀ i - N) = 2 * N + 1 := by ring
      simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hcount : ((latticeSet ε U).ncard : ℝ) ≤ ((2 * N + 1).toNat : ℝ) ^ d := by
      have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, hcard] at hc
      exact_mod_cast hc
    have hcast : ((2 * N + 1).toNat : ℝ) = 2 * (N : ℝ) + 1 := by
      have hn : ((2 * N + 1).toNat : ℤ) = 2 * N + 1 :=
        Int.toNat_of_nonneg (by omega)
      exact_mod_cast hn
    have hbase : 2 * (N : ℝ) + 1 ≤ (2 * max R 0 + 3) / ε := by
      have hceil := Int.ceil_lt_add_one (R / ε)
      change (N : ℝ) < R / ε + 1 at hceil
      rw [max_eq_left hR0, le_div_iff₀ hε.1]
      have hmul := mul_le_mul_of_nonneg_right hceil.le hε.1.le
      rw [add_mul, div_mul_cancel₀ _ hε.1.ne', one_mul] at hmul
      nlinarith only [hmul, hε.2]
    calc
      _ ≤ (2 * (N : ℝ) + 1) ^ d := by simpa only [hcast] using hcount
      _ ≤ ((2 * max R 0 + 3) / ε) ^ d :=
        pow_le_pow_left₀ (by positivity) hbase d
      _ = (2 * max R 0 + 3) ^ d * ε ^ (-(d : ℝ)) := by
        rw [div_pow, Real.rpow_neg hε.1.le, Real.rpow_natCast, div_eq_mul_inv]
  · have he : latticeSet ε U = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    rw [he, Set.ncard_empty, Nat.cast_zero]
    exact mul_nonneg (pow_nonneg (by positivity) d) (Real.rpow_nonneg hε.1.le _)

end
end LongRange
