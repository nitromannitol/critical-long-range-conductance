import LongRangeHeat.Defs
import LongRange.Appendix.Kappa

/-!
# The second moment of the short jumps and the lattice sums of the kernel

* `second_moment_eq`: the identity (2.3), `ε^d ∑_{0 < |z| ≤ 1} J(z) z_i z_j = (κ_ε / d) δ_{ij}`.
* `two_mul_le_kappa`, `exists_mul_abs_log_le_kappa`: `κ_ε ≥ 2d` and `κ_ε ≥ c |ln ε|`.
* `exists_short_sum_le`, `exists_long_sum_le`: the sums `ε^d ∑_{0 < |z| ≤ 1} |z|^{1-d}` and
  `ε^d ∑_{|z| > 1} |z|^{-d-2}` are bounded by a constant `C(d)`.
* `sum_first_moment_eq_zero`: the first moments of the short jumps vanish, since the set of short
  jumps is symmetric under `z ↦ -z`.

The sums over `z ∈ εℤ^d` with `0 < |z| ≤ 1` are written over the finite set
`unitBallIndices d ε` of integer sites `q` with `z = εq`.
-/

namespace LongRangeHeat

open LongRange LatticeProb LatticeProb.Euclidean.Lattice Set

noncomputable section

variable {d : ℕ}

theorem physical_add (ε : ℝ) (q w : Site d) :
    physical ε (q + w) = physical ε q + physical ε w := by
  funext k
  simp [physical, mul_add]

theorem physical_neg (ε : ℝ) (w : Site d) : physical ε (-w) = -physical ε w := by
  funext k
  simp [physical]

theorem radius_neg (v : Fin d → ℝ) : radius (-v) = radius v := by
  simp [radius]

theorem jumpKernel_neg (v : Fin d → ℝ) : jumpKernel (-v) = jumpKernel v := by
  simp [jumpKernel, radius_neg]

theorem neg_mem_unitBallIndices {ε : ℝ} (hε : 0 < ε) (w : Site d) :
    -w ∈ unitBallIndices d ε ↔ w ∈ unitBallIndices d ε := by
  rw [mem_unitBallIndices hε, mem_unitBallIndices hε, physical_neg, radius_neg, neg_ne_zero]

/-- **(2.3)** The second moments of the short jumps:
`ε^d ∑_{0 < |z| ≤ 1} J(z) z_i z_j = (κ_ε / d) δ_{ij}`. -/
theorem second_moment_eq (hd : 1 ≤ d) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (i j : Fin d) :
    ε ^ d * ∑ q ∈ unitBallIndices d ε,
        jumpKernel (physical ε q) * physical ε q i * physical ε q j =
      kappa d ε / d * if i = j then 1 else 0 := by
  have hκ := kappa_pos hd hε
  have h := second_moment_normalized hd hε i j
  rw [div_mul_eq_mul_div, div_eq_iff hκ.ne'] at h
  rw [h]
  split_ifs <;> ring

/-- The `2d` nearest-neighbor jumps `±ε e_i` contribute `2d` to `κ_ε`. -/
theorem two_mul_le_kappa {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : 2 * (d : ℝ) ≤ kappa d ε := by
  classical
  set e : Fin d × Bool → Site d := fun p => Pi.single p.1 (if p.2 then 1 else -1) with he_def
  have hsign : ∀ b : Bool, (if b then (1 : ℤ) else -1) ≠ 0 := fun b => by cases b <;> simp
  have he : Function.Injective e := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have hi := congrFun h i
    by_cases hij : i = j
    · subst hij
      simp only [he_def, Pi.single_eq_same] at hi
      cases s <;> cases t <;> simp_all
    · simp only [he_def, Pi.single_eq_same, Pi.single_apply, hij, ↓reduceIte] at hi
      exact absurd hi (hsign s)
  have hr : ∀ p, radius (physical ε (e p)) = ε := by
    rintro ⟨i, s⟩
    rw [radius_physical_eq_mul hε.1.le]
    cases s <;> simp [he_def, radius, physical, Pi.single_apply]
  have hne : ∀ p, e p ≠ 0 := by
    rintro ⟨i, s⟩ h
    have hi := congrFun h i
    simp only [he_def, Pi.single_eq_same, Pi.zero_apply] at hi
    exact hsign s hi
  have hmem : Finset.univ.image e ⊆ unitBallIndices d ε := by
    intro w hw
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hw
    rw [mem_unitBallIndices hε.1, hr]
    exact ⟨hne p, hε.2.le⟩
  have hεd : 0 < ε ^ d := pow_pos hε.1 d
  unfold kappa
  calc 2 * (d : ℝ) = ε ^ d * ∑ p : Fin d × Bool, (radius (physical ε (e p)) ^ d)⁻¹ := by
        simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        field_simp
        push_cast
        ring
    _ = ε ^ d * ∑ q ∈ Finset.univ.image e, (radius (physical ε q) ^ d)⁻¹ := by
        rw [Finset.sum_image fun p _ p' _ h => he h]
    _ ≤ ε ^ d * ∑ q ∈ unitBallIndices d ε, (radius (physical ε q) ^ d)⁻¹ := by
        gcongr
        intro q _ _
        have := radius_nonneg (physical ε q)
        positivity

/-- `κ_ε ≥ c |ln ε|` on `(0, 1/2)`. -/
theorem exists_mul_abs_log_le_kappa (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε ∈ Ioo (0 : ℝ) (1 / 2), c * |Real.log ε| ≤ kappa d ε := by
  obtain ⟨c, hc, h⟩ := le_kappa hd
  refine ⟨c, hc, fun ε hε => le_trans ?_ (h ε ⟨hε.1, by linarith [hε.2]⟩)⟩
  linarith

/-- The short jumps: `ε^d ∑_{0 < |z| ≤ 1} |z|^{1-d} ≤ C(d)`. -/
theorem exists_short_sum_le (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2),
      ε ^ d * ∑ q ∈ unitBallIndices d ε, 1 / radius (physical ε q) ^ (d - 1) ≤ C := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, -, h⟩ := LatticeSums.radial_bounds d ((d : ℝ) - 1) (by linarith)
  refine ⟨C, fun ε hε => ?_⟩
  have h1 := (h ε ⟨hε.1, by linarith [hε.2]⟩).1
  simp only [show (d : ℝ) - 1 < d by linarith, ↓reduceIte] at h1
  refine le_trans (le_of_eq ?_) h1
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one]

/-- The long jumps: `ε^d ∑_{|z| > 1} |z|^{-d-2} ≤ C(d)`, and the series converges. -/
theorem exists_long_sum_le (d : ℕ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) (1 / 2),
      Summable (fun q : Site d =>
        if 1 < radius (physical ε q) then 1 / radius (physical ε q) ^ (d + 2) else 0) ∧
      ε ^ d * ∑' q : Site d,
        (if 1 < radius (physical ε q) then 1 / radius (physical ε q) ^ (d + 2) else 0) ≤ C := by
  obtain ⟨C, -, h⟩ := LatticeSums.radial_bounds d ((d : ℝ) + 2) (by positivity)
  refine ⟨C, fun ε hε => ?_⟩
  obtain ⟨hs, hle⟩ := (h ε ⟨hε.1, by linarith [hε.2]⟩).2 (by linarith)
  have hcast : ∀ r : ℝ, r ^ ((d : ℝ) + 2) = r ^ (d + 2) := fun r => by
    rw [show ((d : ℝ) + 2) = ((d + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp only [hcast] at hs hle
  have hnn : ∀ q : Site d, 0 ≤
      if 1 < radius (physical ε q) then 1 / radius (physical ε q) ^ (d + 2) else 0 := by
    intro q
    split_ifs
    · have := radius_nonneg (physical ε q)
      positivity
    · exact le_rfl
  have hle' : ∀ q : Site d,
      (if 1 < radius (physical ε q) then 1 / radius (physical ε q) ^ (d + 2) else 0) ≤
        if 1 ≤ radius (physical ε q) then 1 / radius (physical ε q) ^ (d + 2) else 0 := by
    intro q
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.le h2
    · have := radius_nonneg (physical ε q)
      positivity
    · exact le_rfl
  have hs' := Summable.of_nonneg_of_le hnn hle' hs
  exact ⟨hs', le_trans (mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hle' hs' hs)
    (pow_pos hε.1 d).le) hle⟩

/-- The first moments of the short jumps vanish: `∑_{0 < |z| ≤ 1} J(z) ℓ(z) = 0` for every
linear functional `ℓ`. -/
theorem sum_first_moment_eq_zero {ε : ℝ} (hε : 0 < ε) (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) :
    ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * ℓ (physical ε q) = 0 := by
  have h : ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε q) * ℓ (physical ε q) =
      ∑ q ∈ unitBallIndices d ε, jumpKernel (physical ε (-q)) * ℓ (physical ε (-q)) :=
    Finset.sum_equiv (Equiv.neg (Site d)) (fun q => (neg_mem_unitBallIndices hε q).symm)
      fun q _ => by simp
  simp only [physical_neg, jumpKernel_neg, map_neg, mul_neg, Finset.sum_neg_distrib] at h
  linarith

end

end LongRangeHeat
