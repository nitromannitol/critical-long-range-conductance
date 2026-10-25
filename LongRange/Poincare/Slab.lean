import LongRange.Poincare.Averaging

/-!
# A rectangular subset of the forward slab

The nonnegative transverse half of the paper's forward slab has exactly `3^(k*d)` points.
It stays inside the printed sup-norm shell, while its kernel is bounded using Euclidean
radius. Using this subset only changes the dimension-dependent constant.
-/

namespace LongRange.Poincare

open LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

/-- The forward interval and nonnegative transverse intervals at triadic scale `k`. -/
def forwardBox (d k : ℕ) : Finset (Site (d + 1)) :=
  Fintype.piFinset (fun i => if i = 0 then
    Finset.Ico ((3 : ℤ) ^ k) (2 * (3 : ℤ) ^ k)
    else Finset.Ico 0 ((3 : ℤ) ^ k))

/-- Membership in the rectangular half-slab is coordinatewise interval membership. -/
theorem mem_forwardBox {d k : ℕ} {z : Site (d + 1)} :
    z ∈ forwardBox d k ↔
      (3 : ℤ) ^ k ≤ z 0 ∧ z 0 < 2 * (3 : ℤ) ^ k ∧
        ∀ i : Fin (d + 1), i ≠ 0 → 0 ≤ z i ∧ z i < (3 : ℤ) ^ k := by
  simp only [forwardBox, Fintype.mem_piFinset]
  constructor
  · intro hz
    refine ⟨?_, ?_, ?_⟩
    · exact (by simpa only [↓reduceIte, Finset.mem_Ico] using hz 0 :
        (3 : ℤ) ^ k ≤ z 0 ∧ z 0 < 2 * (3 : ℤ) ^ k).1
    · exact (by simpa only [↓reduceIte, Finset.mem_Ico] using hz 0 :
        (3 : ℤ) ^ k ≤ z 0 ∧ z 0 < 2 * (3 : ℤ) ^ k).2
    · intro i hi
      simpa only [if_neg hi, Finset.mem_Ico] using hz i
  · rintro ⟨hlo, hhi, ht⟩ i
    by_cases hi : i = 0
    · subst i
      simpa only [↓reduceIte, Finset.mem_Ico] using And.intro hlo hhi
    · simpa only [if_neg hi, Finset.mem_Ico] using ht i hi

/-- The half-slab has exactly one triadic interval of choices per coordinate. -/
theorem card_forwardBox (d k : ℕ) : (forwardBox d k).card = (3 ^ k) ^ (d + 1) := by
  classical
  rw [forwardBox, Fintype.card_piFinset]
  have hc (i : Fin (d + 1)) :
      (if i = 0 then Finset.Ico ((3 : ℤ) ^ k) (2 * (3 : ℤ) ^ k)
      else Finset.Ico 0 ((3 : ℤ) ^ k)).card = 3 ^ k := by
    split <;> rw [Int.card_Ico]
    · rw [show 2 * (3 : ℤ) ^ k - 3 ^ k = 3 ^ k by ring]
      exact_mod_cast (Int.toNat_natCast (3 ^ k))
    · rw [sub_zero]
      exact_mod_cast (Int.toNat_natCast (3 ^ k))
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Every half-slab displacement belongs to the exact sup-norm shell in Lemma 4.2. -/
theorem forwardBox_shell {d k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {z : Site (d + 1)} (hz : z ∈ forwardBox d k) :
    ε * 3 ^ k ≤ ‖physical ε z‖ ∧ ‖physical ε z‖ < ε * 3 ^ (k + 1) := by
  obtain ⟨hlo, hhi, ht⟩ := mem_forwardBox.mp hz
  have ha : (0 : ℝ) < 3 ^ k := pow_pos (by norm_num) _
  have hc (i : Fin (d + 1)) : 0 ≤ (z i : ℝ) ∧ (z i : ℝ) < 2 * 3 ^ k := by
    by_cases hi : i = 0
    · subst i
      exact ⟨ha.le.trans (by exact_mod_cast hlo), by exact_mod_cast hhi⟩
    · have hb := ht i hi
      exact ⟨by exact_mod_cast hb.1,
        (show (z i : ℝ) < 3 ^ k by exact_mod_cast hb.2).trans (by linarith)⟩
  constructor
  · calc
      ε * 3 ^ k ≤ ε * (z 0 : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlo) hε.le
      _ ≤ ‖physical ε z‖ := by
        simpa only [physical, Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hε.le (hc 0).1)] using norm_le_pi_norm (physical ε z) 0
  · rw [pi_norm_lt_iff (mul_pos hε (pow_pos (by norm_num) _))]
    intro i
    rw [physical, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le (hc i).1)]
    calc
      ε * (z i : ℝ) < ε * (2 * 3 ^ k) := mul_lt_mul_of_pos_left (hc i).2 hε
      _ < ε * 3 ^ (k + 1) := by
        apply mul_lt_mul_of_pos_left _ hε
        rw [pow_succ]
        linarith only [ha]

/-- The Euclidean radius of a half-slab point is bounded by a dimension-only multiple. -/
theorem forwardBox_radius_le {d k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {z : Site (d + 1)} (hz : z ∈ forwardBox d k) :
    radius (physical ε z) ≤ 3 * (d + 1 : ℕ) * (ε * 3 ^ k) := by
  have hn := (forwardBox_shell hε hz).2.le
  have ha : 0 ≤ ε * 3 ^ k := by positivity
  have hc (i : Fin (d + 1)) : |physical ε z i| ≤ 3 * (ε * 3 ^ k) := by
    calc
      _ ≤ ‖physical ε z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (physical ε z) i
      _ ≤ _ := by
        calc
          _ ≤ ε * 3 ^ (k + 1) := hn
          _ = _ := by rw [pow_succ]; ring
  have hs : radius (physical ε z) ^ 2 ≤ (d + 1 : ℕ) * (3 * (ε * 3 ^ k)) ^ 2 := by
    rw [radius_sq]
    calc
      _ ≤ ∑ _ : Fin (d + 1), (3 * (ε * 3 ^ k)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hc i)
        simpa only [sq_abs] using hi
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
  have hd : (1 : ℝ) ≤ (d + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le d))
  have hd2 : ((d + 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (3 * (ε * 3 ^ k)))
  apply (sq_le_sq₀ (radius_nonneg _) (by positivity)).mp
  calc
    _ ≤ (d + 1 : ℕ) * (3 * (ε * 3 ^ k)) ^ 2 := hs
    _ ≤ ((d + 1 : ℕ) : ℝ) ^ 2 * (3 * (ε * 3 ^ k)) ^ 2 := hm
    _ = _ := by ring

end

end LongRange.Poincare
