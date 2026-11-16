import LongRangeHeat.Defs

/-!
# Canonical nearest-neighbor paths and the telescoping identity

For an integer increment `w ≠ 0` (the jump `z = εw`) and a site `x`, the canonical path
`γ_{x,z}` of the heat-kernel version is the nearest-neighbor path from `x` to `x + w` that first
performs `|w_1|` steps in direction `sgn(w_1) e_1`, then `|w_2|` steps in direction
`sgn(w_2) e_2`, and so on until the `d`-th coordinate. The edge `{y, y + e_i}` is represented by
the pair `(y, i)`.

* `prefixPoint w k`: the site with coordinates `w_j` for `j < k` and `0` otherwise; the path
  passes through `x + prefixPoint w k` after its moves in the first `k` directions.
* `pathPoint w i t = prefixPoint w i + t e_i`: the lower endpoint of the edges of `γ_{0,w}` in
  direction `i`, for `t` in `pathRange w i = [min(0, w_i), max(0, w_i))`.
* `pathEdges w`: the edges of `γ_{0,w}`; `canonicalPath x w`: the edges of `γ_{x,w}`, its
  translate by `x`.
* `crossingSet w y i`: the sites `x` with `(y, i) ∈ γ_{x,w}`; it has exactly `|w_i|` elements
  (`card_crossingSet`).
* `telescoping`: the identity (3.2),
  `v(x + z) - v(x) = ε ∑_{(y,i) ∈ γ_{x,z}} sgn(z_i) D_i v(y)`.
-/

namespace LongRangeHeat

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- The site with coordinates `w_j` for `j < k` and `0` for `j ≥ k`. -/
def prefixPoint (w : Site d) (k : ℕ) : Site d :=
  fun j => if (j : ℕ) < k then w j else 0

/-- The lower endpoint `prefixPoint w i + t e_i` of an edge of `γ_{0,w}` in direction `i`. -/
def pathPoint (w : Site d) (i : Fin d) (t : ℤ) : Site d :=
  prefixPoint w i + Pi.single i t

/-- The parameters `t ∈ [min(0, w_i), max(0, w_i))` of the edges of `γ_{0,w}` in direction
`i`. -/
def pathRange (w : Site d) (i : Fin d) : Finset ℤ :=
  Finset.Ico (min 0 (w i)) (max 0 (w i))

/-- The edges `(y, i)` crossed by the canonical path `γ_{0,w}` from `0` to `w`. -/
def pathEdges (w : Site d) : Finset (Site d × Fin d) :=
  Finset.univ.biUnion fun i => (pathRange w i).image fun t => (pathPoint w i t, i)

/-- The edges `(y, i)` crossed by the canonical path `γ_{x,w}` from `x` to `x + w`, the
translate by `x` of `γ_{0,w}`. -/
def canonicalPath (x w : Site d) : Finset (Site d × Fin d) :=
  (pathEdges w).image fun e => (x + e.1, e.2)

/-- The sites `x` whose canonical path `γ_{x,w}` crosses the edge `(y, i)`. -/
def crossingSet (w y : Site d) (i : Fin d) : Finset (Site d) :=
  (pathRange w i).image fun t => y - pathPoint w i t

/-- The empty prefix is the origin. -/
theorem prefixPoint_zero (w : Site d) : prefixPoint w 0 = 0 := by
  ext j
  simp [prefixPoint]

/-- The full prefix is `w` itself. -/
theorem prefixPoint_of_le (w : Site d) {k : ℕ} (hk : d ≤ k) : prefixPoint w k = w := by
  ext j
  simp [prefixPoint, lt_of_lt_of_le j.isLt hk]

/-- The `i`-th coordinate of `pathPoint w i t` is `t`. -/
theorem pathPoint_apply_self (w : Site d) (i : Fin d) (t : ℤ) : pathPoint w i t i = t := by
  simp [pathPoint, prefixPoint]

/-- Consecutive points in direction `i` differ by `e_i`. -/
theorem pathPoint_add_one (w : Site d) (i : Fin d) (t : ℤ) :
    pathPoint w i (t + 1) = pathPoint w i t + Pi.single i 1 := by
  rw [pathPoint, pathPoint, add_assoc, ← Pi.single_add]

/-- The moves in direction `i` start at `prefixPoint w i`. -/
theorem pathPoint_zero (w : Site d) (i : Fin d) : pathPoint w i 0 = prefixPoint w i := by
  simp [pathPoint]

/-- The moves in direction `i` end at `prefixPoint w (i + 1)`. -/
theorem pathPoint_self (w : Site d) (i : Fin d) :
    pathPoint w i (w i) = prefixPoint w (i + 1) := by
  ext j
  simp only [pathPoint, prefixPoint, Pi.add_apply, Pi.single_apply]
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · have hne : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
    simp [h, hne, Nat.lt_succ_of_lt h]
  · have he : j = i := Fin.ext h
    subst he
    simp
  · have hne : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
    simp [hne, not_lt.mpr h.le, show ¬ (j : ℕ) < i + 1 by omega]

/-- Distinct parameters give distinct points. -/
theorem pathPoint_injective (w : Site d) (i : Fin d) : Function.Injective (pathPoint w i) := by
  intro t u h
  have := congrFun h i
  rwa [pathPoint_apply_self, pathPoint_apply_self] at this

/-- The edge `(y, i)` lies on `γ_{x,w}` exactly when `y - x = pathPoint w i t` for some
`t ∈ pathRange w i`. -/
theorem mem_canonicalPath {x w y : Site d} {i : Fin d} :
    (y, i) ∈ canonicalPath x w ↔ ∃ t ∈ pathRange w i, y - x = pathPoint w i t := by
  simp only [canonicalPath, pathEdges, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨p, j, ⟨k, ⟨t, ht, hpt, hjk⟩⟩, hy, hi⟩
    subst hjk hi
    exact ⟨t, ht, by rw [← hy, hpt]; abel⟩
  · rintro ⟨t, ht, hyt⟩
    exact ⟨pathPoint w i t, i, ⟨i, ⟨t, ht, rfl, rfl⟩⟩, by rw [← hyt]; abel, rfl⟩

/-- `x ∈ crossingSet w y i` exactly when the canonical path `γ_{x,w}` crosses `(y, i)`. -/
theorem mem_crossingSet {w y x : Site d} {i : Fin d} :
    x ∈ crossingSet w y i ↔ (y, i) ∈ canonicalPath x w := by
  rw [mem_canonicalPath, crossingSet, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by abel⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, by rw [← h]; abel⟩

/-- `pathRange w i` has `|w_i|` elements. -/
theorem card_pathRange (w : Site d) (i : Fin d) : (pathRange w i).card = (w i).natAbs := by
  rw [pathRange, Int.card_Ico]
  omega

/-- Exactly `|w_i|` translates of the canonical path `γ_{0,w}` cross a given edge `(y, i)`. -/
theorem card_crossingSet (w y : Site d) (i : Fin d) :
    (crossingSet w y i).card = (w i).natAbs := by
  rw [crossingSet, Finset.card_image_of_injective _ fun t u h =>
    pathPoint_injective w i (sub_right_injective h), card_pathRange]

/-- The edges of `γ_{0,w}` in different directions are different. -/
theorem pairwiseDisjoint_pathEdges (w : Site d) :
    ((Finset.univ : Finset (Fin d)) : Set (Fin d)).PairwiseDisjoint
      fun i => (pathRange w i).image fun t => (pathPoint w i t, i) := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro e hi hj
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hj
  exact hij (Prod.mk.inj hu).2.symm

/-- The canonical path `γ_{0,w}` has `|w|_1 = ∑_i |w_i|` edges. -/
theorem card_pathEdges (w : Site d) : (pathEdges w).card = ∑ i, (w i).natAbs := by
  rw [pathEdges, Finset.card_biUnion (pairwiseDisjoint_pathEdges w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.card_image_of_injective _ fun t u h =>
    pathPoint_injective w i (Prod.mk.inj h).1, card_pathRange]

/-- A sum over the edges of `γ_{x,w}`, grouped by direction. -/
theorem sum_canonicalPath {M : Type*} [AddCommMonoid M] (F : Site d × Fin d → M)
    (x w : Site d) :
    ∑ e ∈ canonicalPath x w, F e = ∑ i, ∑ t ∈ pathRange w i, F (x + pathPoint w i t, i) := by
  classical
  have hinj : Set.InjOn (fun e : Site d × Fin d => (x + e.1, e.2)) (pathEdges w) :=
    fun e _ f _ h => Prod.ext (add_left_cancel (Prod.mk.inj h).1) (Prod.mk.inj h).2
  rw [canonicalPath, Finset.sum_image hinj, pathEdges,
    Finset.sum_biUnion (pairwiseDisjoint_pathEdges w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_image fun t _ u _ h => pathPoint_injective w i (Prod.mk.inj h).1]

/-- A sum over the sites `x` with `(y, i) ∈ γ_{x,w}`, indexed by the parameter of the crossed
edge. -/
theorem sum_crossingSet {M : Type*} [AddCommMonoid M] (H : Site d → M) (w y : Site d)
    (i : Fin d) :
    ∑ x ∈ crossingSet w y i, H x = ∑ t ∈ pathRange w i, H (y - pathPoint w i t) :=
  Finset.sum_image fun _ _ _ _ h => pathPoint_injective w i (sub_right_injective h)

/-- Telescoping over an integer interval. -/
theorem sum_Ico_int_sub {M : Type*} [AddCommGroup M] (F : ℤ → M) (m : ℤ) (n : ℕ) :
    ∑ t ∈ Finset.Ico m (m + n), (F (t + 1) - F t) = F (m + n) - F m := by
  have himg : Finset.Ico m (m + n) = (Finset.range n).image fun k : ℕ => m + k := by
    ext t
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(t - m).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [himg, Finset.sum_image fun k _ l _ h => by simpa using h]
  have h := Finset.sum_range_sub (fun k : ℕ => F (m + k)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at h
  exact h

/-- The moves of the canonical path in direction `i` telescope:
`∑_{t ∈ pathRange w i} sgn(w_i) (F(t + 1) - F(t)) = F(w_i) - F(0)`. -/
theorem sum_pathRange_sign_mul {M : Type*} [AddCommGroup M] [Module ℝ M] (F : ℤ → M)
    (w : Site d) (i : Fin d) :
    ∑ t ∈ pathRange w i, (Int.sign (w i) : ℝ) • (F (t + 1) - F t) = F (w i) - F 0 := by
  rcases lt_trichotomy (w i) 0 with h | h | h
  · have hr : pathRange w i = Finset.Ico (w i) (w i + ((w i).natAbs : ℕ)) := by
      rw [pathRange, min_eq_right h.le, max_eq_left h.le]
      congr 1
      omega
    rw [hr, Int.sign_eq_neg_one_of_neg h, ← Finset.smul_sum, sum_Ico_int_sub]
    have : w i + ((w i).natAbs : ℤ) = 0 := by omega
    rw [this]
    simp
  · simp [pathRange, h]
  · have hr : pathRange w i = Finset.Ico (0 : ℤ) (0 + ((w i).natAbs : ℤ)) := by
      rw [pathRange, min_eq_left h.le, max_eq_right h.le]
      congr 1
      omega
    rw [hr, Int.sign_eq_one_of_pos h, ← Finset.smul_sum, sum_Ico_int_sub]
    have : (0 : ℤ) + ((w i).natAbs : ℤ) = w i := by omega
    rw [this]
    simp

/-- The telescoping identity (3.2), grouped by direction: for `ε ≠ 0`,
`v(x + w) - v(x) = ε ∑_i ∑_{t ∈ pathRange w i} sgn(w_i) D_i v(x + pathPoint w i t)`. -/
theorem telescoping_pathRange {ε : ℝ} (hε : ε ≠ 0) (v : Site d → ℝ) (x w : Site d) :
    v (x + w) - v x = ε * ∑ i, ∑ t ∈ pathRange w i,
      (Int.sign (w i) : ℝ) * discreteDeriv ε i v (x + pathPoint w i t) := by
  have hstep : ∀ i : Fin d, ∑ t ∈ pathRange w i,
      (Int.sign (w i) : ℝ) * discreteDeriv ε i v (x + pathPoint w i t) =
      ε⁻¹ * (v (x + prefixPoint w (i + 1)) - v (x + prefixPoint w i)) := by
    intro i
    have h := sum_pathRange_sign_mul (fun t => ε⁻¹ * v (x + pathPoint w i t)) w i
    rw [pathPoint_self, pathPoint_zero, ← mul_sub] at h
    rw [← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [discreteDeriv, smul_eq_mul, pathPoint_add_one, ← add_assoc]
    ring
  simp_rw [hstep]
  rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  have htel := Finset.sum_range_sub (fun k => v (x + prefixPoint w k)) d
  rw [Finset.sum_range (fun k => v (x + prefixPoint w (k + 1)) - v (x + prefixPoint w k))]
    at htel
  rw [htel, prefixPoint_of_le w le_rfl, prefixPoint_zero, add_zero]

/-- The telescoping identity (3.2): for `ε ≠ 0` and every `v : εℤ^d → ℝ`,
`v(x + z) - v(x) = ε ∑_{(y,i) ∈ γ_{x,z}} sgn(z_i) D_i v(y)`. -/
theorem telescoping {ε : ℝ} (hε : ε ≠ 0) (v : Site d → ℝ) (x w : Site d) :
    v (x + w) - v x = ε * ∑ e ∈ canonicalPath x w,
      (Int.sign (w e.2) : ℝ) * discreteDeriv ε e.2 v e.1 := by
  rw [sum_canonicalPath (fun e => (Int.sign (w e.2) : ℝ) * discreteDeriv ε e.2 v e.1)]
  exact telescoping_pathRange hε v x w

end

end LongRangeHeat
