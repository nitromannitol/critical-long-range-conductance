import LongRangeAudit.QuenchedInvariance.Vocabulary.EuclideanLattice

/-! # Independent EuclideanCube vocabulary. -/

open scoped BigOperators ENNReal NNReal Topology

namespace LongRangeAudit.QuenchedInvariance

/-!
# Half-open unit cubes centered at integer points

The cube `cube w` of an integer point `w` is the half-open unit cube centered at `w`.  The
module proves that these cubes have volume one and are pairwise disjoint, and it compares the
critical radial power `|x|^{-d}` on a cube with its value at the center, with an explicit
constant.  No hypothesis is assumed beyond those stated on each declaration.
-/

noncomputable section

open scoped BigOperators
open LatticeProb.Euclidean.Lattice MeasureTheory Set

namespace LatticeProb.Euclidean.Cube

/-- The half-open unit cube centered at the integer point `w`. -/
def cube {d : ℕ} (w : Site d) : Set (Fin d → ℝ) :=
  {x | ∀ k, (w k : ℝ) - 1/2 ≤ x k ∧ x k < (w k : ℝ) + 1/2}

/-- The unit cube is the product of its half-open coordinate intervals. -/
lemma cube_eq_pi {d : ℕ} (w : Site d) :
    cube w = Set.pi Set.univ (fun k => Set.Ico ((w k : ℝ)-1/2) ((w k : ℝ)+1/2)) := by
  ext x
  simp only [cube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_const]

/-- A unit cube is measurable. -/
lemma cube_measurable {d : ℕ} (w : Site d) : MeasurableSet (cube w) := by
  rw [cube_eq_pi]
  exact MeasurableSet.pi (Set.countable_univ) (fun _ _ => measurableSet_Ico)

/-- A unit cube has Lebesgue volume one. -/
lemma cube_volume {d : ℕ} (w : Site d) : volume (cube w) = 1 := by
  rw [cube_eq_pi, Real.volume_pi_Ico]
  simp only [show ∀ k : Fin d, (w k : ℝ)+1/2 - ((w k : ℝ)-1/2) = 1 by intro k; ring,
    ENNReal.ofReal_one, Finset.prod_const_one]

/-- Distinct integer points have disjoint unit cubes. -/
lemma cubes_disjoint {d : ℕ} {w z : Site d} (hwz : w ≠ z) :
    Disjoint (cube w) (cube z) := by
  rw [Set.disjoint_left]
  intro x hx hz
  apply hwz
  funext k
  have h1 : ((w k : ℝ) - z k) < 1 := by linarith [(hx k).1, (hz k).2]
  have h2 : (-1:ℝ) < (w k : ℝ) - z k := by linarith [(hx k).2, (hz k).1]
  have h1' : w k - z k < 1 := by exact_mod_cast h1
  have h2' : -1 < w k - z k := by exact_mod_cast h2
  omega

/-- The constant `(d √d / 2) (4/3)^(d+1)` of the cube-to-center comparison. -/
def comparisonConstant (d : ℕ) : ℝ :=
  ((d : ℝ) * Real.sqrt d / 2) * (4/3 : ℝ) ^ (d+1)

/-- The constant of the disjoint-cube comparison is nonnegative. -/
lemma comparisonConstant_nonneg (d : ℕ) : 0 ≤ comparisonConstant d := by
  unfold comparisonConstant
  positivity

/-- For `c - 1/2 ≤ x < c + 1/2`, the square `(x - c)²` is at most `1/4`. -/
lemma sq_sub_le_quarter {x c : ℝ} (h1 : c - 1 / 2 ≤ x) (h2 : x < c + 1 / 2) :
    (x - c) ^ 2 ≤ 1 / 4 := by
  calc (x - c) ^ 2 ≤ (1 / 2) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    _ = 1 / 4 := by norm_num

/-- A nonnegative `r` with `r ^ 2 ≤ s ^ 2 / 4` satisfies `r ≤ s / 2`, for `s ≥ 0`. -/
lemma le_half_of_sq_le_quarter {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : r ^ 2 ≤ s ^ 2 / 4) : r ≤ s / 2 := by
  refine (sq_le_sq₀ hr (div_nonneg hs (by norm_num))).mp ?_
  calc r ^ 2 ≤ s ^ 2 / 4 := h
    _ = (s / 2) ^ 2 := by ring

/-- On the unit cube centered at `w`, the radius differs from the radius of `w` by at most
`√d / 2`. -/
lemma cube_radius_error {d : ℕ} (w : Site d) {x : Fin d → ℝ}
    (hx : x ∈ cube w) :
    |radius x - radius (physical 1 w)| ≤ Real.sqrt d / 2 := by
  apply (radius_difference x (physical 1 w)).trans
  have hs : ∑ k, (x k - (w k : ℝ))^2 ≤ (d : ℝ) / 4 := by
    calc
      _ ≤ ∑ _k : Fin d, (1/4 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact sq_sub_le_quarter (hx k).1 (hx k).2
      _ = _ := by simp [div_eq_mul_inv]
  have hn := radius_nonneg (x - physical 1 w)
  have he := radius_sq (x - physical 1 w)
  have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
  simp only [Pi.sub_apply, physical, one_mul] at he
  have hsq : radius (x - physical 1 w) ^ 2 ≤ Real.sqrt d ^ 2 / 4 := by
    rw [hd]
    linarith
  exact le_half_of_sq_le_quarter hn (Real.sqrt_nonneg _) hsq

end LatticeProb.Euclidean.Cube

end

end LongRangeAudit.QuenchedInvariance
