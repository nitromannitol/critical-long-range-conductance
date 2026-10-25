import LongRange.Preliminaries.PathCounting.Integer

/-!
# Rescaling the coordinate-path count

Positive physical scaling identifies the qualifying integer endpoint pairs with the
qualifying physical endpoint pairs. The physical ℓ¹ displacement divided by the scale
is the integer ℓ¹ displacement.
-/

namespace LongRange

open LatticeProb LatticeProb.Euclidean.Lattice

variable {d : ℕ}

/-- Rescaling integer endpoint pairs transports both edge usage and the counting bound. -/
lemma scaled_path_counting (ε : ℝ) (hε : 0 < ε) (q : Site d) (a : Sym2 (Site d)) :
    {p : (Fin d → ℝ) × (Fin d → ℝ) |
      p.2 - p.1 = physical ε q ∧ ∃ u v : Site d,
        p.1 = physical ε u ∧ p.2 = physical ε v ∧
          Sym2.map (physical ε) a ∈ pathEdges (scaledCoordPath ε v u)}.Finite ∧
    (Nat.card {p : (Fin d → ℝ) × (Fin d → ℝ) |
      p.2 - p.1 = physical ε q ∧ ∃ u v : Site d,
        p.1 = physical ε u ∧ p.2 = physical ε v ∧
          Sym2.map (physical ε) a ∈ pathEdges (scaledCoordPath ε v u)} : ℝ) ≤
      (∑ i, |physical ε q i|) / ε := by
  classical
  let S := {p : Site d × Site d | p.2 - p.1 = q ∧
    a ∈ pathEdges (coordPath p.2 p.1)}
  let F : Site d × Site d → (Fin d → ℝ) × (Fin d → ℝ) :=
    fun p => (physical ε p.1, physical ε p.2)
  have hsub (v u : Site d) : physical ε (v - u) = physical ε v - physical ε u := by
    funext i
    simp only [physical, Pi.sub_apply, Int.cast_sub, mul_sub]
  have heq : {p : (Fin d → ℝ) × (Fin d → ℝ) |
      p.2 - p.1 = physical ε q ∧ ∃ u v : Site d,
        p.1 = physical ε u ∧ p.2 = physical ε v ∧
          Sym2.map (physical ε) a ∈ pathEdges (scaledCoordPath ε v u)} = F '' S := by
    ext p
    constructor
    · rintro ⟨hz, u, v, hu, hv, he⟩
      have hq : v - u = q := physical_injective hε
        ((hsub v u).trans (by simpa only [hu, hv] using hz))
      have ha : a ∈ pathEdges (coordPath v u) := by
        rw [scaledCoordPath, pathEdges_map, List.mem_map] at he
        obtain ⟨b, hb, hba⟩ := he
        exact (Sym2.map.injective (physical_injective hε) hba) ▸ hb
      exact ⟨(u, v), ⟨hq, ha⟩, Prod.ext hu.symm hv.symm⟩
    · rintro ⟨⟨u, v⟩, ⟨hq, ha⟩, rfl⟩
      refine ⟨?_, u, v, rfl, rfl, ?_⟩
      · exact (hsub v u).symm.trans (congrArg (physical ε) hq)
      · rw [scaledCoordPath, pathEdges_map]
        exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hinj : Function.Injective F := by
    intro p r h
    exact Prod.ext (physical_injective hε (congrArg Prod.fst h))
      (physical_injective hε (congrArg Prod.snd h))
  obtain ⟨hfin, hcard⟩ := integer_path_counting q a
  rw [heq]
  refine ⟨hfin.image F, ?_⟩
  rw [Nat.card_image_of_injective hinj]
  have hl1 : (∑ i, |physical ε q i|) = ε * (∑ i, (q i).natAbs : ℕ) := by
    simp only [physical, abs_mul, abs_of_pos hε, Nat.cast_sum,
      Nat.cast_natAbs, Int.cast_abs, Finset.mul_sum]
  rw [hl1, mul_div_cancel_left₀ _ hε.ne']
  exact_mod_cast hcard

end LongRange
