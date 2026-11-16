import LongRangeHeat.Forcing

/-!
# The telescoping identity (3.2) and Proposition 3.2

Statements of the telescoping identity (3.2) along the canonical paths `γ_{x,z}`, of the count
of the translates of `γ_{0,z}` crossing a given edge (which makes the sums (3.3) finite), and of
Proposition 3.2 (`prop:forcing`) of the heat-kernel version for a square-summable function `g`
with an increment bound `‖g(· + w) - g‖ ≤ K min(|εw|, 1)` in place of the sampled solution
`ū_s`.
-/

namespace LongRangeHeat.Statements

open LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (generator kappa Edge)

/-- **The telescoping identity (3.2).** For `ε ≠ 0`, every `v : εℤ^d → ℝ` and all
`x, z ∈ εℤ^d` (here `z = εw`), `v(x + z) - v(x) = ε ∑_{(y,i) ∈ γ_{x,z}} sgn(z_i) D_i v(y)`. -/
theorem telescoping {d : ℕ} {ε : ℝ} (hε : ε ≠ 0) (v : Site d → ℝ) (x w : Site d) :
    v (x + w) - v x = ε * ∑ e ∈ canonicalPath x w,
      (Int.sign (w e.2) : ℝ) * discreteDeriv ε e.2 v e.1 :=
  LongRangeHeat.telescoping hε v x w

/-- **Finiteness of (3.3).** The sites `x` whose canonical path `γ_{x,z}` crosses the edge
`(y, i)` are exactly the elements of `crossingSet w y i`, and there are `|z_i| / ε = |w_i|` of
them; the path `γ_{0,z}` has `|z|_1 / ε = ∑_i |w_i|` edges. -/
theorem crossing_count {d : ℕ} (w y : Site d) (i : Fin d) :
    (∀ x, x ∈ crossingSet w y i ↔ (y, i) ∈ canonicalPath x w) ∧
      (crossingSet w y i).card = (w i).natAbs ∧
      (pathEdges w).card = ∑ j, (w j).natAbs :=
  ⟨fun _ => mem_crossingSet, card_crossingSet w y i, card_pathEdges w⟩

/-- **Proposition 3.2** (`prop:forcing`, representation of the random term), for a function
`g ∈ L²(εℤ^d)` with the increment bound `‖g(· + z) - g‖ ≤ K min(|z|, 1)` in place of `ū_s`.
There is `C > 0`, depending only on `d` and `λ`, such that for every `ε ∈ (0, 1/2)`, every
realization `a` of the conductances with values in `[λ, λ⁻¹]`, every `K` and every such `g`:
`(L̄ - L^ε) g` and the components of the field `G` of (3.3) lie in `L²(εℤ^d)`, and for every
`v ∈ L²(εℤ^d)`, `|⟨(L̄ - L^ε) g, v⟩ - κ_ε⁻¹ ⟨G, D v⟩| ≤ (C K / κ_ε) ‖v‖`. -/
theorem forcing_representation_of_increment {d : ℕ} (hd : 1 ≤ d) {lam : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ a : Edge d → ℝ,
      (∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) → ∀ (K : ℝ) (g : Site d → ℝ), MemL2 g →
      (∀ w : Site d,
        latticeNorm ε (fun q => g (q + w) - g q) ≤ K * min (radius (physical ε w)) 1) →
      MemL2 (fun q => meanGenerator ε g q - generator ε a g q) ∧
      (∀ i, MemL2 (forcingField ε a g i)) ∧
      ∀ v : Site d → ℝ, MemL2 v →
        |latticeInner ε (fun q => meanGenerator ε g q - generator ε a g q) v -
          (kappa d ε)⁻¹ * ∑ i, latticeInner ε (forcingField ε a g i) (discreteDeriv ε i v)| ≤
          C * K / kappa d ε * latticeNorm ε v :=
  LongRangeHeat.forcing_representation_of_increment hd hlam

end LongRangeHeat.Statements
