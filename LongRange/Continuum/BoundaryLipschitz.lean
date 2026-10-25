import LongRange.TwoScale.ResidualDefs
import LatticeProb.Analysis.Elliptic.Dirichlet
import LatticeProb.Analysis.TaylorHolder

/-!
# Lipschitz control of the exterior defect

A continuous extension inherits the zero boundary values of the Dirichlet solution.
A bounded derivative then controls its exterior defect by Euclidean distance to the domain.
-/

namespace LongRange

open Set LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

/-- Equality in the domain extends to its frontier by continuity. -/
lemma eq_zero_on_frontier_of_eqOn {U : Set (Fin d → ℝ)}
    {v ū : (Fin d → ℝ) → ℝ} (hv : Continuous v)
    (hū : ContinuousOn ū (closure U)) (heq : Set.EqOn v ū U)
    (h0 : ∀ x ∈ frontier U, ū x = 0) : ∀ x ∈ frontier U, v x = 0 := by
  have hc := heq.of_subset_closure hv.continuousOn hū subset_closure (Subset.refl _)
  intro x hx
  exact (hc (frontier_subset_closure hx)).trans (h0 x hx)

/-- A globally bounded derivative controls exterior values by Euclidean domain distance. -/
lemma abs_le_infDist_of_frontier {U : Set (Fin d → ℝ)} (hne : U.Nonempty)
    {v : (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) {N : ℝ}
    (hN : ∀ x, ‖fderiv ℝ v x‖ ≤ N) (h0 : ∀ x ∈ frontier U, v x = 0)
    (y : Fin d → ℝ) (hy : y ∉ U) :
    |v y| ≤ N * Metric.infDist (WithLp.toLp 2 y) (WithLp.toLp 2 '' U) := by
  let e := (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).symm
  have hy' : e y ∈ (e '' U)ᶜ := by
    simpa only [mem_compl_iff, e.injective.mem_set_image] using hy
  have hproper : (e '' U)ᶜ ≠ univ := by
    intro h
    obtain ⟨x, hx⟩ := hne
    have : e x ∈ (e '' U)ᶜ := h.symm ▸ mem_univ _
    exact this ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hy' hproper
  rw [frontier_compl, ← e.image_frontier] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  simp only [compl_compl] at hd
  have hnonneg : 0 ≤ N := (norm_nonneg _).trans (hN x)
  have hbound := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => hv.differentiable (by norm_num) w) (fun w _ => hN w)
    (mem_univ x) (mem_univ y)
  calc
    |v y| = ‖v y - v x‖ := by rw [h0 x hx, sub_zero, Real.norm_eq_abs]
    _ ≤ N * ‖y - x‖ := hbound
    _ ≤ N * radius (y - x) := mul_le_mul_of_nonneg_left
      (LatticeProb.TaylorHolder.norm_le_radius _) hnonneg
    _ = N * dist (e y) (e x) := by rw [radius_norm]; rfl
    _ = _ := by rw [← hd]; rfl

/-- The sampled exterior defect vanishes at every lattice point in the domain. -/
lemma exteriorDefect_eq_zero_on_latticeSet (ε : ℝ) (U : Set (Fin d → ℝ))
    (v : (Fin d → ℝ) → ℝ) :
    ∀ x ∈ latticeSet ε U, exteriorDefect ε U v x = 0 := by
  intro x hx
  simp only [latticeSet, mem_setOf_eq] at hx
  simp only [exteriorDefect, zeroExtension, if_pos hx, sub_self]

/-- The sampled exterior defect is bounded by Euclidean distance to the domain. -/
lemma exteriorDefect_le_boundaryDistance {ε : ℝ} {U : Set (Fin d → ℝ)}
    (hne : U.Nonempty) {v : (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ 1 v) {N : ℝ}
    (hN : ∀ x, ‖fderiv ℝ v x‖ ≤ N) (h0 : ∀ x ∈ frontier U, v x = 0)
    (y : Site d) : |exteriorDefect ε U v y| ≤ N * boundaryDistance ε U y := by
  by_cases hy : physical ε y ∈ U
  · simp only [exteriorDefect, zeroExtension, if_pos hy, sub_self, abs_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hN (physical ε y))) Metric.infDist_nonneg
  · simp only [exteriorDefect, zeroExtension, if_neg hy, sub_zero, boundaryDistance]
    exact abs_le_infDist_of_frontier hne hv hN h0 _ hy

end

end LongRange
