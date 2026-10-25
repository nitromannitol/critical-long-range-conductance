import LatticeProb.Analysis.Elliptic.Domain

/-!
# One-dimensional domains are intervals

A bounded connected open domain in dimension one is an open interval under evaluation
at its sole coordinate. In particular, this applies to domains with `C^{2,σ}` boundary.
-/

namespace LongRange

open Set

/-- A one-dimensional `C^{2,σ}` domain is a nonempty bounded open interval. -/
theorem eq_interval_of_isC2HolderDomain {σ : ℝ} {U : Set (Fin 1 → ℝ)}
    (hU : LatticeProb.Elliptic.IsC2HolderDomain σ U) :
    ∃ α β : ℝ, α < β ∧ U = {x : Fin 1 → ℝ | α < x 0 ∧ x 0 < β} := by
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  let S : Set ℝ := e '' U
  have hopen : IsOpen S := e.isOpenMap U hU.1
  have hconn : IsConnected S := hU.2.1.image e e.continuous.continuousOn
  have hbounded : Bornology.IsBounded S :=
    hU.2.2.1.image_eval 0
  have hbelow : BddBelow S := hbounded.bddBelow
  have habove : BddAbove S := hbounded.bddAbove
  have hinterval : S = Ioo (sInf S) (sSup S) := by
    apply Subset.antisymm
    · rw [← interior_Icc]
      exact hopen.subset_interior_iff.mpr (subset_Icc_csInf_csSup hbelow habove)
    · exact hconn.Ioo_csInf_csSup_subset hbelow habove
  obtain ⟨y, hy⟩ := hconn.nonempty
  have hyinterval : sInf S < y ∧ y < sSup S := by
    rwa [hinterval] at hy
  refine ⟨sInf S, sSup S, hyinterval.1.trans hyinterval.2, ?_⟩
  ext x
  change x ∈ U ↔ e x ∈ Ioo (sInf S) (sSup S)
  rw [← hinterval]
  exact (e.injective.mem_set_image).symm

end LongRange
