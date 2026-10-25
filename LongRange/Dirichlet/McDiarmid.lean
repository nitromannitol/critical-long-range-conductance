import LongRange.Model.Conductance
import LatticeProb.Prob.McDiarmidIndep

/-!
# McDiarmid bounds for finite families of conductances

An injectively indexed finite family of edges inherits independence from Assumption (U).
Reindexing by `Fin` transfers the universal McDiarmid bound to this family.
-/

namespace LongRange

open MeasureTheory ProbabilityTheory LatticeProb

noncomputable section

/-- Bounded coordinate oscillations give a universal O₂ bound for a finite edge family. -/
theorem edge_mcdiarmid :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
      {P : Measure Ω} {lam : ℝ}
      {a : Ω → Edge d → ℝ}, AssumptionU P lam a →
      ∀ {J : Type*} [Fintype J] [DecidableEq J] (e : J → Edge d), Function.Injective e →
      ∀ (f : (J → ℝ) → ℝ), Measurable f → ∀ δ : J → ℝ, (∀ j, 0 ≤ δ j) →
      (∀ j (y : J → ℝ) (t : ℝ), (∀ i, y i ∈ Set.Icc lam lam⁻¹) →
        t ∈ Set.Icc lam lam⁻¹ → |f y - f (Function.update y j t)| ≤ δ j) →
      OsBound P 2 (C * Real.sqrt (∑ j, δ j ^ 2))
        (fun ω => |f (fun j => a ω (e j)) - ∫ ω', f (fun j => a ω' (e j)) ∂P|) := by
  classical
  obtain ⟨C, hC, hbound⟩ := mcdiarmid_indep
  refine ⟨C, hC, ?_⟩
  intro d Ω _ P lam a hA J _ _ e he f hf δ hδ hdiff
  haveI := hA.isProbabilityMeasure
  let σ := Fintype.equivFin J
  let X := fun k ω => a ω (e (σ.symm k))
  let g := fun y : Fin (Fintype.card J) → ℝ => f (fun j => y (σ j))
  have hg : Measurable g :=
    hf.comp (measurable_pi_lambda _ fun j => measurable_pi_apply (σ j))
  have hind : iIndepFun X P := hA.iIndep.precomp (he.comp σ.symm.injective)
  have hgbd : ∀ k (y : Fin (Fintype.card J) → ℝ) t,
      (∀ i, y i ∈ Set.Icc lam lam⁻¹) → t ∈ Set.Icc lam lam⁻¹ →
      |g y - g (Function.update y k t)| ≤ δ (σ.symm k) := by
    intro k y t hy ht
    have hup : (fun j => Function.update y k t (σ j)) =
        Function.update (fun j => y (σ j)) (σ.symm k) t :=
      Function.update_comp_equiv y σ k t
    dsimp only [g]
    rw [hup]
    exact hdiff (σ.symm k) _ t (fun j => hy (σ j)) ht
  have h := (hbound hA.lam_pos hA.lam_le_one P X
    (fun k => hA.measurable _) hind (fun k ω => hA.bounds ω _) g hg
    (fun k => δ (σ.symm k)) (fun k => hδ _) hgbd).2
  have hsample : ∀ ω, g (fun k => X k ω) = f (fun j => a ω (e j)) := by
    intro ω
    simp only [g, X, Equiv.symm_apply_apply]
  have hsum : (∑ k, δ (σ.symm k) ^ 2) = ∑ j, δ j ^ 2 := by
    exact σ.symm.sum_comp (fun j => δ j ^ 2)
  simpa only [hsum, hsample] using h

end

end LongRange
