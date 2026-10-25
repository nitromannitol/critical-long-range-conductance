import LatticeProb.External.GilbargTrudinger
import LatticeProb.Analysis.TaylorHolder

/-!
# Extension supported in a fixed Euclidean ball

A neighborhood chosen before the datum fixes the support radius in the cited extension
input. Zero extension preserves the Hölder bound by comparison with a nearest boundary point.
-/

noncomputable section

namespace LongRange

open Set LatticeProb.Euclidean.Lattice LatticeProb.Elliptic

/-- A continuous function vanishing outside an open proper set preserves an interior
Hölder increment bound on the whole finite-dimensional space. -/
lemma abs_sub_le_of_zero_outside_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsOpen S) {f : E → ℝ} (hf : Continuous f)
    (hz : ∀ x, x ∉ S → f x = 0) {σ H : ℝ} (hσ : 0 < σ) (hH : 0 ≤ H)
    (hb : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ H * ‖x - y‖ ^ σ) :
    ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ σ := by
  have hcross : ∀ x ∈ S, ∀ y, y ∉ S →
      |f x - f y| ≤ H * ‖x - y‖ ^ σ := by
    intro x hx y hy
    have hproper : S ≠ univ := fun h => hy (h.symm ▸ mem_univ y)
    obtain ⟨z, hzfront, hdist⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hproper
    have hzout : z ∉ S := by
      simpa only [hS.interior_eq] using hzfront.2
    have hbound : |f x - f z| ≤ H * ‖x - z‖ ^ σ := by
      apply le_on_closure (fun w hw => hb x hx w hw)
        ((continuous_const.sub hf).abs.continuousOn) _ hzfront.1
      exact (continuous_const.mul
        ((continuous_const.sub continuous_id).norm.rpow_const
          (fun _ => Or.inr hσ.le))).continuousOn
    have hnorm : ‖x - z‖ ≤ ‖x - y‖ := by
      rw [← dist_eq_norm, ← hdist, ← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem hy
    rw [hz y hy, ← hz z hzout]
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hnorm hσ.le) hH)
  intro x y
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · exact hb x hx y hy
    · exact hcross x hx y hy
  · by_cases hy : y ∈ S
    · simpa only [abs_sub_comm (f y) (f x), norm_sub_rev y x] using hcross y hy x hx
    · rw [hz x hx, hz y hy, sub_self, abs_zero]
      exact mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)

/-- Vanishing off a set makes the global supremum bounded by the supremum on that set. -/
lemma supNorm_univ_le_of_zero_outside {d : ℕ} {S : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (hz : ∀ x, x ∉ S → f x = 0) :
    supNorm univ f ≤ supNorm S f := by
  refine iSup_le fun x => iSup_le fun _ => ?_
  by_cases hx : x ∈ S
  · exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  · simp only [hz x hx, abs_zero, ENNReal.ofReal_zero]
    exact bot_le

/-- Zero extension of a continuous function preserves the Euclidean Hölder seminorm. -/
lemma holderSeminorm_univ_le_of_zero_outside {d : ℕ} {S : Set (Fin d → ℝ)}
    (hS : IsOpen S) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hz : ∀ x, x ∉ S → f x = 0) {σ : ℝ} (hσ : 0 < σ) :
    holderSeminorm σ univ f ≤ holderSeminorm σ S f := by
  by_cases htop : holderSeminorm σ S f = ⊤
  · rw [htop]
    exact le_top
  let H := (holderSeminorm σ S f).toReal
  have hb : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ H * radius (x - y) ^ σ := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, abs_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (radius_nonneg _) _)
    apply (div_le_iff₀
      (Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) σ)).mp
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y
      (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl))))
  have hglobal : ∀ x y, |f x - f y| ≤ H * radius (x - y) ^ σ := by
    have h := abs_sub_le_of_zero_outside_open
      (hS.preimage (PiLp.continuous_ofLp 2 _))
      (hf.comp (PiLp.continuous_ofLp 2 _))
      (fun x hx => hz (WithLp.ofLp x) hx) hσ ENNReal.toReal_nonneg
      (fun x hx y hy => by
        simpa only [radius_norm, WithLp.toLp_sub, WithLp.toLp_ofLp, Function.comp_apply, H] using
          hb (WithLp.ofLp x) hx (WithLp.ofLp y) hy)
    intro x y
    simpa only [radius_norm, WithLp.toLp_sub, WithLp.ofLp_toLp, Function.comp_apply, H] using
      h (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  refine iSup_le fun x => iSup_le fun _ => iSup_le fun y => iSup_le fun _ =>
    iSup_le fun hxy => ?_
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
  exact (div_le_iff₀
    (Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) σ)).mpr (hglobal x y)

/-- A globally smooth supported function has its global coordinate norm bounded by
its norm on any open neighborhood of its support. -/
lemma c2HolderNorm_univ_le_of_tsupport_subset {d : ℕ} {S : Set (Fin d → ℝ)}
    (hS : IsOpen S) {v : (Fin d → ℝ) → ℝ} (hv : ContDiff ℝ 2 v)
    (hsupp : tsupport v ⊆ S) {σ : ℝ} (hσ : 0 < σ) :
    c2HolderNorm σ univ v ≤ c2HolderNorm σ S v := by
  have hz : ∀ x, x ∉ S → v x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
  have hp : ∀ i x, x ∉ S → partialDeriv i v x = 0 := by
    intro i x hx
    unfold partialDeriv
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hsupp h))]
    rfl
  have hpp : ∀ i j x, x ∉ S → secondPartial i j v x = 0 := by
    intro i j x hx
    have hnot : x ∉ Function.support (iteratedFDeriv ℝ 2 v) :=
      fun h => hx (hsupp (support_iteratedFDeriv_subset 2 h))
    have heq : iteratedFDeriv ℝ 2 v x = 0 := Function.notMem_support.mp hnot
    simp only [secondPartial, heq, zero_apply]
  have hcont : ∀ i j, Continuous (secondPartial i j v) := by
    intro i j
    exact (hv.continuous_iteratedFDeriv (m := 2) (by norm_num)).eval_const
      ![Pi.single i 1, Pi.single j 1]
  unfold c2HolderNorm
  apply add_le_add
  · apply add_le_add
    · exact add_le_add (supNorm_univ_le_of_zero_outside hz)
        (Finset.sum_le_sum fun i _ => supNorm_univ_le_of_zero_outside (hp i))
    · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        supNorm_univ_le_of_zero_outside (hpp i j)
  · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      holderSeminorm_univ_le_of_zero_outside hS (hcont i j) (hpp i j) hσ

/-- The cited extension input gives a global coordinate Hölder bound and support in
a Euclidean ball whose radius is chosen uniformly before the datum. -/
theorem regular_extension_of_gt_ball
    (h637 : LatticeProb.External.GilbargTrudingerHolderExtension)
    {d : ℕ} (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {U : Set (Fin d → ℝ)} (hU : LatticeProb.Elliptic.IsC2HolderDomain σ U) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ (∀ x ∈ U, radius x < R) ∧
      ∀ u : (Fin d → ℝ) → ℝ,
        ContDiffOn ℝ 2 u U → LatticeProb.Elliptic.c2HolderNorm σ U u < ⊤ →
        ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧
          (∀ x, R ≤ radius x → v x = 0) ∧ Set.EqOn v u U ∧
          LatticeProb.Elliptic.c2HolderNorm σ Set.univ v ≤
            ENNReal.ofReal C * LatticeProb.Elliptic.c2HolderNorm σ U u := by
  obtain ⟨B, hB⟩ := hU.2.2.1.isCompact_closure.exists_bound_of_continuousOn
    (radius_continuous d).continuousOn
  let R := |B| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hcl : closure U ⊆ {x | radius x < R} := by
    intro x hx
    have hxB : radius x ≤ B := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (radius_nonneg x)] using hB x hx
    exact lt_of_le_of_lt (hxB.trans (le_abs_self B)) (by dsimp [R]; linarith)
  have hopen : IsOpen {x : Fin d → ℝ | radius x < R} :=
    isOpen_lt (radius_continuous d) continuous_const
  obtain ⟨C, hC, hext⟩ := h637 d hd σ hσ hσ1 U hU _ hopen hcl
  refine ⟨C, R, hC, hR, fun x hx => hcl (subset_closure hx), ?_⟩
  intro u hu hnorm
  obtain ⟨v, hv, _, hsupp, heq, hbound⟩ := hext u hu hnorm
  refine ⟨v, hv, ?_, heq, ?_⟩
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_lt_of_ge hx) (hsupp hmem)
  · exact (c2HolderNorm_univ_le_of_tsupport_subset hopen hv hsupp hσ).trans hbound

end LongRange
