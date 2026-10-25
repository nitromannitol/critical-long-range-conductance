import LongRange.Corrector.Definition
import LongRange.HeatKernel.UnitWalk
import LatticeProb.Analysis.WeightedSquareSeries
import LatticeProb.Prob.OrthogonalSeries

/-!
# Weighted square bounds for the corrector equation

Applying weighted Cauchy--Schwarz to the corrector equation keeps the physical row
normalization explicit.
-/

namespace LongRange.Corrector.EnergyLowerBound

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Euclidean.Lattice

noncomputable section

variable {d : ℕ}

open Classical

/-- The physical outgoing conductance weight, including the zero diagonal. -/
def rowWeight (ε : ℝ) (a : Edge d → ℝ) (q z : Site d) : ℝ :=
  if hz : z = 0 then 0 else a (edgeAdd q z hz) * jumpKernel (physical ε z)

/-- The uncentered affine drift with the physical slope increment. -/
def affineDrift (ε : ℝ) (a : Edge d → ℝ) (p : Fin d → ℝ) (q : Site d) : ℝ :=
  ∑' z, rowWeight ε a q z * linearFn ε p z

/-- Ellipticity gives a nonnegative row weight. -/
theorem rowWeight_nonneg {ε lam : ℝ} (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (q z : Site d) :
    0 ≤ rowWeight ε a q z := by
  unfold rowWeight
  split
  · exact le_rfl
  · exact mul_nonneg (hlam.le.trans (ha _).1) (jumpKernel_nonneg _)

/-- Ellipticity bounds and makes summable every outgoing physical row. -/
theorem rowWeight_summable_bound (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (q : Site d) :
    Summable (rowWeight ε a q) ∧
      ∑' z, rowWeight ε a q z ≤ lam⁻¹ * ∑' z : Site d, jumpKernel (physical ε z) := by
  have hdom := (summable_jumpKernel hd hε).mul_left lam⁻¹
  have hle (z : Site d) : rowWeight ε a q z ≤ lam⁻¹ * jumpKernel (physical ε z) := by
    unfold rowWeight
    split
    · exact mul_nonneg (inv_nonneg.mpr hlam.le) (jumpKernel_nonneg _)
    · exact mul_le_mul_of_nonneg_right (ha _).2 (jumpKernel_nonneg _)
  have hs := hdom.of_nonneg_of_le (rowWeight_nonneg hlam ha q) hle
  exact ⟨hs, (hs.tsum_le_tsum hle hdom).trans_eq tsum_mul_left⟩

/-- The physical affine row is absolutely summable. -/
theorem summable_affineDrift (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ) (q : Site d) :
    Summable (fun z => rowWeight ε a q z * linearFn ε p z) := by
  have hs := summable_generator_affine hd hε hlam ha p
    (φ := 0) ⟨0, le_rfl, fun _ => by simp only [Pi.zero_apply, abs_zero, le_refl]⟩ q
  apply hs.congr
  intro z
  by_cases hz : z = 0
  · simp only [hz, rowWeight, ↓reduceDIte, zero_mul]
  · simp only [hz, rowWeight, ↓reduceDIte, Pi.zero_apply, add_zero,
      linearFn_add, add_sub_cancel_left]
    ring

/-- The corrector equation identifies its outgoing first moment with minus the affine drift. -/
theorem corrector_row_first_moment (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    {φ : Site d → ℝ} (hφ : IsCorrectorMinimizer ε U a p φ)
    {q : Site d} (hq : q ∈ latticeSet ε U) :
    (∑' z, rowWeight ε a q z * (φ (q + z) - φ q)) = -affineDrift ε a p q := by
  have hs := summable_generator_bounded hd hε.1 hlam ha
    (exists_bound_of_finite_support (hφ.1.hasFiniteSupport hε.1 hU)) q
  have hs' : Summable (fun z => rowWeight ε a q z * (φ (q + z) - φ q)) := by
    apply hs.congr
    intro z
    by_cases hz : z = 0
    · simp only [hz, rowWeight, ↓reduceDIte, zero_mul]
    · simp only [hz, rowWeight, ↓reduceDIte]
      ring
  have heq := (isCorrectorMinimizer_iff hd hε hU hlam ha p hφ.1).mp hφ.2 q hq
  have hterm (z : Site d) :
      (if hz : z = 0 then 0 else a (edgeAdd q z hz) *
        ((linearFn ε p (q + z) + φ (q + z)) - (linearFn ε p q + φ q)) *
          jumpKernel (physical ε z)) =
      rowWeight ε a q z * linearFn ε p z +
        rowWeight ε a q z * (φ (q + z) - φ q) := by
    by_cases hz : z = 0
    · simp only [hz, rowWeight, ↓reduceDIte, zero_mul, add_zero]
    · simp only [hz, rowWeight, ↓reduceDIte, linearFn_add]
      ring
  unfold generator at heq
  simp_rw [hterm] at heq
  rw [(summable_affineDrift hd hε.1 hlam ha p q).tsum_add hs'] at heq
  have hscale : ε ^ d / kappa d ε ≠ 0 :=
    div_ne_zero (pow_ne_zero _ hε.1.ne') (kappa_pos hd hε).ne'
  have hz := (mul_eq_zero.mp heq).resolve_left hscale
  exact eq_neg_of_add_eq_zero_right hz

/-- Cauchy--Schwarz at all interior sites gives a deterministic lower bound on the energy. -/
theorem correctorEnergy_ge_affineDrift (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hlam : 0 < lam)
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) (p : Fin d → ℝ)
    (s : Finset (Site d)) (hsU : ∀ q ∈ s, q ∈ latticeSet ε U)
    {R : ℝ} (hR : 0 < R)
    (hrow : ∀ q, ∑' z, rowWeight ε a q z ≤ R) :
    ε ^ (2 * d) / (2 * kappa d ε * R) * ∑ q ∈ s, affineDrift ε a p q ^ 2 ≤
      correctorEnergy ε U a p := by
  obtain ⟨φ, hφ, _⟩ := existsUnique_correctorMinimizer hd hε hU hlam ha p
  let Q : Site d × Site d → ℝ := fun qz =>
    rowWeight ε a qz.1 qz.2 * (φ (qz.1 + qz.2) - φ qz.1) ^ 2
  have hQ (qz : Site d × Site d) : 0 ≤ Q qz :=
    mul_nonneg (rowWeight_nonneg hlam ha _ _) (sq_nonneg _)
  have hsum : Summable Q := by
    apply (summable_bilinForm hd hε.1 hlam ha
      (hφ.1.hasFiniteSupport hε.1 hU) (hφ.1.hasFiniteSupport hε.1 hU)).congr
    intro qz
    dsimp only [Q, rowWeight]
    split_ifs <;> ring
  have hsite (q : Site d) (hq : q ∈ s) : affineDrift ε a p q ^ 2 ≤
      R * ∑' z, Q (q, z) := by
    have hsfirst := summable_generator_bounded hd hε.1 hlam ha
      (exists_bound_of_finite_support (hφ.1.hasFiniteSupport hε.1 hU)) q
    have hsfirst' : Summable (fun z => rowWeight ε a q z * (φ (q + z) - φ q)) := by
      apply hsfirst.congr
      intro z
      by_cases hz : z = 0
      · simp only [hz, rowWeight, ↓reduceDIte, zero_mul]
      · simp only [hz, rowWeight, ↓reduceDIte]
        ring
    have hc := LatticeProb.sq_tsum_mul_le (rowWeight_nonneg hlam ha q)
      (rowWeight_summable_bound hd hε.1 hlam ha q).1 hsfirst' (hsum.prod_factor q)
    rw [corrector_row_first_moment hd hε hlam hU ha p hφ (hsU q hq), neg_sq] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (hrow q) (tsum_nonneg (fun z => hQ (q, z))))
  have htotal : (∑ q ∈ s, affineDrift ε a p q ^ 2) ≤ R * ∑' qz, Q qz := by
    calc
      _ ≤ ∑ q ∈ s, R * ∑' z, Q (q, z) := Finset.sum_le_sum hsite
      _ = R * ∑ q ∈ s, ∑' z, Q (q, z) := (Finset.mul_sum _ _ _).symm
      _ ≤ R * ∑' q, ∑' z, Q (q, z) :=
        mul_le_mul_of_nonneg_left
          (hsum.prod.sum_le_tsum s (fun q _ => tsum_nonneg (fun z => hQ (q, z)))) hR.le
      _ = _ := by rw [hsum.tsum_prod]
  have henergy : correctorEnergy ε U a p =
      ε ^ (2 * d) / (2 * kappa d ε) * ∑' qz, Q qz := by
    rw [correctorEnergy_eq_bilinForm hd hε hU hlam ha p hφ.1 hφ.2]
    unfold bilinForm
    congr 1
    apply tsum_congr
    intro qz
    dsimp only [Q, rowWeight]
    split_ifs <;> ring
  rw [henergy]
  have hkap := kappa_pos hd hε
  have hn : 0 ≤ ε ^ (2 * d) / (2 * kappa d ε * R) :=
    div_nonneg (pow_nonneg hε.1.le _) (mul_nonneg (mul_nonneg (by norm_num) hkap.le) hR.le)
  have hm := mul_le_mul_of_nonneg_left htotal hn
  calc
    _ ≤ ε ^ (2 * d) / (2 * kappa d ε * R) * (R * ∑' qz, Q qz) := hm
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      field_simp


end

end LongRange.Corrector.EnergyLowerBound
