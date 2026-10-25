import LongRange.Walk.KilledResolvent
import LongRange.Walk.InitialLaw
import LongRange.Walk.Multiplier
import LatticeProb.Prob.JumpChain.PositionFdd
import LatticeProb.Prob.JumpChain.KilledL2
import LatticeProb.Prob.JumpChain.MarkovProperty

/-!
# Finite killed walk observations

The discrete killed semigroup acts by the finite killed transition kernel.
Physical-volume weighted pairings recover averages against an initial lattice density.
-/

namespace LongRange

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open LatticeProb.JumpChain.BoundedRates
open scoped BoundedContinuousFunction NNReal

noncomputable section

variable {d : ℕ}

/-- The discrete killed semigroup evaluates by summing the killed kernel over the domain. -/
theorem discreteKilledSemigroup_apply (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (t : ℝ≥0)
    (f : discreteL2 ε U) (x : Site d) (hx : x ∈ latticeSet ε U) :
    (discreteKilledSemigroup hd hε hlam a ha hb).operator t f x =
      ∑ y ∈ (latticeSet_finite hε hb).toFinset,
        (walkRates hd hε hlam a ha).killedKernel (latticeSet ε U) t x y * f y :=
  killedOp_apply _ _ _ (pow_pos hε d) t f x hx

/-- Discrete multiplication has its sampled pointwise value at every interior atom. -/
theorem mulDiscrete_apply_atom {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (φ : (Fin d → ℝ) →ᵇ ℝ)
    (f : discreteL2 ε U) (x : Site d) (hx : x ∈ latticeSet ε U) :
    mulDiscrete ε U φ f x = φ (physical ε x) * f x :=
  eq_of_ae_killedMeasure (latticeSet ε U) (pow_pos hε d)
    (mulDiscrete_apply ε U φ f) x hx

/-- The physical-volume weighted inner product is the finite lattice pairing. -/
theorem inner_discreteL2_eq_sum {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (g f : discreteL2 ε U) :
    inner ℝ g f = ε ^ d * ∑ x ∈ (latticeSet_finite hε hb).toFinset, g x * f x := by
  classical
  rw [L2.inner_def, integral_countable (L2.integrable_inner g f)]
  simp only [Real.inner_apply, smul_eq_mul, latticeMeasure,
    killedMeasure_real_singleton (latticeSet ε U) (pow_pos hε d).le]
  rw [tsum_eq_sum (s := (latticeSet_finite hε hb).toFinset)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos ((latticeSet_finite hε hb).mem_toFinset.mp hx)]
  · intro x hx
    rw [if_neg (fun h => hx ((latticeSet_finite hε hb).mem_toFinset.mpr h)), zero_mul]

/-- An initial density converts a finite initial-law average into the discrete pairing. -/
theorem sum_initialLaw_eq_inner {ε : ℝ} (hε : 0 < ε)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    (ν : Measure (Site d)) (g f : discreteL2 ε U)
    (hν : ∀ x ∈ latticeSet ε U, ν.real {x} = ε ^ d * g x) :
    (∑ x ∈ (latticeSet_finite hε hb).toFinset, ν.real {x} * f x) = inner ℝ g f := by
  classical
  rw [inner_discreteL2_eq_sum hε hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hν x ((latticeSet_finite hε hb).mem_toFinset.mp hx), mul_assoc]

/-- Finite observation cylinders partition a survival-weighted test function. -/
theorem integral_survival_eq_sum_cylinders {S : Type*} [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (rates : JumpChain.BoundedRates S)
    (ν : Measure S) [IsProbabilityMeasure ν] (U : Set S) (hU : U.Finite)
    {k : ℕ} (t : Fin k → ℝ≥0) (T : ℝ≥0) (ht : ∀ i, t i ≤ T)
    (F : (Fin k → S) → ℝ) :
    (∫ h, {h : JumpChain.RegularHistory S | ∀ s ≤ T, h.position s ∈ U}.indicator
      (fun h => F (fun i => h.position (t i))) h ∂rates.regularLaw ν) =
      letI := hU.fintype
      ∑ x : Fin k → U,
        (rates.regularLaw ν).real {h |
          (∀ i, h.position (t i) = (x i : S)) ∧
            ∀ s ≤ T, h.position s ∈ U} * F (fun i => x i) := by
  classical
  letI := hU.fintype
  let A : Set (JumpChain.RegularHistory S) := {h | ∀ s ≤ T, h.position s ∈ U}
  let E (x : Fin k → U) : Set (JumpChain.RegularHistory S) :=
    {h | (∀ i, h.position (t i) = (x i : S)) ∧ ∀ s ≤ T, h.position s ∈ U}
  have hA : MeasurableSet A :=
    (naturalSigma_le T) _ (measurableSet_survival_naturalSigma U T)
  have hE (x : Fin k → U) : MeasurableSet (E x) := by
    apply MeasurableSet.inter _ hA
    have hm : MeasurableSet (⋂ i : Fin k,
        {h : JumpChain.RegularHistory S | h.position (t i) = (x i : S)}) :=
      MeasurableSet.iInter fun i => measurableSet_eq_fun
        (JumpChain.RegularHistory.measurable_position (S := S) (t i)) measurable_const
    convert hm using 1
    ext h
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  have heq : A.indicator (fun h => F (fun i => h.position (t i))) =
      fun h => ∑ x : Fin k → U, (E x).indicator (fun _ => F (fun i => x i)) h := by
    funext h
    by_cases hh : h ∈ A
    · let x : Fin k → U := fun i => ⟨h.position (t i), hh _ (ht i)⟩
      rw [Set.indicator_of_mem hh, Finset.sum_eq_single x]
      · rw [Set.indicator_of_mem (show h ∈ E x from ⟨fun _ => rfl, hh⟩)]
      · intro y _ hy
        apply Set.indicator_of_notMem
        rintro ⟨he, _⟩
        apply hy
        funext i
        exact Subtype.ext (he i).symm
      · exact fun hx => (hx (Finset.mem_univ x)).elim
    · rw [Set.indicator_of_notMem hh]
      symm
      apply Finset.sum_eq_zero
      intro x _
      exact Set.indicator_of_notMem (fun hx => hh hx.2) _
  change (∫ h, A.indicator _ h ∂rates.regularLaw ν) = _
  rw [heq, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_indicator_const _ (hE x), smul_eq_mul]
  · intro x _
    exact (integrable_const _).indicator (hE x)

/-- The atomic killed finite-dimensional law as a finite sum of real masses. -/
theorem regularLaw_killed_position_fdd_real {S : Type*} [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (rates : JumpChain.BoundedRates S)
    (ν : Measure S) [IsProbabilityMeasure ν] (U : Set S) (hU : U.Finite)
    (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (x : Fin (k + 1) → S) :
    (rates.regularLaw ν).real {h |
      (∀ i : Fin (k + 1), 0 < i → h.position (t i) = x i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ U} =
      ∑ z ∈ hU.toFinset, ν.real {z} *
        ∏ i : Fin k, rates.killedKernel U (t i.succ - t i.castSucc)
          (Function.update x 0 z i.castSucc) (Function.update x 0 z i.succ) := by
  classical
  rw [measureReal_def, rates.regularLaw_killed_position_fdd ν U k t ht ht0 x,
    tsum_eq_sum (s := hU.toFinset)]
  · rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro z hz
      rw [if_pos (hU.mem_toFinset.mp hz), ENNReal.toReal_mul, ENNReal.toReal_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact ENNReal.toReal_ofReal (rates.killedKernel_nonneg U _ _ _)
    · intro z _
      exact ENNReal.mul_ne_top (by split_ifs <;> simp)
        (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
  · intro z hz
    rw [if_neg (fun h => hz (hU.mem_toFinset.mpr h)), zero_mul]

/-- Products of sampled observations on surviving paths have the finite killed-kernel law. -/
theorem killed_product_expectation_eq_kernel_sum (hd : 1 ≤ d)
    {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {U : Set (Fin d → ℝ)}
    (hb : Bornology.IsBounded U) (ν : Measure (Site d)) [IsProbabilityMeasure ν]
    (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    (∫ h, {h : JumpChain.RegularHistory (Site d) |
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet ε U}.indicator
      (fun h => ∏ i : Fin k, φ i (physical ε (h.position (t i.succ)))) h
        ∂(walkRates hd hε hlam a ha).regularLaw ν) =
      letI := (latticeSet_finite hε hb).fintype
      ∑ y : Fin k → latticeSet ε U,
        (∑ z ∈ (latticeSet_finite hε hb).toFinset, ν.real {z} *
          ∏ i : Fin k, (walkRates hd hε hlam a ha).killedKernel (latticeSet ε U)
            (t i.succ - t i.castSucc)
            (Fin.cons (α := fun _ => Site d) z (fun j => (y j : Site d)) i.castSucc)
            (y i)) * ∏ i : Fin k, φ i (physical ε (y i)) := by
  classical
  letI := (latticeSet_finite hε hb).fintype
  rw [integral_survival_eq_sum_cylinders (walkRates hd hε hlam a ha) ν (latticeSet ε U)
    (latticeSet_finite hε hb) (fun i => t i.succ) (t (Fin.last k))
    (fun i => ht (Fin.le_last _))
    (fun x => ∏ i : Fin k, φ i (physical ε (x i)))]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  have he := regularLaw_killed_position_fdd_real (walkRates hd hε hlam a ha)
    ν (latticeSet ε U) (latticeSet_finite hε hb) k t ht ht0
    (Fin.cons (α := fun _ => Site d) 0 (fun j => (y j : Site d)))
  have hevent : {h : JumpChain.RegularHistory (Site d) |
      (∀ i, h.position (t i.succ) = (y i : Site d)) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet ε U} =
      {h : JumpChain.RegularHistory (Site d) |
      (∀ i : Fin (k + 1), 0 < i →
        h.position (t i) = Fin.cons (α := fun _ => Site d) 0 (fun j => (y j : Site d)) i) ∧
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet ε U} := by
    ext h
    simp only [Set.mem_setOf_eq, Fin.forall_fin_succ, lt_self_iff_false,
      false_implies, Fin.cons_succ, Fin.succ_pos, true_implies, true_and]
  rw [hevent, he]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Fin.update_cons_zero, Fin.cons_succ]

/-- Backward products use successive time increments and sampled multipliers.
The empty product is the constant one on the finite domain. -/
def killedBackwardProduct (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) :
    (k : ℕ) → (Fin k → ℝ≥0) →
      (Fin k → ((Fin d → ℝ) →ᵇ ℝ)) → discreteL2 ε U
  | 0, _, _ => (memLp_latticeMeasure hε hb (fun _ => 1)).toLp _
  | k + 1, δ, φ => (discreteKilledSemigroup hd hε hlam a ha hb).operator (δ 0)
      (mulDiscrete ε U (φ 0)
        (killedBackwardProduct hd hε hlam a ha hb k
          (fun i => δ i.succ) (fun i => φ i.succ)))

/-- The backward product is exactly the sum over finite killed-kernel paths. -/
theorem killedBackwardProduct_apply (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U) (k : ℕ)
    (δ : Fin k → ℝ≥0) (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ))
    (x : Site d) (hx : x ∈ latticeSet ε U) :
    killedBackwardProduct hd hε hlam a ha hb k δ φ x =
      letI := (latticeSet_finite hε hb).fintype
      ∑ y : Fin k → latticeSet ε U,
        ∏ i : Fin k, (walkRates hd hε hlam a ha).killedKernel (latticeSet ε U)
          (δ i) (Fin.cons (α := fun _ => Site d) x (fun j => (y j : Site d)) i.castSucc) (y i) *
            φ i (physical ε (y i)) := by
  classical
  letI := (latticeSet_finite hε hb).fintype
  induction k generalizing x with
  | zero =>
    rw [killedBackwardProduct, toLp_latticeMeasure_apply hε hb _ x hx]
    simp
  | succ k ih =>
    rw [killedBackwardProduct,
      discreteKilledSemigroup_apply hd hε hlam a ha hb _ _ x hx]
    have hsum (f : Site d → ℝ) :
        (∑ y ∈ (latticeSet_finite hε hb).toFinset, f y) =
          ∑ y : latticeSet ε U, f y := by
      apply Finset.sum_bij (fun y hy =>
        (⟨y, (latticeSet_finite hε hb).mem_toFinset.mp hy⟩ : latticeSet ε U))
        (fun _ _ => Finset.mem_univ _) _ _ _
      · intro y _ z _ he
        exact congrArg Subtype.val he
      · intro y _
        exact ⟨y, (latticeSet_finite hε hb).mem_toFinset.mpr y.property, rfl⟩
      · intro _ _
        rfl
    rw [hsum]
    simp_rw [mulDiscrete_apply_atom hε _ _ _ (Subtype.property _),
      ih _ _ _ (Subtype.property _), ← mul_assoc, Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    symm
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => latticeSet ε U)).symm
    intro y
    simp only [Fin.prod_univ_succ, Fin.consEquiv_symm_apply, Fin.tail]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    change (y i.castSucc : Site d) = _
    exact congrArg (fun v : Fin (k + 1) → Site d => v i.castSucc)
      (Fin.cons_self_tail (fun j => (y j : Site d))).symm

/-- The killed product expectation is the initial-law average of the backward product. -/
theorem killed_product_expectation_eq_sum (hd : 1 ≤ d)
    {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {U : Set (Fin d → ℝ)}
    (hb : Bornology.IsBounded U) (ν : Measure (Site d)) [IsProbabilityMeasure ν]
    (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    (∫ h, {h : JumpChain.RegularHistory (Site d) |
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet ε U}.indicator
      (fun h => ∏ i : Fin k, φ i (physical ε (h.position (t i.succ)))) h
        ∂(walkRates hd hε hlam a ha).regularLaw ν) =
      ∑ x ∈ (latticeSet_finite hε hb).toFinset, ν.real {x} *
        killedBackwardProduct hd hε hlam a ha hb k
          (fun i => t i.succ - t i.castSucc) φ x := by
  classical
  letI := (latticeSet_finite hε hb).fintype
  rw [killed_product_expectation_eq_kernel_sum hd hε hlam a ha hb ν k t ht ht0 φ]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [killedBackwardProduct_apply hd hε hlam a ha hb k _ _ x
    ((latticeSet_finite hε hb).mem_toFinset.mp hx), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- A lattice density identifies killed product expectations with the weighted L² pairing. -/
theorem killed_product_expectation_eq_inner (hd : 1 ≤ d)
    {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {U : Set (Fin d → ℝ)}
    (hb : Bornology.IsBounded U) (ν : Measure (Site d)) [IsProbabilityMeasure ν]
    (g : discreteL2 ε U)
    (hν : ∀ x ∈ latticeSet ε U, ν.real {x} = ε ^ d * g x)
    (k : ℕ) (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    (∫ h, {h : JumpChain.RegularHistory (Site d) |
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet ε U}.indicator
      (fun h => ∏ i : Fin k, φ i (physical ε (h.position (t i.succ)))) h
        ∂(walkRates hd hε hlam a ha).regularLaw ν) =
      inner ℝ g (killedBackwardProduct hd hε hlam a ha hb k
        (fun i => t i.succ - t i.castSucc) φ) := by
  rw [killed_product_expectation_eq_sum hd hε hlam a ha hb ν k t ht ht0 φ]
  exact sum_initialLaw_eq_inner hε hb ν g _ hν

/-- A single backward observation is the killed semigroup applied to its sampled test. -/
theorem killedBackwardProduct_one (hd : 1 ≤ d) {ε lam : ℝ} (hε : 0 < ε)
    (hlam : 0 < lam) (a : Edge d → ℝ) (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    {U : Set (Fin d → ℝ)} (hb : Bornology.IsBounded U)
    (δ : Fin 1 → ℝ≥0) (φ : Fin 1 → ((Fin d → ℝ) →ᵇ ℝ)) :
    killedBackwardProduct hd hε hlam a ha hb 1 δ φ =
      (discreteKilledSemigroup hd hε hlam a ha hb).operator (δ 0)
        ((memLp_latticeMeasure hε hb (fun x => φ 0 (physical ε x))).toLp _) := by
  rw [killedBackwardProduct]
  congr 1
  apply killedLp_ext (latticeSet ε U) (ε ^ d)
  intro x hx
  change mulDiscrete ε U (φ 0)
    (killedBackwardProduct hd hε hlam a ha hb 0
      (fun i => δ i.succ) (fun i => φ i.succ)) x =
      (memLp_latticeMeasure hε hb (fun x => φ 0 (physical ε x))).toLp _ x
  rw [mulDiscrete_apply_atom hε _ _ x hx, killedBackwardProduct,
    toLp_latticeMeasure_apply hε hb _ x hx,
    toLp_latticeMeasure_apply hε hb _ x hx, mul_one]

/-- Full-cell initial laws give the pairing with their actual full-space cell averages. -/
theorem initialLaw_killed_product_expectation_eq_inner (hd : 1 ≤ d)
    {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) (a : Edge d → ℝ)
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹) {U : Set (Fin d → ℝ)}
    (hb : Bornology.IsBounded U) (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g volume) (hg0 : ∀ᵐ y ∂volume, 0 ≤ g y)
    (hg1 : ∫ y, g y = 1) (k : ℕ) (t : Fin (k + 1) → ℝ≥0)
    (ht : Monotone t) (ht0 : t 0 = 0) (φ : Fin k → ((Fin d → ℝ) →ᵇ ℝ)) :
    (∫ h, {h : JumpChain.RegularHistory (Site d) |
        ∀ s ≤ t (Fin.last k), h.position s ∈ latticeSet ε U}.indicator
      (fun h => ∏ i : Fin k, φ i (physical ε (h.position (t i.succ)))) h
        ∂(walkRates hd hε hlam a ha).regularLaw
          (initialLaw ε g hε hg hg0 hg1 : Measure (Site d))) =
      inner ℝ ((memLp_latticeMeasure hε hb (cellAverage ε Set.univ g)).toLp _)
        (killedBackwardProduct hd hε hlam a ha hb k
          (fun i => t i.succ - t i.castSucc) φ) := by
  apply killed_product_expectation_eq_inner hd hε hlam a ha hb _ _ _ k t ht ht0 φ
  intro x hx
  rw [measureReal_def, initialLaw_singleton,
    ENNReal.toReal_ofReal (cellMass_nonneg hε hg0 x),
    toLp_latticeMeasure_apply hε hb _ x hx]

end

end LongRange
