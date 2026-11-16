import LongRange.Support.Prob.Cadlag.HalfLine.ChainPathLaw

/-!
# Measurable dependence of jump-chain laws on the rates

For a family of bounded jump rates indexed by a measurable parameter, with measurable entries
and a common total-rate bound, the singleton transition masses and the finite-dimensional
distributions of the position process depend measurably on the parameter.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
open scoped ENNReal NNReal

noncomputable section

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Countable S]
  [MeasurableSingletonClass S] {r : Ω → BoundedRates S} {R : ℝ}

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem measurable_tsum_q (hq : ∀ i j, Measurable fun ω => (r ω).q i j) (i : S) :
    Measurable fun ω => ∑' k, (r ω).q i k := by
  have h : ∀ ω, ∑' k, (r ω).q i k = (∑' k, ENNReal.ofReal ((r ω).q i k)).toReal := by
    intro ω
    rw [← ENNReal.ofReal_tsum_of_nonneg ((r ω).q_nonneg i) ((r ω).summable i),
      ENNReal.toReal_ofReal (tsum_nonneg ((r ω).q_nonneg i))]
  simp_rw [h]
  exact (Measurable.tsum fun k => (hq i k).ennreal_ofReal).ennreal_toReal

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem measurable_p (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (i j : S) : Measurable fun ω => (r ω).p i j := by
  by_cases hji : j = i
  · have : ∀ ω, (r ω).p i j = 1 - (∑' k, (r ω).q i k) / R := by
      intro ω
      simp only [BoundedRates.p, hji, ↓reduceIte, hR]
    simp_rw [this]
    exact measurable_const.sub ((measurable_tsum_q hq i).div_const R)
  · have : ∀ ω, (r ω).p i j = (r ω).q i j / R := by
      intro ω
      simp only [BoundedRates.p, hji, ↓reduceIte, hR]
    simp_rw [this]
    exact (hq i j).div_const R

theorem measurable_kernel_singleton (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (i j : S) : Measurable fun ω => (r ω).kernel i {j} := by
  simp_rw [BoundedRates.kernel_singleton]
  exact (measurable_p hq hR i j).ennreal_ofReal

theorem measurable_kernel_pow_singleton (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (n : ℕ) (i j : S) :
    Measurable fun ω => ((r ω).kernel ^ n) i {j} := by
  induction n generalizing i j with
  | zero =>
    have : ∀ ω, ((r ω).kernel ^ 0) i {j} = (Measure.dirac i) {j} := by
      intro ω
      rfl
    simp_rw [this]
    exact measurable_const
  | succ n ih =>
    have : ∀ ω, ((r ω).kernel ^ (n + 1)) i {j} =
        ∑' m, (r ω).kernel m {j} * ((r ω).kernel ^ n) i {m} := by
      intro ω
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ (measurableSet_singleton j),
        lintegral_countable']
    simp_rw [this]
    exact Measurable.tsum fun m =>
      (measurable_kernel_singleton hq hR m j).mul (ih i m)

theorem measurable_transitionKernel_singleton (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (t : ℝ≥0) (i j : S) :
    Measurable fun ω => (r ω).transitionKernel t i {j} := by
  have : ∀ ω, (r ω).transitionKernel t i {j} =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(R * t)) * (R * t) ^ n / n.factorial) *
        ((r ω).kernel ^ n) i {j} := by
    intro ω
    rw [BoundedRates.transitionKernel_singleton, hR]
  simp_rw [this]
  exact Measurable.tsum fun n => measurable_const.mul
    (measurable_kernel_pow_singleton hq hR n i j)

theorem measurable_regularLaw_fdd (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (x : S) {k : ℕ} (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t)
    (ht0 : t 0 = 0) (y : Fin k → S) :
    Measurable fun ω => (r ω).regularLaw (Measure.dirac x)
      {h | ∀ j : Fin k, h.position (t j.succ) = y j} := by
  have hset : {h : RegularHistory S | ∀ j : Fin k, h.position (t j.succ) = y j} =
      {h | ∀ i : Fin (k + 1), 0 < i → h.position (t i) = (Fin.cons x y : Fin (k + 1) → S) i} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    rw [Fin.forall_fin_succ]
    simp only [Fin.succ_pos, forall_const, Fin.cons_succ]
    constructor
    · intro hh
      exact ⟨fun hi => absurd hi (lt_irrefl _), hh⟩
    · exact fun hh => hh.2
  simp_rw [hset]
  have hform : ∀ ω, (r ω).regularLaw (Measure.dirac x)
      {h | ∀ i : Fin (k + 1), 0 < i → h.position (t i) = (Fin.cons x y : Fin (k + 1) → S) i} =
      ∑' x₀, Measure.dirac x {x₀} * ∏ i : Fin k,
        (r ω).transitionKernel (t i.succ - t i.castSucc)
          (Function.update (Fin.cons x y : Fin (k + 1) → S) 0 x₀ i.castSucc)
          {Function.update (Fin.cons x y : Fin (k + 1) → S) 0 x₀ i.succ} :=
    fun ω => (r ω).regularLaw_position_fdd (Measure.dirac x) k t ht ht0 _
  simp_rw [hform]
  exact Measurable.tsum fun x₀ => measurable_const.mul
    (Finset.measurable_prod _ fun i _ => measurable_transitionKernel_singleton hq hR _ _ _)

theorem measurable_regularLaw_cylinder (hq : ∀ i j, Measurable fun ω => (r ω).q i j)
    (hR : ∀ ω, (r ω).R = R) (x : S) (F : Finset ℝ≥0) (B : ℝ≥0 → Set S) :
    Measurable fun ω => (r ω).regularLaw (Measure.dirac x)
      {h | ∀ s ∈ F, h.position s ∈ B s} := by
  classical
  set G : Finset ℝ≥0 := insert 0 F with hG
  set B' : ℝ≥0 → Set S := fun s => if s ∈ F then B s else Set.univ with hB'
  obtain ⟨k, hk⟩ : ∃ k, G.card = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨0, Finset.mem_insert_self _ _⟩)
  set t : Fin (k + 1) ↪o ℝ≥0 := G.orderEmbOfFin hk with ht
  have hmem : ∀ i, t i ∈ G := fun i => G.orderEmbOfFin_mem hk i
  have hex : ∀ s ∈ G, ∃ i, t i = s := by
    intro s hs
    have : s ∈ Set.range t := by rw [ht, Finset.range_orderEmbOfFin]; exact hs
    exact this
  have ht0 : t 0 = 0 := by
    obtain ⟨i, hi⟩ := hex 0 (Finset.mem_insert_self _ _)
    exact le_antisymm (hi ▸ t.monotone (Fin.zero_le i)) bot_le
  have hevent : {h : RegularHistory S | ∀ s ∈ F, h.position s ∈ B s} =
      {h | ∀ i : Fin (k + 1), h.position (t i) ∈ B' (t i)} := by
    ext h
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hh i
      by_cases hi : t i ∈ F
      · simpa only [hB', hi, ↓reduceIte] using hh _ hi
      · simp only [hB', hi, ↓reduceIte, Set.mem_univ]
    · intro hh s hs
      obtain ⟨i, hi⟩ := hex s (Finset.mem_insert_of_mem hs)
      have := hh i
      simpa only [hB', hi, hs, ↓reduceIte] using this
  have hae : ∀ ω, (r ω).regularLaw (Measure.dirac x)
      ((fun h : RegularHistory S => h.position 0) ⁻¹' {x})ᶜ = 0 := by
    intro ω
    have := (r ω).regularLaw_map_position_zero (Measure.dirac x)
    have h2 := congrArg (fun ν : Measure S => ν {x}ᶜ) this
    simp only [Measure.dirac_apply' _ (measurableSet_singleton x).compl] at h2
    rw [Measure.map_apply (RegularHistory.measurable_position 0)
      (measurableSet_singleton x).compl, Set.indicator_of_notMem (by simp)] at h2
    rw [← Set.preimage_compl]
    exact h2
  simp_rw [hevent]
  set T : Set (RegularHistory S) := (fun h : RegularHistory S => h.position 0) ⁻¹' {x} with hT
  set E' : Set (RegularHistory S) :=
    {h | ∀ j : Fin k, h.position (t j.succ) ∈ B' (t j.succ)} with hE'
  set E : Set (RegularHistory S) := {h | ∀ i : Fin (k + 1), h.position (t i) ∈ B' (t i)} with hE
  have hET : ∀ ω, (r ω).regularLaw (Measure.dirac x) E =
      (r ω).regularLaw (Measure.dirac x) (E ∩ T) := fun ω =>
    (measure_inter_conull (hae ω)).symm
  by_cases hx : x ∈ B' 0
  · have hEE : ∀ ω, (r ω).regularLaw (Measure.dirac x) E =
        (r ω).regularLaw (Measure.dirac x) E' := by
      intro ω
      rw [hET ω, ← measure_inter_conull (s := E') (hae ω)]
      congr 1
      ext h
      simp only [hE, hE', hT, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        Set.mem_singleton_iff, Fin.forall_fin_succ, ht0]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        exact ⟨⟨h3 ▸ hx, h2⟩, h3⟩
    simp_rw [hEE]
    set Y : Set (Fin k → S) := {y | ∀ j, y j ∈ B' (t j.succ)} with hY
    have hU : E' = ⋃ y ∈ Y, {h : RegularHistory S | ∀ j : Fin k, h.position (t j.succ) = y j} := by
      ext h
      simp only [hE', hY, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      constructor
      · intro hh
        exact ⟨fun j => h.position (t j.succ), hh, fun j => rfl⟩
      · rintro ⟨y, hy, hh⟩ j
        rw [hh j]
        exact hy j
    have hmeas : ∀ y : Fin k → S,
        MeasurableSet {h : RegularHistory S | ∀ j : Fin k, h.position (t j.succ) = y j} := by
      intro y
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j =>
        (RegularHistory.measurable_position _) (measurableSet_singleton _)
    have hdisj : Y.PairwiseDisjoint
        (fun y : Fin k → S => {h : RegularHistory S | ∀ j : Fin k, h.position (t j.succ) = y j}) := by
      intro y _ y' _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro h hh hh'
      apply hne
      funext j
      rw [← hh j, ← hh' j]
    have hsum : ∀ ω, (r ω).regularLaw (Measure.dirac x) E' = ∑' y : Y,
        (r ω).regularLaw (Measure.dirac x)
          {h : RegularHistory S | ∀ j : Fin k, h.position (t j.succ) = (y : Fin k → S) j} := by
      intro ω
      rw [hU]
      exact measure_biUnion (Set.to_countable Y) hdisj fun y _ => hmeas y
    simp_rw [hsum]
    exact Measurable.tsum fun y => measurable_regularLaw_fdd hq hR x t t.monotone ht0 y
  · have hz : ∀ ω, (r ω).regularLaw (Measure.dirac x) E = 0 := by
      intro ω
      rw [hET ω]
      have : E ∩ T = ∅ := by
        ext h
        simp only [hE, hT, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
          Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hh h0
        have := hh 0
        rw [ht0, h0] at this
        exact hx this
      rw [this, measure_empty]
    simp_rw [hz]
    exact measurable_const

end

end LongRangeHeat
