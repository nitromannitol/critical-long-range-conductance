import LongRangeHeat.FddAnnealed
import LongRangeHeat.Statements.HeatKernelBounds

/-!
# The limit of the annealed expectation of a product of observations

Step 2 of the proof of Proposition 4.3. For `k + 1` observation times `t_0 ≤ ⋯ ≤ t_k` and
observables `g_i ∈ C_c^∞(ℝ^d)`, the annealed expectation `E^ann_0[∏ g_i(X^ε_{t_i})]` converges, as
`ε → 0`, to `P̄_{t_0} F̄_0(0)`, where `F̄_k = g_k` and `F̄_i = g_i P̄_{t_{i+1} - t_i} F̄_{i+1}`.
The first time is positive in `tendsto_integral_chainExp_of_pos`; if it vanishes, the factor
`g_0(0)` splits off (`tendsto_integral_chainExp`).
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.JumpChain
  LatticeProb.Euclidean.Lattice Set Filter
open scoped NNReal Topology ContDiff
open LongRange (Edge walkRates walkEmbed)

noncomputable section

section Times

variable {k : ℕ}

/-- The increments `t_1 - t_0, …, t_k - t_{k-1}` of the observation times. -/
def gaps (t : Fin (k + 1) → ℝ≥0) : Fin k → ℝ≥0 := fun i => t i.succ - t i.castSucc

theorem timeIncr_zero (t : Fin (k + 1) → ℝ≥0) : timeIncr t 0 = t 0 := by
  simp [timeIncr]

theorem tail_timeIncr (t : Fin (k + 1) → ℝ≥0) : Fin.tail (timeIncr t) = gaps t := by
  funext i
  show (Fin.cons 0 t : Fin (k + 1 + 1) → ℝ≥0) i.succ.succ -
    (Fin.cons 0 t : Fin (k + 1 + 1) → ℝ≥0) i.succ.castSucc = t i.succ - t i.castSucc
  rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ]

theorem physical_zero_site {d : ℕ} (ε : ℝ) : physical ε (0 : Site d) = 0 := by
  funext k
  simp [physical]

theorem tail_gaps {k : ℕ} (t : Fin (k + 2) → ℝ≥0) : Fin.tail (gaps t) = gaps (Fin.tail t) := by
  funext j
  show t j.succ.succ - t j.succ.castSucc = t j.succ.succ - t j.castSucc.succ
  rw [Fin.succ_castSucc]

theorem chainExp_succ_of_zero {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (rates : BoundedRates S) (s : Fin (k + 1) → ℝ≥0)
    (g : Fin (k + 1) → S → ℝ) (z : S) (hs : s 0 = 0) :
    chainExp rates (k + 1) s g z = g 0 z * chainExp rates k (Fin.tail s) (Fin.tail g) z := by
  rw [chainExp, hs, walkOp_zero]

end Times

section Limit

variable {d : ℕ}

/-- The annealed expectation of a product of observations at times `t_0 < ⋯`, the first of which
is positive, converges to `P̄_{t_0} F̄_0 (0)`. -/
theorem tendsto_integral_chainExp_of_pos
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {M : ℝ} (hM : 0 ≤ M) {k : ℕ}
    (t : Fin (k + 1) → ℝ≥0) (ht : Monotone t) (h0 : 0 < t 0) {g : Fin (k + 1) → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hgc : ∀ i, HasCompactSupport (g i))
    (hgM : ∀ i x, |g i x| ≤ M) {ι : Type*} {l : Filter ι} (ε : ι → ℝ)
    (hε : ∀ i, ε i ∈ Ioo (0 : ℝ) (1 / 2)) (hε0 : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => ∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
        (k + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 ∂P) l
      (𝓝 (continuumHeat (continuumChain k (gaps t) g) ((t 0 : ℝ≥0) : ℝ) 0)) := by
  have hPm := hP.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ := Statements.heat_kernel_bounds hMSC hNash hDavies hd hP.lam_mem
  obtain ⟨hFs, hFc⟩ := continuumChain_testFunction hd k (gaps t) g hg hgc
  obtain ⟨M', L, M₂, hM', hL, hM₂⟩ := exists_bounds_of_testFunction hFs hFc
  set T : ℝ≥0 := t 0 + ∑ i, gaps t i with hT
  have hgapsT : ∀ i, gaps t i ≤ T := fun i =>
    (Finset.single_le_sum (f := gaps t) (fun _ _ => bot_le) (Finset.mem_univ i)).trans
      (le_add_self)
  obtain ⟨K₁, hK₁, h₁⟩ := exists_integral_chainDefect_le hd hP.lam_mem hM T k (gaps t) g hg hgc
    hgapsT
  obtain ⟨K₂, hK₂, h₂⟩ := exists_integral_stepError_le hd hFs hFc hP.lam_mem T
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- the small time `h`
  set B : ℝ → ℝ := fun r => (L + 4 * M' * C) * r ^ ((1 : ℝ) / 3) + M₂ * r with hB
  have hBc : ContinuousAt B 0 := by
    refine ((continuousAt_const.mul (Real.continuousAt_rpow_const 0 ((1 : ℝ) / 3)
      (Or.inr (by norm_num)))).add (continuousAt_const.mul continuousAt_id))
  have hB0 : B 0 = 0 := by simp [hB]
  have ht0 : (0 : ℝ) < t 0 := by exact_mod_cast h0
  have hIoo : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) (min (t 0 : ℝ) 1) :=
    Ioo_mem_nhdsGT (lt_min ht0 one_pos)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) (min (t 0 : ℝ) 1) ∧ B r < δ / 2 :=
    hIoo.and
      ((hBc.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (by rw [hB0]; exact half_pos hδ)))
  obtain ⟨r₀, ⟨hr0, hr1⟩, hrB⟩ := hev.exists
  set h : ℝ≥0 := ⟨r₀, hr0.le⟩ with hh
  have hhr : (h : ℝ) = r₀ := rfl
  have hh0 : 0 < h := by exact_mod_cast hr0
  have hhτ : h < t 0 := by
    have := lt_of_lt_of_le hr1 (min_le_left _ _)
    exact_mod_cast this
  have hh1 : h ≤ 1 := by
    have := lt_of_lt_of_le hr1 (min_le_right _ _)
    exact_mod_cast this.le
  set A : ℝ := Real.sqrt (C / ((h + h : ℝ≥0) : ℝ) ^ ((d : ℝ) / 2)) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hE1 : ∀ᶠ i in l, ε i ≤ h + h ∧ ε i ≤ (h : ℝ) ^ ((1 : ℝ) / 3) := by
    have hpos : 0 < min (((h + h : ℝ≥0) : ℝ)) ((h : ℝ) ^ ((1 : ℝ) / 3)) :=
      lt_min (by exact_mod_cast add_pos hh0 hh0) (Real.rpow_pos_of_pos (by exact_mod_cast hh0) _)
    filter_upwards [hε0.eventually (ge_mem_nhds hpos)] with i hi
    exact ⟨by exact_mod_cast hi.trans (min_le_left _ _), hi.trans (min_le_right _ _)⟩
  have hlog : Tendsto (fun i => Real.sqrt |Real.log (ε i)|) l atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_abs_atBot_atTop.comp
      (Real.tendsto_log_nhdsGT_zero.comp
        (tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall fun i => (hε i).1⟩)))
  have hlim : Tendsto (fun i => A * ((K₁ + K₂) / Real.sqrt |Real.log (ε i)|)) l (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop hlog).const_mul A
  have hE2 := hlim.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [hE1, hE2] with i hi1 hi2
  obtain ⟨S₁, hS₁0, hS₁i, hS₁, hS₁c⟩ := h₁ Ω P a hP (ε i) (hε i)
  obtain ⟨S₂, hS₂0, hS₂i, hS₂, hS₂c⟩ := h₂ Ω P a hP (ε i) (hε i)
  have hQm := measurable_chainExp_env hd a hP.bounds hP.lam_mem.1 hP.measurable (hε i).1 t ht
    (fun j => (hg j).continuous) hM hgM
  have hQb : ∀ r, |chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
      (k + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0| ≤ M ^ (k + 1) := fun r =>
    abs_chainExp_le _ hM (k + 1) _ _ (fun j y => hgM j _) 0
  have hQi := Integrable.of_bound (hQm.aestronglyMeasurable (μ := P)) (M ^ (k + 1))
    (Eventually.of_forall fun r => by simpa using hQb r)
  have hBh : (L + 4 * M' * C) * (h : ℝ) ^ ((1 : ℝ) / 3) + M₂ * h < δ / 2 := hrB
  have hpt : ∀ r, |chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
      (k + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 -
        continuumHeat (continuumChain k (gaps t) g) ((t 0 : ℝ≥0) : ℝ) 0| ≤
      A * (S₁ r + S₂ r) + ((L + 4 * M' * C) * (h : ℝ) ^ ((1 : ℝ) / 3) + M₂ * h) := by
    intro r
    rw [chainExp_succ_eq, timeIncr_zero, tail_timeIncr]
    have hs₂ := hS₂c r (t 0 - h) (tsub_le_self.trans (le_add_of_nonneg_right bot_le))
    have key := abs_walkOp_chain_sub_le hd (hε i).1 hP.lam_mem.1 (hP.bounds r) hC.le
      (hbound (ε i) (hε i) (a r) (hP.bounds r) 0 0).1
      (hbound (ε i) (hε i) (a r) (hP.bounds r) 0 0).2 hM hg hgc hgM (hS₁c r).1 hM' hL hM₂
      (τ := t 0) (h := h) hh0 hh1 hhτ hi1.1 hi1.2 hs₂.2
    have hdef := (hS₁c r).2
    have hstep := hs₂.1
    have hmul : A * (chainDefect (ε i) (a r) M k (gaps t) g +
        stepError (ε i) (a r) (continuumChain k (gaps t) g) (t 0 - h)) ≤ A * (S₁ r + S₂ r) :=
      mul_le_mul_of_nonneg_left (add_le_add hdef hstep) hA0
    linarith
  have hrhs : Integrable (fun r => A * (S₁ r + S₂ r) +
      ((L + 4 * M' * C) * (h : ℝ) ^ ((1 : ℝ) / 3) + M₂ * h)) P :=
    ((hS₁i.add hS₂i).const_mul A).add (integrable_const _)
  have hI : |∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
      (k + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 ∂P -
        continuumHeat (continuumChain k (gaps t) g) ((t 0 : ℝ≥0) : ℝ) 0| ≤
      A * ((K₁ + K₂) / Real.sqrt |Real.log (ε i)|) +
        ((L + 4 * M' * C) * (h : ℝ) ^ ((1 : ℝ) / 3) + M₂ * h) := by
    set Q : Ω → ℝ := fun r => chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
      (k + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 with hQ
    set c : ℝ := continuumHeat (continuumChain k (gaps t) g) ((t 0 : ℝ≥0) : ℝ) 0 with hc
    have h1 : ∫ r, Q r ∂P - c = ∫ r, (Q r - c) ∂P := by
      rw [integral_sub hQi (integrable_const c)]
      simp
    rw [h1]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono (hQi.sub (integrable_const c)).abs hrhs hpt).trans ?_
    have hi12 : Integrable (fun r => A * (S₁ r + S₂ r)) P := (hS₁i.add hS₂i).const_mul A
    rw [integral_add hi12 (integrable_const _), integral_const_mul, integral_add hS₁i hS₂i]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hsum : ∫ r, S₁ r ∂P + ∫ r, S₂ r ∂P ≤ (K₁ + K₂) / Real.sqrt |Real.log (ε i)| := by
      rw [add_div]
      exact add_le_add hS₁ hS₂
    have := mul_le_mul_of_nonneg_left hsum hA0
    linarith
  rw [Real.dist_eq]
  linarith

/-- The vanishing first time: the observable `g_0` is evaluated at the starting point. -/
theorem timeIncr_tail_of_zero {k : ℕ} (t : Fin (k + 2) → ℝ≥0) (h0 : t 0 = 0) :
    timeIncr (Fin.tail t) = Fin.tail (timeIncr t) := by
  have h1 : timeIncr (Fin.tail t) = Fin.cons (t 1) (gaps (Fin.tail t)) := by
    rw [← Fin.cons_self_tail (timeIncr (Fin.tail t)), timeIncr_zero, tail_timeIncr]
    rfl
  rw [h1, tail_timeIncr]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]
    show t 1 = t (Fin.succ 0) - t (Fin.castSucc 0)
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, h0, tsub_zero]
  · rw [Fin.cons_succ]
    show t j.succ.succ - t j.castSucc.succ = t j.succ.succ - t j.succ.castSucc
    rw [Fin.succ_castSucc]

theorem tendsto_integral_chainExp
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {M : ℝ} (hM : 0 ≤ M) {k : ℕ}
    (t : Fin (k + 1) → ℝ≥0) (ht : StrictMono t) {g : Fin (k + 1) → (Fin d → ℝ) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) (hgc : ∀ i, HasCompactSupport (g i))
    (hgM : ∀ i x, |g i x| ≤ M) {ι : Type*} {l : Filter ι} (ε : ι → ℝ)
    (hε : ∀ i, ε i ∈ Ioo (0 : ℝ) (1 / 2)) (hε0 : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => ∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
        (k + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 ∂P) l
      (𝓝 (continuumHeat (continuumChain k (gaps t) g) ((t 0 : ℝ≥0) : ℝ) 0)) := by
  have hPm := hP.isProbabilityMeasure
  rcases eq_zero_or_pos (t 0) with h0 | h0
  · cases k with
    | zero =>
        have : ∀ i, ∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
            (0 + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 ∂P = g 0 0 := by
          intro i
          simp [chainExp_succ_eq, latticeChain, timeIncr_zero, h0, walkOp_zero, restrict,
            physical_zero_site]
        simp only [this]
        simp only [continuumChain, h0, NNReal.coe_zero, continuumHeat_zero]
        exact tendsto_const_nhds
    | succ k =>
        have h01 : t 0 < t 1 := ht Fin.zero_lt_one
        rw [h0] at h01
        have hpos : 0 < Fin.tail t 0 := by simpa [Fin.tail] using h01
        have hcore := tendsto_integral_chainExp_of_pos hMSC hNash hDavies hd P a hP hM (Fin.tail t)
          (fun i j hij => ht.monotone (Fin.succ_le_succ_iff.2 hij)) hpos (g := Fin.tail g)
          (fun i => hg i.succ) (fun i => hgc i.succ) (fun i x => hgM i.succ x) ε hε hε0
        have heq : ∀ i, ∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
            (k + 1 + 1) (timeIncr t) (fun j => restrict (ε i) (g j)) 0 ∂P = g 0 0 *
            ∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r))
              (k + 1) (timeIncr (Fin.tail t)) (fun j => restrict (ε i) (Fin.tail g j)) 0 ∂P := by
          intro i
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun r => ?_)
          have hz : timeIncr t 0 = 0 := by rw [timeIncr_zero]; exact h0
          dsimp only
          rw [chainExp_succ_of_zero _ (timeIncr t) _ _ hz, ← timeIncr_tail_of_zero t h0]
          have hr : restrict (ε i) (g 0) 0 = g 0 0 := by simp [restrict, physical_zero_site]
          rw [hr]
          rfl
        simp only [heq]
        convert hcore.const_mul (g 0 0) using 2
        rw [h0, NNReal.coe_zero, continuumHeat_zero]
        change g 0 0 * continuumHeat (continuumChain k (Fin.tail (gaps t)) (Fin.tail g))
          ((gaps t 0 : ℝ≥0) : ℝ) 0 = _
        rw [tail_gaps]
        have : gaps t 0 = Fin.tail t 0 := by
          show t (Fin.succ 0) - t (Fin.castSucc 0) = t (Fin.succ 0)
          simp [h0]
        rw [this]
  · exact tendsto_integral_chainExp_of_pos hMSC hNash hDavies hd P a hP hM t ht.monotone h0 hg hgc
      hgM ε hε hε0

end Limit

end

end LongRangeHeat
