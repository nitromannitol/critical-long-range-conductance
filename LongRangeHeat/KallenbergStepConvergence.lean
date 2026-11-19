import LongRangeHeat.KallenbergStepApproximation

/-!
# Convergence of finite step paths

Step paths converge when their distinct cuts and values converge.
-/

namespace LatticeProb.Cadlag.HalfLine

open Filter
open scoped Topology ENNReal NNReal

/-- Step paths with converging distinct cuts and fixed values converge in the
half-line Skorokhod metric. The first cut is fixed at zero. -/
theorem tendsto_stepPath_of_cuts {E : Type*} [MetricSpace E] (N : ℕ)
    (s : Fin (N + 1) → Time) (r : ℕ → Fin (N + 1) → Time)
    (v : Fin (N + 2) → E) (hs : Function.Injective s) (hszero : s 0 = 0)
    (hrzero : ∀ n, r n 0 = 0)
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 (s i))) :
    Tendsto (fun n => stepPath (r n) v) atTop (𝓝 (stepPath s v)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let a : ℝ := ε / 4
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds ha))
  let T : Time := ⟨max R 0, le_max_right _ _⟩
  have htail : Real.exp (-(T : ℝ)) < a := hR _ (le_max_left _ _)
  let B : ℝ≥0 := ⟨a / (N + 2 : ℝ), div_nonneg ha.le (by positivity)⟩
  have hB : 0 < (B : ℝ) := by
    change 0 < a / (N + 2 : ℝ)
    exact div_pos ha (by positivity)
  filter_upwards [eventually_exists_small_timeChange_interpolating_knots
    N s r B ha hB hs hszero hrzero hr] with n hn
  obtain ⟨l, hl, hmove, halign⟩ := hn
  have hcard : ((Finset.univ.image s).card : ℝ) * (B : ℝ) ≤ a := by
    have hc : ((Finset.univ.image s).card : ℝ) ≤ N + 1 := by
      exact_mod_cast (show (Finset.univ.image s).card ≤ N + 1 by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Finset.card_image_le : (Finset.univ.image s).card ≤ Finset.univ.card))
    change ((Finset.univ.image s).card : ℝ) * (a / (N + 2 : ℝ)) ≤ a
    have hden : 0 < (N + 2 : ℝ) := by positivity
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) ha.le]
  have hd := skorohodDistanceExtended_le_of_step_approximations
    (stepPath s v) (stepPath (r n) v) (N + 1) s v l T B 0 0
    (fun i => hmove (s i))
    (fun t _ => by simp only [stepPath, dist_self, le_refl])
    (fun t _ => by simpa only [stepPath, halign, dist_self] using (le_refl (0 : ℝ)))
  have hcard' : (Finset.univ.image s).card * ENNReal.ofReal B ≤ ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hcard
  have hbound : skorohodDistanceExtended (stepPath s v) (stepPath (r n) v) ≤
      ENNReal.ofReal (2 * a) := by
    apply hd.trans
    simp only [zero_add, ENNReal.ofReal_zero]
    apply max_le
    · exact hl.trans (ENNReal.ofReal_le_ofReal (by linarith))
    · calc
        _ ≤ ENNReal.ofReal a + ENNReal.ofReal a :=
          add_le_add hcard' (ENNReal.ofReal_le_ofReal htail.le)
        _ = ENNReal.ofReal (2 * a) := by
          rw [← ENNReal.ofReal_add ha.le ha.le]
          congr 1
          ring
  have hdreal := ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 2 * a) hbound
  rw [dist_comm]
  exact hdreal.trans_lt (by dsimp only [a]; linarith)

/-- Step paths converge jointly in their distinct cuts and their values. -/
theorem tendsto_stepPath_of_cuts_and_values {E : Type*} [MetricSpace E] (N : ℕ)
    (s : Fin (N + 1) → Time) (r : ℕ → Fin (N + 1) → Time)
    (v : Fin (N + 2) → E) (w : ℕ → Fin (N + 2) → E)
    (hs : Function.Injective s) (hszero : s 0 = 0)
    (hrzero : ∀ n, r n 0 = 0)
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 (s i)))
    (hw : Tendsto w atTop (𝓝 v)) :
    Tendsto (fun n => stepPath (r n) (w n)) atTop (𝓝 (stepPath s v)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp
    (tendsto_stepPath_of_cuts N s r v hs hszero hrzero hr) (ε / 2) he,
    Metric.tendsto_nhds.mp hw (ε / 2) he] with n hcuts hvalues
  calc
    dist (stepPath (r n) (w n)) (stepPath s v) ≤
        dist (stepPath (r n) (w n)) (stepPath (r n) v) +
          dist (stepPath (r n) v) (stepPath s v) := dist_triangle _ _ _
    _ ≤ dist (w n) v + dist (stepPath (r n) v) (stepPath s v) :=
      add_le_add (dist_stepPath_le (r n) (w n) v) le_rfl
    _ < ε := by linarith

/-- Adding a cut at zero with the same initial value leaves a step path
unchanged. -/
theorem stepPath_cons_zero {E : Type*} [MetricSpace E] {N : ℕ}
    (s : Fin N → Time) (v : Fin (N + 1) → E) :
    stepPath (Fin.cons 0 s) (Fin.cons (v 0) v) = stepPath s v := by
  apply Subtype.ext
  funext t
  change (Fin.cons (v 0) v : Fin (N + 2) → E) (stepIndex (Fin.cons 0 s) t) =
    v (stepIndex s t)
  simp only [stepIndex, Fin.cons_zero, not_lt_of_ge zero_le, ite_false, Fin.cons_succ]

/-- Step paths converge jointly in their positive distinct cuts and values. -/
theorem tendsto_stepPath_of_positive_cuts_and_values {E : Type*} [MetricSpace E]
    (N : ℕ) (s : Fin N → Time) (r : ℕ → Fin N → Time)
    (v : Fin (N + 1) → E) (w : ℕ → Fin (N + 1) → E)
    (hs : Function.Injective s) (hspos : ∀ i, 0 < s i)
    (hr : ∀ i, Tendsto (fun n => r n i) atTop (𝓝 (s i)))
    (hw : Tendsto w atTop (𝓝 v)) :
    Tendsto (fun n => stepPath (r n) (w n)) atTop (𝓝 (stepPath s v)) := by
  have hs' : Function.Injective (Fin.cons 0 s) := by
    apply Fin.cons_injective_of_injective _ hs
    rintro ⟨i, hi⟩
    exact (ne_of_gt (hspos i)) hi
  have hr' : ∀ i : Fin (N + 1), Tendsto (fun n => (Fin.cons 0 (r n) : Fin (N + 1) → Time) i) atTop
      (𝓝 ((Fin.cons 0 s : Fin (N + 1) → Time) i)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : Time)) atTop (𝓝 0))
    · simpa only [Fin.cons_succ] using hr j
  have hw' : Tendsto (fun n => (Fin.cons (w n 0) (w n) : Fin (N + 2) → E)) atTop
      (𝓝 (Fin.cons (v 0) v : Fin (N + 2) → E)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using (tendsto_pi_nhds.mp hw 0)
    · simpa only [Fin.cons_succ] using (tendsto_pi_nhds.mp hw j)
  simpa only [stepPath_cons_zero] using
    (tendsto_stepPath_of_cuts_and_values N (Fin.cons 0 s) (fun n => Fin.cons 0 (r n))
      (Fin.cons (v 0) v) (fun n => Fin.cons (w n 0) (w n)) hs'
      (Fin.cons_zero _ _) (fun n => Fin.cons_zero _ _) hr' hw')

end LatticeProb.Cadlag.HalfLine
