import LongRangeHeat.FddGaussianChain
import LongRangeHeat.FddMarginals
import LongRangeHeat.FddLimit
import LongRangeHeat.FddWeak

/-!
# The Brownian limit of the finite-dimensional marginals

For a standard Brownian law `B` on `C(ℝ≥0, ℝ^d)` (the coordinates are independent real Brownian
motions), the increments of the coordinates between the times `0 = t_{-1} ≤ t_0 < ⋯ < t_m` are
independent centered Gaussians with the variances `t_u - t_{u-1}`. Together with the Markov property
for Gaussian steps (`integral_prod_gaussian_steps`) this gives, for test functions `ψ_u`,
`E[∏_u ψ_u(d^{-1/2} W_{t_u})] = P̄_{t_0} F̄_0(0)` (`integral_brownian_prod`).
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb Set Filter
open scoped NNReal

noncomputable section

variable {d : ℕ}

/-- The increments `W_{t'_{v+1}} - W_{t'_v}` of a path. -/
def brownianStep {m : ℕ} (t' : Fin (m + 2) → ℝ≥0) (ω : BrownianPath d) (v : Fin (m + 1)) :
    Fin d → ℝ :=
  fun i => ω (t' v.succ) i - ω (t' v.castSucc) i

theorem measurable_coord_eval (s : ℝ≥0) (i : Fin d) :
    Measurable fun ω : BrownianPath d => ω s i :=
  ((measurable_pi_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable).comp
    (continuous_eval_const s).measurable

/-- The increments of a standard Brownian motion over the intervals `[t'_v, t'_{v+1}]` are
independent in all coordinates. -/
theorem iIndepFun_brownianStep {B : Measure (BrownianPath d)} (hB : IsStandardBrownianLaw B)
    {m : ℕ} (t' : Fin (m + 2) → ℝ≥0) (ht' : Monotone t') :
    iIndepFun (fun (p : Fin d × Fin (m + 1)) (ω : BrownianPath d) => brownianStep t' ω p.2 p.1)
      B := by
  obtain ⟨hprob, hbm, hindep⟩ := hB
  have := hprob
  let V : Fin d → BrownianPath d → (Fin (m + 1) → ℝ) := fun i ω v => brownianStep t' ω v i
  have hVm : ∀ i, Measurable (V i) := fun i =>
    measurable_pi_iff.mpr fun v =>
      (measurable_coord_eval _ i).sub (measurable_coord_eval _ i)
  have hVgauss : ∀ i, HasGaussianLaw (V i) B := fun i =>
    (hbm i).isGaussianProcess.hasGaussianLaw_increments (t := t')
  have hVind : iIndepFun V B := by
    have hG : Measurable fun (f : ℝ≥0 → ℝ) (v : Fin (m + 1)) => f (t' v.succ) - f (t' v.castSucc) :=
      measurable_pi_iff.mpr fun v =>
        ((measurable_pi_apply (t' v.succ)).sub (measurable_pi_apply (t' v.castSucc)))
    exact hindep.comp (fun _ => fun f (v : Fin (m + 1)) => f (t' v.succ) - f (t' v.castSucc))
      (fun _ => hG)
  have hall : HasGaussianLaw (fun ω (p : Fin d × Fin (m + 1)) => brownianStep t' ω p.2 p.1) B := by
    have h1 := iIndepFun.hasGaussianLaw hVgauss hVind
    let L : (Fin d → Fin (m + 1) → ℝ) →L[ℝ] (Fin d × Fin (m + 1) → ℝ) :=
      ContinuousLinearMap.pi fun p =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) p.2).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin (m + 1) → ℝ) p.1)
    exact h1.map_fun L
  refine hall.iIndepFun_of_covariance_eq_zero fun p q hpq => ?_
  refine IndepFun.covariance_eq_zero ?_ ((hall.eval p).memLp_two) ((hall.eval q).memLp_two)
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    have hinc := (hbm p.1).toIsPreBrownianReal.hasIndepIncrements (m + 1) t' ht'
    have := hinc.indepFun h2
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at h1
    subst h1
    exact this
  · exact (hVind.indepFun h1).comp (measurable_pi_apply p.2) (measurable_pi_apply q.2)

/-- The increment `W^i_{t'_{v+1}} - W^i_{t'_v}` is a centered Gaussian of variance
`t'_{v+1} - t'_v`. -/
theorem hasLaw_brownianStep {B : Measure (BrownianPath d)} (hB : IsStandardBrownianLaw B) {m : ℕ}
    (t : Fin (m + 1) → ℝ≥0) (ht : Monotone t) (v : Fin (m + 1)) (i : Fin d) :
    HasLaw (fun ω : BrownianPath d => brownianStep (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) ω v i)
      (gaussianReal 0 (timeIncr t v)) B := by
  obtain ⟨hprob, hbm, _⟩ := hB
  have hle : (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) v.castSucc ≤
      (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) v.succ :=
    monotone_cons_zero ht (Fin.castSucc_le_succ v)
  have h := (hbm i).toIsPreBrownianReal.hasLaw_sub
    ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) v.succ) ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) v.castSucc)
  have hn : nndist ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) v.succ).1
      ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) v.castSucc).1 = timeIncr t v := by
    apply NNReal.coe_injective
    rw [coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hle))]
    simp only [timeIncr]
    rw [NNReal.coe_sub hle]
    rfl
  rw [hn] at h
  exact h

theorem cumSum_telescope : ∀ (m : ℕ) (F : Fin (m + 2) → Fin d → ℝ) (u : Fin (m + 1)),
    cumSum (fun v => F v.succ - F v.castSucc) u = F u.succ - F 0
  | 0, F, u => by
      have : u = 0 := Fin.cases (motive := fun u => u = 0) rfl (fun j => j.elim0) u
      subst this
      rw [cumSum_zero]
      rfl
  | m + 1, F, u => by
      refine Fin.cases ?_ (fun u' => ?_) u
      · rw [cumSum_zero]
        rfl
      · rw [cumSum_succ]
        have ih := cumSum_telescope m (fun w => F w.succ) u'
        have hfun : (fun v : Fin (m + 1) => F v.succ.succ - F v.succ.castSucc) =
            fun v => F v.succ.succ - F v.castSucc.succ := by
          funext v
          rw [Fin.succ_castSucc]
        have hfun' : (fun v : Fin (m + 1) => ((fun v : Fin (m + 2) => F v.succ - F v.castSucc) v.succ)) =
            fun v : Fin (m + 1) => F v.succ.succ - F v.castSucc.succ := by
          funext v
          show F v.succ.succ - F v.succ.castSucc = _
          rw [Fin.succ_castSucc]
        rw [hfun'] 
        rw [show (fun v : Fin (m + 1) => F v.succ.succ - F v.castSucc.succ) =
          fun v : Fin (m + 1) => (fun w : Fin (m + 2) => F w.succ) v.succ -
            (fun w : Fin (m + 2) => F w.succ) v.castSucc from rfl, ih]
        show F (Fin.succ 0) - F (Fin.castSucc 0) + (F u'.succ.succ - F (Fin.succ 0)) =
          F u'.succ.succ - F 0
        simp only [Fin.castSucc_zero]
        abel

/-- **Markov property of Brownian motion at finitely many times**: for test functions `ψ_u` and
times `t_0 ≤ ⋯ ≤ t_m`, `E[∏_u ψ_u(d^{-1/2} W_{t_u})] = P̄_{t_0} F̄_0 (0)`. -/
theorem integral_brownian_prod (hd : 1 ≤ d) {B : Measure (BrownianPath d)}
    (hB : IsStandardBrownianLaw B) {m : ℕ} (t : Fin (m + 1) → ℝ≥0) (ht : Monotone t)
    {ψ : Fin (m + 1) → (Fin d → ℝ) → ℝ} (hψ : ∀ u, IsTestFunction (ψ u)) :
    ∫ ω : BrownianPath d, ∏ u, ψ u (WithLp.ofLp (((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t u))) ∂B =
      continuumHeat (continuumChain m (gaps t) ψ) ((t 0 : ℝ≥0) : ℝ) 0 := by
  have hprob := hB.1
  have hmono : Monotone (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) := monotone_cons_zero ht
  choose Bd hBd using fun u => exists_bound_testFunction (hψ u)
  have hBnn : ∀ u, 0 ≤ Bd u := fun u => (abs_nonneg _).trans (hBd u 0)
  have hM0 : 0 ≤ ∑ u, Bd u := Finset.sum_nonneg fun u _ => hBnn u
  have hgM : ∀ u y, |ψ u y| ≤ ∑ u, Bd u := fun u y =>
    (hBd u y).trans (Finset.single_le_sum (f := Bd) (fun u _ => hBnn u) (Finset.mem_univ u))
  have hind := iIndepFun_brownianStep hB (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) hmono
  have hstep := integral_prod_gaussian_steps hd hM0 (m + 1) (timeIncr t) ψ hψ hgM 0
    (P' := B) (fun v ω => brownianStep (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) ω v)
    (fun v i => (measurable_coord_eval _ i).sub (measurable_coord_eval _ i)) hind
    (hasLaw_brownianStep hB t ht)
  have hzero : ∀ᵐ ω ∂B, ∀ i, ω 0 i = 0 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(hB.2.1 i).eval_zero_ae_eq_zero] with ω h
    exact h
  have hae : ∀ᵐ ω ∂B, ∏ u, ψ u (WithLp.ofLp (((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t u))) =
      ∏ u, ψ u (0 + ((d : ℝ) ^ (-(1 : ℝ) / 2)) • cumSum (fun v =>
        brownianStep (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) ω v) u) := by
    filter_upwards [hzero] with ω h0
    refine Finset.prod_congr rfl fun u _ => ?_
    have htel := cumSum_telescope m
      (fun s' : Fin (m + 2) => WithLp.ofLp (ω ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) s'))) u
    have hz : WithLp.ofLp (ω ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) 0)) = 0 := by
      funext i
      exact h0 i
    rw [hz, sub_zero] at htel
    have hcum : cumSum (fun v => brownianStep (Fin.cons 0 t : Fin (m + 2) → ℝ≥0) ω v) u =
        WithLp.ofLp (ω (t u)) := by
      refine htel.trans ?_
      show WithLp.ofLp (ω ((Fin.cons 0 t : Fin (m + 2) → ℝ≥0) u.succ)) = _
      rw [Fin.cons_succ]
    rw [hcum, zero_add]
    simp
  rw [integral_congr_ae hae, hstep]
  show continuumHeat (fun y => ψ 0 y * contExp m (Fin.tail (timeIncr t)) (Fin.tail ψ) y)
    ((timeIncr t 0 : ℝ≥0) : ℝ) 0 = _
  rw [mul_contExp_eq_continuumChain m (Fin.tail (timeIncr t)) ψ, tail_timeIncr, timeIncr_zero]

end

end LongRangeHeat


