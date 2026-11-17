import LongRangeHeat.FddGaussian
import LongRangeHeat.FddChain
import LongRangeHeat.FddAlgebra

/-!
# Products of observations of a sum of independent Gaussian steps

For independent centered Gaussian vectors `D_0, …, D_{k-1}` in `ℝ^d` with independent coordinates
of variances `s_0, …, s_{k-1}`, the partial sums `S_u = D_0 + ⋯ + D_u` satisfy
`E[∏_u ψ_u(x + d^{-1/2} S_u)] = contExp k s ψ x`, the backward recursion with the heat flow
`P̄_{s_u}` (`integral_prod_gaussian_steps`). This is the Markov property of Brownian motion for
finitely many times.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff

noncomputable section

variable {d : ℕ}

/-- The partial sums `D_0 + ⋯ + D_u` of a family of vectors. -/
def cumSum {k : ℕ} (D : Fin k → Fin d → ℝ) (u : Fin k) : Fin d → ℝ :=
  ∑ v : Fin k, if v ≤ u then D v else 0

theorem cumSum_zero {k : ℕ} (D : Fin (k + 1) → Fin d → ℝ) : cumSum D 0 = D 0 := by
  rw [cumSum, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

theorem cumSum_succ {k : ℕ} (D : Fin (k + 1) → Fin d → ℝ) (u : Fin k) :
    cumSum D u.succ = D 0 + cumSum (fun v => D v.succ) u := by
  rw [cumSum, Fin.sum_univ_succ]
  simp [cumSum, Fin.succ_le_succ_iff]

/-- The backward recursion `E[∏ g_u(X_{t_u})] = e^{s_0 Δ}(g_0 e^{s_1 Δ}(g_1 ⋯))` in the continuum,
with the empty product equal to `1`. -/
def contExp {d : ℕ} : (k : ℕ) → (Fin k → ℝ≥0) → (Fin k → (Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ
  | 0, _, _ => fun _ => 1
  | k + 1, s, g =>
      continuumHeat (fun y => g 0 y * contExp k (Fin.tail s) (Fin.tail g) y) ((s 0 : ℝ≥0) : ℝ)

theorem contExp_contDiff (hd : 1 ≤ d) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin k → (Fin d → ℝ) → ℝ),
      (∀ u, IsTestFunction (g u)) → ContDiff ℝ ∞ (contExp k s g)
  | 0, s, g, _ => contDiff_const
  | k + 1, s, g, hg => by
      have ih := contExp_contDiff hd k (Fin.tail s) (Fin.tail g) fun u => hg u.succ
      exact contDiff_continuumHeat hd ((hg 0).1.mul ih)
        ((hg 0).2.mul_right) (s 0).2

theorem abs_contExp_le (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (g : Fin k → (Fin d → ℝ) → ℝ),
      (∀ u, IsTestFunction (g u)) → (∀ u y, |g u y| ≤ M) → ∀ x, |contExp k s g x| ≤ M ^ k
  | 0, s, g, _, _, x => by simp [contExp]
  | k + 1, s, g, hg, hgM, x => by
      have ih := abs_contExp_le hd hM k (Fin.tail s) (Fin.tail g) (fun u => hg u.succ)
        (fun u => hgM u.succ)
      have hc : Continuous fun y => g 0 y * contExp k (Fin.tail s) (Fin.tail g) y :=
        ((hg 0).1.continuous).mul
          (contExp_contDiff hd k (Fin.tail s) (Fin.tail g) fun u => hg u.succ).continuous
      have hb : ∀ y, |g 0 y * contExp k (Fin.tail s) (Fin.tail g) y| ≤ M ^ (k + 1) := fun y => by
        rw [abs_mul, pow_succ']
        exact mul_le_mul (hgM 0 y) (ih y) (abs_nonneg _) hM
      exact abs_continuumHeat_le hd hc hb (s 0).2 x

/-- The recursion `contExp` is the function `F̄_0` of the proof of Proposition 4.3. -/
theorem mul_contExp_eq_continuumChain {d : ℕ} :
    ∀ (m : ℕ) (s : Fin m → ℝ≥0) (g : Fin (m + 1) → (Fin d → ℝ) → ℝ),
      (fun y => g 0 y * contExp m s (Fin.tail g) y) = continuumChain m s g
  | 0, s, g => by
      funext y
      simp [contExp, continuumChain]
  | m + 1, s, g => by
      funext y
      have ih := mul_contExp_eq_continuumChain m (Fin.tail s) (Fin.tail g)
      show g 0 y * continuumHeat (fun y' => Fin.tail g 0 y' *
        contExp m (Fin.tail s) (Fin.tail (Fin.tail g)) y') ((s 0 : ℝ≥0) : ℝ) y = _
      rw [ih]
      rfl

theorem measurable_cumSum {k : ℕ} (u : Fin k) :
    Measurable fun y : Fin k → Fin d → ℝ => cumSum y u := by
  unfold cumSum
  refine Finset.measurable_sum _ fun v _ => ?_
  by_cases h : v ≤ u
  · simpa [h] using measurable_pi_apply v
  · simp [h]

/-- The first step is independent of the others. -/
theorem indepFun_first_rest {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {k : ℕ}
    {f : Fin d × Fin (k + 1) → Ω' → ℝ} (hf : iIndepFun f P') (hm : ∀ p, Measurable (f p)) :
    IndepFun (fun w (i : Fin d) => f (i, 0) w)
      (fun w (v : Fin k) (i : Fin d) => f (i, v.succ) w) P' := by
  classical
  let S : Finset (Fin d × Fin (k + 1)) := Finset.univ.filter fun p => p.2 = 0
  let T : Finset (Fin d × Fin (k + 1)) := Finset.univ.filter fun p => p.2 ≠ 0
  have hST : Disjoint S T := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact h2 h1
  have h := hf.indepFun_finset S T hST hm
  have e1 : Measurable (fun (a : S → ℝ) (i : Fin d) => a ⟨(i, 0), by simp [S]⟩) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have e2 : Measurable
      (fun (b : T → ℝ) (v : Fin k) (i : Fin d) => b ⟨(i, v.succ), by simp [T]⟩) :=
    measurable_pi_iff.mpr fun v => measurable_pi_iff.mpr fun i => measurable_pi_apply _
  exact h.comp e1 e2

/-- **The Markov property of Brownian motion at finitely many times**, for independent Gaussian
steps: `E[∏_u ψ_u(x + d^{-1/2} (D_0 + ⋯ + D_u))] = contExp k s ψ x`. -/
theorem integral_prod_gaussian_steps (hd : 1 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    ∀ (k : ℕ) (s : Fin k → ℝ≥0) (ψ : Fin k → (Fin d → ℝ) → ℝ), (∀ u, IsTestFunction (ψ u)) →
      (∀ u y, |ψ u y| ≤ M) → ∀ (x : Fin d → ℝ) {Ω' : Type*} [MeasurableSpace Ω']
        (P' : Measure Ω') [IsProbabilityMeasure P'] (D : Fin k → Ω' → Fin d → ℝ),
        (∀ v i, Measurable fun w => D v w i) →
        iIndepFun (fun (p : Fin d × Fin k) w => D p.2 w p.1) P' →
        (∀ v i, HasLaw (fun w => D v w i) (gaussianReal 0 (s v)) P') →
        ∫ w, ∏ u, ψ u (x + ((d : ℝ) ^ (-(1 : ℝ) / 2)) • cumSum (fun v => D v w) u) ∂P' =
          contExp k s ψ x
  | 0, s, ψ, _, _, x, Ω', _, P', _, D, _, _, _ => by simp [contExp]
  | k + 1, s, ψ, hψ, hψM, x, Ω', _, P', _, D, hm, hind, hlaw => by
      set c : ℝ := (d : ℝ) ^ (-(1 : ℝ) / 2) with hc
      have hind0 := indepFun_first_rest
        (f := fun (p : Fin d × Fin (k + 1)) w => D p.2 w p.1) hind (fun p => hm p.2 p.1)
      have hX0m : Measurable fun w => D 0 w := measurable_pi_iff.mpr fun i => hm 0 i
      have hYm : Measurable fun w (v : Fin k) => D v.succ w :=
        measurable_pi_iff.mpr fun v => measurable_pi_iff.mpr fun i => hm v.succ i
      set F : (Fin d → ℝ) × (Fin k → Fin d → ℝ) → ℝ := fun p =>
        ψ 0 (x + c • p.1) * ∏ u : Fin k, ψ u.succ ((x + c • p.1) + c • cumSum p.2 u) with hF
      have hint_eq : ∀ w, ∏ u : Fin (k + 1), ψ u (x + c • cumSum (fun v => D v w) u) =
          F (D 0 w, fun v => D v.succ w) := by
        intro w
        rw [Fin.prod_univ_succ]
        simp only [hF, cumSum_zero]
        congr 1
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [cumSum_succ, smul_add, add_assoc]
      simp_rw [hint_eq]
      have hFm : Measurable F := by
        refine Measurable.mul ?_ (Finset.measurable_prod _ fun u _ => ?_)
        · exact (hψ 0).1.continuous.measurable.comp
            (measurable_const.add (measurable_const_smul c |>.comp measurable_fst))
        · exact (hψ u.succ).1.continuous.measurable.comp
            ((measurable_const.add (measurable_const_smul c |>.comp measurable_fst)).add
              (measurable_const_smul c |>.comp ((measurable_cumSum u).comp measurable_snd)))
      have hFb : ∀ p, |F p| ≤ M ^ (k + 1) := fun p => by
        rw [hF, abs_mul, Finset.abs_prod, pow_succ']
        exact mul_le_mul (hψM 0 _) (by
          calc ∏ u : Fin k, |ψ u.succ _| ≤ ∏ _u : Fin k, M :=
                Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun u _ => hψM u.succ _
            _ = M ^ k := by simp) (Finset.prod_nonneg fun _ _ => abs_nonneg _) hM
      have hmapj : P'.map (fun w => (D 0 w, fun v : Fin k => D v.succ w)) =
          (P'.map fun w => D 0 w).prod (P'.map fun (w : Ω') (v : Fin k) => D v.succ w) :=
        (indepFun_iff_map_prod_eq_prod_map_map hX0m.aemeasurable hYm.aemeasurable).1 hind0
      have hFi : Integrable F ((P'.map fun w => D 0 w).prod (P'.map fun (w : Ω') (v : Fin k) => D v.succ w)) := by
        have : IsProbabilityMeasure ((P'.map fun w => D 0 w).prod (P'.map fun (w : Ω') (v : Fin k) => D v.succ w)) :=
          by
            rw [← hmapj]
            infer_instance
        exact Integrable.of_bound hFm.aestronglyMeasurable (M ^ (k + 1))
          (Filter.Eventually.of_forall fun p => by simpa using hFb p)
      rw [← integral_map (hX0m.prodMk hYm).aemeasurable hFm.aestronglyMeasurable, hmapj,
        integral_prod F hFi]
      -- inner integral
      have hdep := fun (z : Fin d → ℝ) =>
        integral_prod_gaussian_steps hd hM k (Fin.tail s) (Fin.tail ψ) (fun u => hψ u.succ)
          (fun u y => hψM u.succ y) (x + c • z) (P' := P') (fun (v : Fin k) w => D v.succ w)
          (fun (v : Fin k) (i : Fin d) => hm v.succ i)
          (hind.precomp (g := fun p : Fin d × Fin k => (p.1, p.2.succ))
            (fun p q hpq => by
              simp only [Prod.mk.injEq] at hpq
              exact Prod.ext hpq.1 (Fin.succ_injective _ hpq.2)))
          (fun (v : Fin k) (i : Fin d) => hlaw v.succ i)
      have hinner : ∀ z : Fin d → ℝ, ∫ y, F (z, y) ∂(P'.map fun (w : Ω') (v : Fin k) => D v.succ w) =
          ψ 0 (x + c • z) * contExp k (Fin.tail s) (Fin.tail ψ) (x + c • z) := by
        intro z
        have h1 : ∀ y, F (z, y) = ψ 0 (x + c • z) *
            ∏ u : Fin k, ψ u.succ ((x + c • z) + c • cumSum y u) := fun y => rfl
        simp_rw [h1]
        rw [integral_const_mul, integral_map hYm.aemeasurable]
        · congr 1
          exact hdep z
        · refine (Finset.measurable_prod _ fun u _ => ?_).aestronglyMeasurable
          exact (hψ u.succ).1.continuous.measurable.comp
            (measurable_const.add (measurable_const_smul c |>.comp (measurable_cumSum u)))
      simp_rw [hinner]
      -- the first step
      have hind00 : iIndepFun (fun (i : Fin d) w => D 0 w i) P' :=
        hind.precomp (g := fun i : Fin d => (i, (0 : Fin (k + 1))))
          (fun i j hij => by simpa using hij)
      have hX0law : P'.map (fun w => D 0 w) =
          Measure.pi (fun _ : Fin d => gaussianReal 0 (s 0)) := by
        rw [hind00.map_fun_eq_pi_map fun i => (hm 0 i).aemeasurable]
        congr 1
        funext i
        exact (hlaw 0 i).map_eq
      rw [hX0law]
      have hG : Continuous fun y => ψ 0 y * contExp k (Fin.tail s) (Fin.tail ψ) y :=
        (hψ 0).1.continuous.mul
          (contExp_contDiff hd k (Fin.tail s) (Fin.tail ψ) fun u => hψ u.succ).continuous
      exact integral_pi_gaussian_eq_continuumHeat hd hG x

end

end LongRangeHeat

