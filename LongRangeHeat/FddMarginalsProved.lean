import LongRangeHeat.FddMarginals
import LongRangeHeat.FddTightProved
import LongRangeHeat.FddLimitProved

/-!
# Convergence of finite-dimensional distributions

Tightness and convergence of products imply weak convergence of the marginals.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Euclidean.Lattice Set Filter
open scoped NNReal ENNReal Topology
open LongRange (Edge walkRates walkEmbed)

noncomputable section

variable {d : ℕ}

theorem tendsto_fddLaw_proved
    (hNash : LatticeProb.External.ChenKimKumagaiWangNash)
    (hDavies : LatticeProb.External.ChenKimKumagaiWangDavies)
    (hd : 1 ≤ d) {lam : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (a : Ω → Edge d → ℝ) (hP : ConductanceLaw P lam a) {k : ℕ} (t : Fin k → ℝ≥0)
    (ht : StrictMono t) (B : ProbabilityMeasure (BrownianPath d))
    (hbrown : ∀ (m : ℕ) (t' : Fin (m + 1) → ℝ≥0) (ψ : Fin (m + 1) → (Fin d → ℝ) → ℝ),
      StrictMono t' → (∀ u, IsTestFunction (ψ u)) →
        ∫ ω : BrownianPath d, ∏ u, ψ u (WithLp.ofLp (((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t' u))) ∂(B : Measure _) =
          continuumHeat (continuumChain m (gaps t') ψ) ((t' 0 : ℝ≥0) : ℝ) 0)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ i, ε i ∈ Ioo (0 : ℝ) (1 / 2))
    (hε0 : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => fddLaw hd P a hP (hε i).1 t) l (𝓝 (brownianFdd B t)) := by
  have hPm := hP.isProbabilityMeasure
  refine tendsto_of_tight_of_subProd (isTightMeasureSet_fddLaw_proved hNash hDavies hd P a hP t ε hε)
    fun S ψ hψ => ?_
  have hcont := continuous_subProd S hψ
  have hint : ∀ i, ∫ x, subProd S ψ x ∂(fddLaw hd P a hP (hε i).1 t : Measure _) =
      ∫ X, subProd S ψ (pathEval t X) ∂(annealedLaw hd P a hP (hε i).1 : Measure (PathSpace d)) :=
    fun i => integral_map (measurable_pathEval t).aemeasurable hcont.aestronglyMeasurable
  have hlim : ∫ x, subProd S ψ x ∂(brownianFdd B t : Measure _) =
      ∫ ω : BrownianPath d, subProd S ψ (fun j => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t j)) ∂(B : Measure _) :=
    integral_map (measurable_brownianEval t _).aemeasurable hcont.aestronglyMeasurable
  simp_rw [hint, hlim]
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [subProd, Finset.prod_empty, integral_const, probReal_univ, one_smul]
    exact tendsto_const_nhds
  · obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
      ⟨S.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 hne)).symm⟩
    set e := S.orderEmbOfFin hm with he
    have hts : StrictMono (t ∘ e) := ht.comp e.strictMono
    choose B₀ hB₀ using fun j => exists_bound_testFunction (hψ j)
    set M : ℝ := ∑ u : Fin (m + 1), B₀ (e u) with hM
    have hBnn : ∀ u, 0 ≤ B₀ (e u) := fun u => (abs_nonneg _).trans (hB₀ (e u) 0)
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun u _ => hBnn u
    have hgM : ∀ u y, |ψ (e u) y| ≤ M := fun u y =>
      (hB₀ (e u) y).trans (Finset.single_le_sum (f := fun u => B₀ (e u))
        (fun u _ => hBnn u) (Finset.mem_univ u))
    have hprod : ∀ X : PathSpace d, subProd S ψ (pathEval t X) =
        pathProd (t ∘ e) (fun u => ψ (e u)) X := fun X => by
      simp only [subProd, pathProd, pathEval, Function.comp]
      exact prod_orderEmbOfFin S hm (fun j => ψ j (WithLp.ofLp (X.1 (t j))))
    have hprodB : ∀ ω : BrownianPath d,
        subProd S ψ (fun j => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t j)) =
          ∏ u, ψ (e u) (WithLp.ofLp (((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t (e u)))) := fun ω =>
      prod_orderEmbOfFin S hm (fun j => ψ j (WithLp.ofLp (((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t j))))
    simp_rw [hprod, hprodB]
    have hb : ∫ ω : BrownianPath d, ∏ u, ψ (e u)
        (WithLp.ofLp (((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t (e u)))) ∂(B : Measure _) =
        continuumHeat (continuumChain m (gaps (t ∘ e)) (fun u => ψ (e u))) (((t ∘ e) 0 : ℝ≥0) : ℝ)
          0 := hbrown m (t ∘ e) (fun u => ψ (e u)) hts fun u => hψ (e u)
    rw [hb]
    have hann : ∀ i, ∫ X, pathProd (t ∘ e) (fun u => ψ (e u)) X
        ∂(annealedLaw hd P a hP (hε i).1 : Measure (PathSpace d)) =
        ∫ r, chainExp (walkRates hd (hε i).1 hP.lam_mem.1 (a r) (hP.bounds r)) (m + 1)
          (timeIncr (t ∘ e)) (fun u => restrict (ε i) (ψ (e u))) 0 ∂P := fun i =>
      integral_annealedLaw_pathProd hd P a hP (hε i).1 (t ∘ e) hts.monotone
        (fun u => (hψ (e u)).1.continuous) hM0 hgM
    simp_rw [hann]
    exact tendsto_integral_chainExp_proved hNash hDavies hd P a hP hM0 (t ∘ e) hts
      (fun u => (hψ (e u)).1) (fun u => (hψ (e u)).2) hgM ε hε hε0

end

end LongRangeHeat
