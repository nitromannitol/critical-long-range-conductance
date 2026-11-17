import LongRangeHeat.FddTight
import LongRangeHeat.FddWeak
import LatticeProb.Prob.BrownianPathSpace

/-!
# Weak convergence of the finite-dimensional marginals

The law of `(X^ε_{t_1}, …, X^ε_{t_k})` under the annealed measure is tight
(`isTightMeasureSet_fddLaw`), and for every set of indices `S` and test functions `ψ_j` the
integral of `∏_{j ∈ S} ψ_j(x_j)` converges to the corresponding Brownian integral
(`tendsto_integral_chainExp`, and the Markov property of the limit as the hypothesis `hbrown`).
By `tendsto_of_tight_of_subProd` the laws converge weakly.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory LatticeProb LatticeProb.Euclidean.Lattice Set Filter
open scoped NNReal ENNReal Topology
open LongRange (Edge walkRates walkEmbed)

noncomputable section

variable {d : ℕ}

/-- The law of `d^{-1/2} (W_{t_1}, …, W_{t_k})` for a Brownian law `B`. -/
def brownianFdd (B : ProbabilityMeasure (BrownianPath d)) {k : ℕ} (t : Fin k → ℝ≥0) :
    ProbabilityMeasure (Fin k → EuclideanSpace ℝ (Fin d)) :=
  ProbabilityMeasure.map B fun ω j => ((d : ℝ) ^ (-(1 : ℝ) / 2)) • ω (t j)

theorem measurable_brownianEval {k : ℕ} (t : Fin k → ℝ≥0) (c : ℝ) :
    Measurable fun (ω : BrownianPath d) (j : Fin k) => c • ω (t j) :=
  (continuous_pi fun j => (continuous_eval_const (t j)).const_smul c).measurable

theorem prod_orderEmbOfFin {k n : ℕ} (S : Finset (Fin k)) (h : S.card = n) (f : Fin k → ℝ) :
    ∏ j ∈ S, f j = ∏ u : Fin n, f (S.orderEmbOfFin h u) := by
  have himg : Finset.univ.image (S.orderEmbOfFin h) = S := by
    ext j
    constructor
    · intro hj
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hj
      exact S.orderEmbOfFin_mem h u
    · intro hj
      have : j ∈ Set.range (S.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hj
      obtain ⟨u, rfl⟩ := this
      exact Finset.mem_image_of_mem _ (Finset.mem_univ u)
  calc ∏ j ∈ S, f j = ∏ j ∈ Finset.univ.image (S.orderEmbOfFin h), f j :=
        Finset.prod_congr himg.symm fun _ _ => rfl
    _ = _ := Finset.prod_image fun x _ y _ hxy => (S.orderEmbOfFin h).injective hxy

/-- **Weak convergence of the finite-dimensional marginals**, from the Brownian Markov
identity `hbrown`. -/
theorem tendsto_fddLaw
    (hMSC : LatticeProb.External.MuruganSaloffCosteUniform)
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
  refine tendsto_of_tight_of_subProd (isTightMeasureSet_fddLaw hMSC hNash hDavies hd P a hP t ε hε)
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
    exact tendsto_integral_chainExp hMSC hNash hDavies hd P a hP hM0 (t ∘ e) hts
      (fun u => (hψ (e u)).1) (fun u => (hψ (e u)).2) hgM ε hε hε0

end

end LongRangeHeat
