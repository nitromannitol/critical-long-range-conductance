import LongRangeHeat.Forcing
import LongRangeHeat.StochasticO
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian tails of the field `G`

This file proves Lemma 3.3 (`lem:G`) of the heat-kernel version for the vector field `G` of (3.3)
built from a square-summable function `g` with an increment bound
`‖g(· + w) - g‖ ≤ K min(|εw|, 1)`: the norm `‖G‖_{L²(εℤ^d)}` satisfies `‖G‖ ≤ 𝒪₂(C K)` with `C`
depending only on `d` and `λ`.

For a fixed edge `(y, i)`, `G_i(y)` is a finite linear combination of the independent, centered
and bounded variables `a(e) - 1`; the coefficient of each edge collects the two orientations
`(x, z)` and `(x + z, -z)` of the pair. Hoeffding's lemma (`ProbabilityTheory`'s sub-Gaussian
moment generating functions) gives a Gaussian tail with variance proxy `σ_i²(y)`, hence
`G_i(y)² ≤ 𝒪₁(C σ_i²(y))` through the layer-cake formula and Lemma 2.3 (i). Lemma 2.3 (iii) sums
these bounds over the edges, and the crossing count of the canonical paths bounds
`ε^d ∑_{y,i} σ_i²(y)` by `C K² ∑_{w ≠ 0} |w|^{-(2d+1)}`.
-/

namespace LongRangeHeat

open MeasureTheory ProbabilityTheory Filter Topology Set
open LatticeProb LatticeProb.Euclidean.Lattice
open LongRange (kappa jumpKernel Edge edgeAdd jumpKernel_of_ne_zero)
open scoped ENNReal NNReal

noncomputable section

/-! ### From Gaussian tails to `𝒪₂` -/

/-- `∫_0^∞ t e^{-b t²} dt = (2b)⁻¹` for `b > 0`. -/
theorem integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-b * t ^ 2) = (2 * b)⁻¹ := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).const_mul (-b)).exp).const_mul (-(2 * b)⁻¹)
    convert this using 1
    field_simp
    ring
  have hlim : Tendsto (fun t => -(2 * b)⁻¹ * Real.exp (-b * t ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -b * t ^ 2) atTop atBot :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (-(2 * b)⁻¹)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop) hderiv
    (integrable_mul_exp_neg_mul_sq hb).integrableOn hlim]
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A nonnegative random variable with the Gaussian tail `P[Y ≥ t] ≤ 2 exp(-t² / 2σ²)` satisfies
`Y ≤ 𝒪₂(√6 σ)`. -/
theorem isOq_two_of_tail [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY0 : ∀ ω, 0 ≤ Y ω)
    (hYm : AEMeasurable Y P) {σ : ℝ} (hσ : 0 < σ)
    (htail : ∀ t > 0, P {ω | t ≤ Y ω} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2)))) :
    IsOq P 2 Y (Real.sqrt 6 * σ) := by
  set K := 6 * σ ^ 2 with hK
  have hKpos : 0 < K := by positivity
  set g : ℝ → ℝ := fun t => 2 * t / K * Real.exp (t ^ 2 / K) with hg
  have hgc : Continuous g := by fun_prop
  have hprim : ∀ x, ∫ t in (0)..x, g t = Real.exp (x ^ 2 / K) - 1 := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Real.exp (t ^ 2 / K))
      (fun t _ => ?_) (hgc.intervalIntegrable _ _)]
    · simp
    · have := ((hasDerivAt_pow 2 t).div_const K).exp
      convert this using 1
      simp only [hg]
      field_simp
      ring
  have hcake := lintegral_comp_eq_lintegral_meas_le_mul P (Eventually.of_forall hY0) hYm
    (fun t _ => hgc.intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => by
      simp only [hg]; positivity))
  simp only [hprim] at hcake
  have hb : 0 < 1 / (3 * σ ^ 2) := by positivity
  have hint := integral_Ioi_mul_exp_neg_mul_sq hb
  have hpt : ∀ t, 2 * Real.exp (-t ^ 2 / (2 * σ ^ 2)) * g t =
      2 / (3 * σ ^ 2) * (t * Real.exp (-(1 / (3 * σ ^ 2)) * t ^ 2)) := by
    intro t
    simp only [hg, hK]
    have he : -(1 / (3 * σ ^ 2)) * t ^ 2 = -t ^ 2 / (2 * σ ^ 2) + t ^ 2 / (6 * σ ^ 2) := by
      field_simp
      ring
    rw [he, Real.exp_add]
    field_simp
    ring
  have hRHS : ∫⁻ t in Ioi 0, P {ω | t ≤ Y ω} * ENNReal.ofReal (g t) ≤ 1 := by
    calc ∫⁻ t in Ioi 0, P {ω | t ≤ Y ω} * ENNReal.ofReal (g t)
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (2 / (3 * σ ^ 2) *
            (t * Real.exp (-(1 / (3 * σ ^ 2)) * t ^ 2))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t (ht : 0 < t) => ?_
          calc P {ω | t ≤ Y ω} * ENNReal.ofReal (g t)
              ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2))) * ENNReal.ofReal (g t) :=
                mul_le_mul_of_nonneg_right (htail t ht) (by positivity)
            _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), hpt]
      _ = ENNReal.ofReal (∫ t in Ioi 0, 2 / (3 * σ ^ 2) *
            (t * Real.exp (-(1 / (3 * σ ^ 2)) * t ^ 2))) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((integrable_mul_exp_neg_mul_sq hb).integrableOn.const_mul _)
            ((ae_restrict_iff' measurableSet_Ioi).mpr
              (Eventually.of_forall fun t (ht : 0 < t) => by positivity))]
      _ = 1 := by
          rw [integral_const_mul, hint]
          field_simp
          simp
  refine ⟨hYm, ?_⟩
  have hY : ∀ ω, ENNReal.ofReal (Real.exp ((max (Y ω) 0 / (Real.sqrt 6 * σ)) ^ 2)) =
      ENNReal.ofReal (Real.exp (Y ω ^ 2 / K) - 1) + 1 := by
    intro ω
    rw [max_eq_left (hY0 ω), div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), ← hK,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add
        (sub_nonneg.mpr (Real.one_le_exp (by positivity))) zero_le_one, sub_add_cancel]
  simp_rw [hY]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, hcake]
  calc _ ≤ (1 : ℝ≥0∞) + 1 := by gcongr
    _ = 2 := one_add_one_eq_two

/-- A sub-Gaussian random variable with variance proxy `c > 0` satisfies `|X| ≤ 𝒪₂(√(6c))`. -/
theorem isOq_two_abs_of_hasSubgaussianMGF [IsProbabilityMeasure P] {X : Ω → ℝ} {c : ℝ≥0}
    (hc : 0 < c) (h : HasSubgaussianMGF X c P) :
    IsOq P 2 (fun ω => |X ω|) (Real.sqrt 6 * Real.sqrt c) := by
  have hcr : (0 : ℝ) < c := hc
  refine isOq_two_of_tail (fun ω => abs_nonneg _)
    (continuous_abs.measurable.comp_aemeasurable h.aemeasurable) (Real.sqrt_pos.mpr hcr)
    fun t ht => ?_
  rw [Real.sq_sqrt hcr.le]
  have h1 : P {ω | t ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (h.measure_ge_le ht.le)
  have h2 : P {ω | t ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (h.neg.measure_ge_le ht.le)
  calc P {ω | t ≤ |X ω|} ≤ P ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := by
        refine measure_mono fun ω (hω : t ≤ |X ω|) => ?_
        rcases le_abs'.mp hω with h | h
        · exact Or.inr (show t ≤ -X ω by linarith)
        · exact Or.inl h
    _ ≤ P {ω | t ≤ X ω} + P {ω | t ≤ -X ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * c))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, ← two_mul]

/-- Increasing the scale preserves `X ≤ 𝒪_q(A)`. -/
theorem IsOq.mono {q : ℕ} {X : Ω → ℝ} {A B : ℝ} (h : IsOq P q X A) (hA : 0 < A)
    (hAB : A ≤ B) : IsOq P q X B :=
  ⟨h.1, (lintegral_mono fun _ => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (pow_le_pow_left₀ (div_nonneg (le_max_right _ _) (hA.le.trans hAB))
      (div_le_div_of_nonneg_left (le_max_right _ _) hA hAB) q))).trans h.2⟩

/-- Multiplying the variable and the scale by `c > 0` preserves `X ≤ 𝒪_q(A)`. -/
theorem IsOq.const_mul {q : ℕ} {X : Ω → ℝ} {A c : ℝ} (h : IsOq P q X A) (hc : 0 < c) :
    IsOq P q (fun ω => c * X ω) (c * A) := by
  refine ⟨h.1.const_mul c, le_of_eq_of_le (lintegral_congr fun ω => ?_) h.2⟩
  show ENNReal.ofReal (Real.exp ((max (c * X ω) 0 / (c * A)) ^ q)) = _
  rw [show max (c * X ω) 0 = c * max (X ω) 0 by rw [mul_max_of_nonneg _ _ hc.le, mul_zero],
    mul_div_mul_left _ _ hc.ne']

/-! ### Hoeffding's inequality for the conductances -/

variable {d : ℕ}

/-- Hoeffding: a finite linear combination `∑_e c_e (a(e) - 1)` of the centered conductances is
sub-Gaussian with variance proxy `∑_e c_e² ((λ⁻¹ - λ) / 2)²`. -/
theorem hasSubgaussianMGF_sum_conductance {lam : ℝ} {a : Ω → Edge d → ℝ}
    (hA : ConductanceLaw P lam a) (E : Finset (Edge d)) (c : Edge d → ℝ) :
    ∃ v : ℝ≥0, (v : ℝ) = (∑ e ∈ E, c e ^ 2) * ((lam⁻¹ - lam) / 2) ^ 2 ∧
      HasSubgaussianMGF (fun ω => ∑ e ∈ E, c e * (a ω e - 1)) v P := by
  have := hA.isProbabilityMeasure
  have hll : lam ≤ lam⁻¹ := hA.lam_mem.2.trans ((one_le_inv₀ hA.lam_mem.1).mpr hA.lam_mem.2)
  have hind : iIndepFun (fun e ω => c e * (a ω e - 1)) P :=
    hA.indep.comp (fun e x => c e * (x - 1)) fun e => by fun_prop
  set θ : ℝ≥0 := (‖(lam⁻¹ - 1) - (lam - 1)‖₊ / 2) ^ 2 with hθ
  have hθr : (θ : ℝ) = ((lam⁻¹ - lam) / 2) ^ 2 := by
    rw [hθ, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    norm_num
  have hterm : ∀ e, HasSubgaussianMGF (fun ω => c e * (a ω e - 1))
      ((show ℝ≥0 from ⟨c e ^ 2, sq_nonneg _⟩) * θ) P := by
    intro e
    have hint : Integrable (fun ω => a ω e) P :=
      Integrable.of_bound (hA.measurable e).aestronglyMeasurable lam⁻¹
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hA.lam_mem.1.le.trans (hA.bounds ω e).1)]
          exact (hA.bounds ω e).2)
    have h0 : HasSubgaussianMGF (fun ω => a ω e - 1) θ P :=
      hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        ((hA.measurable e).sub_const 1).aemeasurable
        (Eventually.of_forall fun ω => ⟨by linarith [(hA.bounds ω e).1],
          by linarith [(hA.bounds ω e).2]⟩)
        (by rw [integral_sub hint (integrable_const 1), hA.mean_one e]; simp)
    exact h0.const_mul (c e)
  refine ⟨_, ?_, HasSubgaussianMGF.sum_of_iIndepFun hind fun e _ => hterm e⟩
  rw [NNReal.coe_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [NNReal.coe_mul, hθr]
  rfl

/-! ### `G_i(y)` as a linear combination of the conductances -/

/-- The pairs `(x, w)` with `w` a short jump and `(y, i) ∈ γ_{x,w}`. -/
def crossingPairs (ε : ℝ) (y : Site d) (i : Fin d) : Finset (Site d × Site d) :=
  (unitBallIndices d ε).biUnion fun w => (crossingSet w y i).image fun x => (x, w)

/-- A sum over `crossingPairs`, indexed by the short jump and the parameter of the crossed
edge. -/
theorem sum_crossingPairs {M : Type*} [AddCommMonoid M] (F : Site d × Site d → M) (ε : ℝ)
    (y : Site d) (i : Fin d) :
    ∑ p ∈ crossingPairs ε y i, F p =
      ∑ w ∈ unitBallIndices d ε, ∑ t ∈ pathRange w i, F (y - pathPoint w i t, w) := by
  rw [crossingPairs, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_image fun x _ x' _ h => (Prod.mk.inj h).1,
      sum_crossingSet (fun x => F (x, w))]
  · intro w _ w' _ hww'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨x', _, hx'⟩ := Finset.mem_image.mp hp'
    exact hww' (Prod.mk.inj hx').2.symm

/-- The jumps of the pairs in `crossingPairs` are short. -/
theorem snd_mem_of_mem_crossingPairs {ε : ℝ} {y : Site d} {i : Fin d} {p : Site d × Site d}
    (hp : p ∈ crossingPairs ε y i) : p.2 ∈ unitBallIndices d ε := by
  obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hpw
  exact hw

/-- The coefficient `(ε^{d+1} / 2) J(z) sgn(z_i) (g(x + z) - g(x))` of `a_{x,z} - 1` in
`G_i(y)`, for the pair `p = (x, w)` with `z = εw`. -/
def forcingCoeff (ε : ℝ) (g : Site d → ℝ) (i : Fin d) (p : Site d × Site d) : ℝ :=
  ε ^ (d + 1) / 2 * jumpKernel (physical ε p.2) * (Int.sign (p.2 i) : ℝ) *
    (g (p.1 + p.2) - g p.1)

/-- The edge `{x, x + w}` of a pair `(x, w)` with `w ≠ 0` (a fixed edge when `w = 0`). -/
def pairEdge (hd : 1 ≤ d) (p : Site d × Site d) : Edge d :=
  if hw : p.2 = 0 then LongRange.baseEdge hd else edgeAdd p.1 p.2 hw

/-- `G_i(y)` is a linear combination of the centered conductances of the pairs crossing
`(y, i)`. -/
theorem forcingField_eq_sum_pairs (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (a : Edge d → ℝ)
    (g : Site d → ℝ) (i : Fin d) (y : Site d) :
    forcingField ε a g i y =
      ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p * (a (pairEdge hd p) - 1) := by
  rw [forcingField_eq, sum_crossingPairs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw0 : w ≠ 0 := ((mem_unitBallIndices hε w).mp hw).1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [forcingCoeff, pairEdge, centeredIncrement, hw0, ↓reduceDIte]
  ring

/-- The edges whose conductance enters `G_i(y)`. -/
def crossingEdges (hd : 1 ≤ d) (ε : ℝ) (y : Site d) (i : Fin d) : Finset (Edge d) :=
  (crossingPairs ε y i).image (pairEdge hd)

/-- The coefficient of `a(e) - 1` in `G_i(y)`: the sum over the orientations of `e`. -/
def edgeCoeff (hd : 1 ≤ d) (ε : ℝ) (g : Site d → ℝ) (i : Fin d) (y : Site d) (e : Edge d) : ℝ :=
  ∑ p ∈ (crossingPairs ε y i).filter (fun p => pairEdge hd p = e), forcingCoeff ε g i p

/-- `G_i(y)` is a linear combination of the centered conductances of the edges, each
orientation of an edge contributing to its coefficient. -/
theorem forcingField_eq_sum_edges (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (a : Edge d → ℝ)
    (g : Site d → ℝ) (i : Fin d) (y : Site d) :
    forcingField ε a g i y =
      ∑ e ∈ crossingEdges hd ε y i, edgeCoeff hd ε g i y e * (a e - 1) := by
  rw [forcingField_eq_sum_pairs hd hε, ← Finset.sum_fiberwise_of_maps_to
    (g := pairEdge hd) (t := crossingEdges hd ε y i) fun p hp => Finset.mem_image_of_mem _ hp]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [edgeCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.mp hp).2]

/-- An edge has at most two orientations `(x, w)` with `w ≠ 0`. -/
theorem card_filter_pairEdge_le (hd : 1 ≤ d) (s : Finset (Site d × Site d))
    (hs : ∀ p ∈ s, p.2 ≠ 0) (e : Edge d) :
    (s.filter fun p => pairEdge hd p = e).card ≤ 2 := by
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep e.1
  have hsub : s.filter (fun p => pairEdge hd p = e) ⊆ {(u, v - u), (v, u - v)} := by
    intro p hp
    obtain ⟨hps, hpe⟩ := Finset.mem_filter.mp hp
    simp only [pairEdge, hs p hps, ↓reduceDIte] at hpe
    have h1 : s(p.1, p.1 + p.2) = s(u, v) := (congrArg Subtype.val hpe).trans huv.symm
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases Sym2.eq_iff.mp h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 (by rw [← h2, ← h1]; abel))
    · exact Or.inr (Prod.ext h1 (by rw [← h2, ← h1]; abel))
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

/-- The variance proxy of `G_i(y)`: `∑_e c_e² ≤ 2 ∑_{(x,w)} b_{x,w}²`. -/
theorem sum_sq_edgeCoeff_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (g : Site d → ℝ) (i : Fin d)
    (y : Site d) :
    ∑ e ∈ crossingEdges hd ε y i, edgeCoeff hd ε g i y e ^ 2 ≤
      2 * ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p ^ 2 := by
  have hs : ∀ p ∈ crossingPairs ε y i, p.2 ≠ 0 := fun p hp =>
    ((mem_unitBallIndices hε p.2).mp (snd_mem_of_mem_crossingPairs hp)).1
  calc ∑ e ∈ crossingEdges hd ε y i, edgeCoeff hd ε g i y e ^ 2
      ≤ ∑ e ∈ crossingEdges hd ε y i, 2 * ∑ p ∈ (crossingPairs ε y i).filter
          (fun p => pairEdge hd p = e), forcingCoeff ε g i p ^ 2 :=
        Finset.sum_le_sum fun e _ => sq_sum_le_card_mul_sum_sq.trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_pairEdge_le hd _ hs e)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ = 2 * ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (s := crossingPairs ε y i)
          (t := crossingEdges hd ε y i) (g := pairEdge hd)
          (fun p hp => Finset.mem_image_of_mem _ hp) (fun p => forcingCoeff ε g i p ^ 2)]

/-! ### Summing the variances -/

/-- `b_{x,w}² ≤ (ε^{d+1} / 2)² J(εw)² (g(x + w) - g(x))²`. -/
theorem forcingCoeff_sq_le (ε : ℝ) (g : Site d → ℝ) (i : Fin d) (p : Site d × Site d) :
    forcingCoeff ε g i p ^ 2 ≤ (ε ^ (d + 1) / 2) ^ 2 * jumpKernel (physical ε p.2) ^ 2 *
      (g (p.1 + p.2) - g p.1) ^ 2 := by
  have hs : (Int.sign (p.2 i) : ℝ) ^ 2 ≤ 1 := by
    rcases Int.sign_trichotomy (p.2 i) with h | h | h <;> simp [h]
  calc forcingCoeff ε g i p ^ 2 = (ε ^ (d + 1) / 2 * jumpKernel (physical ε p.2) *
        (g (p.1 + p.2) - g p.1)) ^ 2 * (Int.sign (p.2 i) : ℝ) ^ 2 := by
        rw [forcingCoeff]
        ring
    _ ≤ (ε ^ (d + 1) / 2 * jumpKernel (physical ε p.2) * (g (p.1 + p.2) - g p.1)) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring

/-- Summing the variance proxies over the edges in direction `i`: each short jump `w` is counted
`|w_i|` times. -/
theorem summable_and_tsum_crossingPairs_le {ε : ℝ} {g : Site d → ℝ} (hg : MemL2 g) (i : Fin d) :
    Summable (fun y => ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p ^ 2) ∧
      ∑' y, ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p ^ 2 ≤
        ∑ w ∈ unitBallIndices d ε, ((w i).natAbs : ℝ) * ((ε ^ (d + 1) / 2) ^ 2 *
          jumpKernel (physical ε w) ^ 2 * ∑' x, (g (x + w) - g x) ^ 2) := by
  have hfx : ∀ w, Summable fun x => forcingCoeff ε g i (x, w) ^ 2 := fun w =>
    ((summable_sq_sub_shift hg w).mul_left ((ε ^ (d + 1) / 2) ^ 2 *
      jumpKernel (physical ε w) ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
      fun x => forcingCoeff_sq_le ε g i (x, w)
  have hsh : ∀ w (t : ℤ), Summable fun y => forcingCoeff ε g i (y - pathPoint w i t, w) ^ 2 :=
    fun w t => (Equiv.summable_iff (f := fun x => forcingCoeff ε g i (x, w) ^ 2)
      (Equiv.subRight (pathPoint w i t))).mpr (hfx w)
  have hW : ∀ y, ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p ^ 2 =
      ∑ w ∈ unitBallIndices d ε, ∑ t ∈ pathRange w i,
        forcingCoeff ε g i (y - pathPoint w i t, w) ^ 2 := fun y =>
    sum_crossingPairs (fun p => forcingCoeff ε g i p ^ 2) ε y i
  have hs : Summable fun y => ∑ p ∈ crossingPairs ε y i, forcingCoeff ε g i p ^ 2 := by
    simp_rw [hW]
    exact summable_sum fun w _ => summable_sum fun t _ => hsh w t
  refine ⟨hs, ?_⟩
  simp_rw [hW]
  rw [Summable.tsum_finsetSum fun w _ => summable_sum fun t _ => hsh w t]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [Summable.tsum_finsetSum fun t _ => hsh w t]
  have hshift : ∀ t ∈ pathRange w i, ∑' y, forcingCoeff ε g i (y - pathPoint w i t, w) ^ 2 =
      ∑' x, forcingCoeff ε g i (x, w) ^ 2 := fun t _ =>
    (Equiv.subRight (pathPoint w i t)).tsum_eq (fun x => forcingCoeff ε g i (x, w) ^ 2)
  rw [Finset.sum_congr rfl hshift, Finset.sum_const, card_pathRange, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun x => forcingCoeff_sq_le ε g i (x, w)) (hfx w)
    ((summable_sq_sub_shift hg w).mul_left _)

/-- The lattice sum `∑_{w ≠ 0} |w|^{-(d+1)}`. -/
def radialSum (d : ℕ) : ℝ :=
  ∑' w : Site d, (radius (physical 1 w) ^ (d + 1))⁻¹

/-- The series `∑_{w ≠ 0} |w|^{-(d+1)}` converges for `d ≥ 1`. -/
theorem summable_radialSum (hd : 1 ≤ d) :
    Summable fun w : Site d => (radius (physical 1 w) ^ (d + 1))⁻¹ :=
  (LatticeProb.Euclidean.Summability.euclidean_radial_error_summable d hd).congr fun w => by
    rw [zpow_neg, zpow_natCast]

/-- With the increment bound `‖g(· + w) - g‖ ≤ K min(|εw|, 1)`, the summed variance proxies are
at most `(d / 4) K² ∑_{w ≠ 0} |w|^{-(d+1)}`. -/
theorem variance_sum_le (hd : 1 ≤ d) {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) {g : Site d → ℝ}
    (hgK : ∀ w : Site d,
      latticeNorm ε (fun q => g (q + w) - g q) ≤ K * min (radius (physical ε w)) 1) :
    ε ^ d * ∑ w ∈ unitBallIndices d ε, (∑ i, ((w i).natAbs : ℝ)) * ((ε ^ (d + 1) / 2) ^ 2 *
      jumpKernel (physical ε w) ^ 2 * ∑' x, (g (x + w) - g x) ^ 2) ≤
      d / 4 * radialSum d * K ^ 2 := by
  rw [Finset.mul_sum]
  have hpt : ∀ w ∈ unitBallIndices d ε, ε ^ d * ((∑ i, ((w i).natAbs : ℝ)) *
      ((ε ^ (d + 1) / 2) ^ 2 * jumpKernel (physical ε w) ^ 2 * ∑' x, (g (x + w) - g x) ^ 2)) ≤
      d / 4 * K ^ 2 * (radius (physical 1 w) ^ (d + 1))⁻¹ := by
    intro w hw
    have hw0 : w ≠ 0 := ((mem_unitBallIndices hε w).mp hw).1
    set r := radius (physical 1 w) with hr
    have hr1 : 1 ≤ r := lattice_radius_ge_one hw0
    have hr0 : 0 < r := by linarith
    have hJ : jumpKernel (physical ε w) = ((ε * r) ^ (d + 2))⁻¹ := by
      rw [jumpKernel_of_ne_zero (fun h => hw0 ((physical_eq_zero_iff hε w).mp h)),
        radius_physical_eq_mul hε.le]
    have hT : ε ^ d * ∑' x, (g (x + w) - g x) ^ 2 ≤ K ^ 2 * (ε * r) ^ 2 := by
      have h0 : 0 ≤ ε ^ d * ∑' x, (g (x + w) - g x) ^ 2 :=
        mul_nonneg (pow_nonneg hε.le d) (tsum_nonneg fun _ => sq_nonneg _)
      have hmin : K * min (radius (physical ε w)) 1 ≤ K * (ε * r) :=
        mul_le_mul_of_nonneg_left ((min_le_left _ _).trans_eq
          (radius_physical_eq_mul hε.le w)) hK
      calc ε ^ d * ∑' x, (g (x + w) - g x) ^ 2
          = Real.sqrt (ε ^ d * ∑' x, (g (x + w) - g x) ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ (K * (ε * r)) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) ((hgK w).trans hmin) 2
        _ = K ^ 2 * (ε * r) ^ 2 := by ring
    have hs1 : ∑ i, ((w i).natAbs : ℝ) ≤ d * r := by
      calc ∑ i, ((w i).natAbs : ℝ) ≤ ∑ _i : Fin d, r := Finset.sum_le_sum fun i _ => by
            have := abs_coord_le_radius (physical 1 w) i
            simp only [physical, one_mul] at this
            rw [Nat.cast_natAbs, Int.cast_abs]
            exact this
        _ = d * r := by simp
    have hid : (ε ^ (d + 1) / 2) ^ 2 * ((ε * r) ^ (d + 2))⁻¹ ^ 2 * (ε * r) ^ 2 =
        1 / 4 * (r ^ (2 * d + 2))⁻¹ := by
      field_simp
      ring
    have hs0 : 0 ≤ ∑ i, ((w i).natAbs : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc ε ^ d * ((∑ i, ((w i).natAbs : ℝ)) * ((ε ^ (d + 1) / 2) ^ 2 *
          jumpKernel (physical ε w) ^ 2 * ∑' x, (g (x + w) - g x) ^ 2))
        = (∑ i, ((w i).natAbs : ℝ)) * ((ε ^ (d + 1) / 2) ^ 2 * ((ε * r) ^ (d + 2))⁻¹ ^ 2) *
          (ε ^ d * ∑' x, (g (x + w) - g x) ^ 2) := by rw [hJ]; ring
      _ ≤ (∑ i, ((w i).natAbs : ℝ)) * ((ε ^ (d + 1) / 2) ^ 2 * ((ε * r) ^ (d + 2))⁻¹ ^ 2) *
          (K ^ 2 * (ε * r) ^ 2) :=
          mul_le_mul_of_nonneg_left hT (mul_nonneg hs0 (by positivity))
      _ = (∑ i, ((w i).natAbs : ℝ)) * K ^ 2 *
          ((ε ^ (d + 1) / 2) ^ 2 * ((ε * r) ^ (d + 2))⁻¹ ^ 2 * (ε * r) ^ 2) := by ring
      _ = (∑ i, ((w i).natAbs : ℝ)) * K ^ 2 * (1 / 4 * (r ^ (2 * d + 2))⁻¹) := by rw [hid]
      _ ≤ (d * r) * K ^ 2 * (1 / 4 * (r ^ (2 * d + 2))⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs1 (sq_nonneg K))
            (by positivity)
      _ = d / 4 * K ^ 2 * (r ^ (2 * d + 1))⁻¹ := by
          rw [show 2 * d + 2 = (2 * d + 1) + 1 by ring, pow_succ]
          field_simp
          ring
      _ ≤ d / 4 * K ^ 2 * (r ^ (d + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hr0 _)
            (pow_le_pow_right₀ hr1 (by omega))) (by positivity)
  calc ∑ w ∈ unitBallIndices d ε, ε ^ d * ((∑ i, ((w i).natAbs : ℝ)) *
        ((ε ^ (d + 1) / 2) ^ 2 * jumpKernel (physical ε w) ^ 2 * ∑' x, (g (x + w) - g x) ^ 2))
      ≤ ∑ w ∈ unitBallIndices d ε, d / 4 * K ^ 2 * (radius (physical 1 w) ^ (d + 1))⁻¹ :=
        Finset.sum_le_sum hpt
    _ = d / 4 * K ^ 2 * ∑ w ∈ unitBallIndices d ε, (radius (physical 1 w) ^ (d + 1))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ d / 4 * K ^ 2 * radialSum d :=
        mul_le_mul_of_nonneg_left ((summable_radialSum hd).sum_le_tsum _ fun w _ =>
          inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)) (by positivity)
    _ = d / 4 * radialSum d * K ^ 2 := by ring

/-! ### Lemma 3.3 for a general function -/

/-- Hoeffding for one edge: `G_i(y)² ≤ 𝒪₁(6 σ_i²(y))`, where
`σ_i²(y) = (∑_e c_e²) ((λ⁻¹ - λ) / 2)²` is the variance proxy of `G_i(y)`. -/
theorem isOq_one_sq_forcingField (hd : 1 ≤ d) {lam : ℝ} {a : Ω → Edge d → ℝ}
    (hA : ConductanceLaw P lam a) {ε : ℝ} (hε : 0 < ε) (g : Site d → ℝ) (i : Fin d)
    (y : Site d)
    (hpos : 0 < (∑ e ∈ crossingEdges hd ε y i, edgeCoeff hd ε g i y e ^ 2) *
      ((lam⁻¹ - lam) / 2) ^ 2) :
    IsOq P 1 (fun ω => forcingField ε (a ω) g i y ^ 2)
      (6 * ((∑ e ∈ crossingEdges hd ε y i, edgeCoeff hd ε g i y e ^ 2) *
        ((lam⁻¹ - lam) / 2) ^ 2)) := by
  have := hA.isProbabilityMeasure
  obtain ⟨v, hv, hsub⟩ :=
    hasSubgaussianMGF_sum_conductance hA (crossingEdges hd ε y i) (edgeCoeff hd ε g i y)
  have hvpos : 0 < v := by
    rw [← NNReal.coe_pos, hv]
    exact hpos
  have h1 := (isOq_two_iff (fun ω => abs_nonneg _) _).mp
    (isOq_two_abs_of_hasSubgaussianMGF hvpos hsub)
  have hX : (fun ω => forcingField ε (a ω) g i y ^ 2) = fun ω =>
      |∑ e ∈ crossingEdges hd ε y i, edgeCoeff hd ε g i y e * (a ω e - 1)| ^ 2 := by
    funext ω
    rw [sq_abs, forcingField_eq_sum_edges hd hε]
  rw [hX]
  convert h1 using 1
  rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt v.coe_nonneg, hv]

/-- **Lemma 3.3** (`lem:G`) for a function `g ∈ L²(εℤ^d)` with the increment bound
`‖g(· + w) - g‖ ≤ K min(|εw|, 1)`: there is `C > 0`, depending only on `d` and `λ`, such that for
every law of the conductances, every `ε ∈ (0, 1/2)` and every `K > 0`, the components of the field
`G` of (3.3) built from `g` lie in `L²(εℤ^d)` and `‖G‖_{L²(εℤ^d)} ≤ 𝒪₂(C K)`. -/
theorem forcingField_gaussian_tails_of_increment (hd : 1 ≤ d) {lam : ℝ}
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → Edge d → ℝ),
      ConductanceLaw P lam a → ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 2), ∀ K > 0, ∀ g : Site d → ℝ,
      MemL2 g → (∀ w : Site d,
        latticeNorm ε (fun q => g (q + w) - g q) ≤ K * min (radius (physical ε w)) 1) →
      (∀ ω i, MemL2 (forcingField ε (a ω) g i)) ∧
      IsOq P 2 (fun ω => Real.sqrt (∑ i, latticeNormSq ε (forcingField ε (a ω) g i)))
        (C * K) := by
  set θ := ((lam⁻¹ - lam) / 2) ^ 2 with hθ
  have hθ0 : 0 ≤ θ := sq_nonneg _
  have hR0 : 0 ≤ radialSum d :=
    tsum_nonneg fun _ => inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
  have hC0 : 0 ≤ 3 * d * θ * radialSum d := by positivity
  refine ⟨Real.sqrt (3 * d * θ * radialSum d + 1), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro Ω _ P a hA ε hε K hK g hg hgK
  have := hA.isProbabilityMeasure
  have hε0 := hε.1
  have hMem : ∀ ω i, MemL2 (forcingField ε (a ω) g i) := fun ω i =>
    memL2_forcingField hA.lam_mem (hA.bounds ω) hg ε i
  refine ⟨hMem, ?_⟩
  set X : Fin d × Site d → Ω → ℝ := fun k ω => forcingField ε (a ω) g k.1 k.2 with hXdef
  set V : Fin d × Site d → ℝ := fun k =>
    (∑ e ∈ crossingEdges hd ε k.2 k.1, edgeCoeff hd ε g k.1 k.2 e ^ 2) * θ with hVdef
  set W : Fin d × Site d → ℝ := fun k =>
    ∑ p ∈ crossingPairs ε k.2 k.1, forcingCoeff ε g k.1 p ^ 2 with hWdef
  have hV0 : ∀ k, 0 ≤ V k := fun k => mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hθ0
  have hW0 : ∀ k, 0 ≤ W k := fun k => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hVW : ∀ k, V k ≤ 2 * θ * W k := fun k => by
    calc V k ≤ (2 * W k) * θ :=
          mul_le_mul_of_nonneg_right (sum_sq_edgeCoeff_le hd hε0 g k.1 k.2) hθ0
      _ = 2 * θ * W k := by ring
  have hWs : Summable W := by
    rw [summable_prod_of_nonneg hW0]
    exact ⟨fun i => (summable_and_tsum_crossingPairs_le hg i).1, .of_finite⟩
  have hVs : Summable V := (hWs.mul_left (2 * θ)).of_nonneg_of_le hV0 hVW
  have hWb : ε ^ d * ∑' k, W k ≤ d / 4 * radialSum d * K ^ 2 := by
    rw [hWs.tsum_prod, tsum_fintype]
    calc ε ^ d * ∑ i, ∑' y, W (i, y)
        ≤ ε ^ d * ∑ i, ∑ w ∈ unitBallIndices d ε, ((w i).natAbs : ℝ) * ((ε ^ (d + 1) / 2) ^ 2 *
          jumpKernel (physical ε w) ^ 2 * ∑' x, (g (x + w) - g x) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
            (summable_and_tsum_crossingPairs_le hg i).2) (pow_nonneg hε0.le d)
      _ = ε ^ d * ∑ w ∈ unitBallIndices d ε, (∑ i, ((w i).natAbs : ℝ)) *
          ((ε ^ (d + 1) / 2) ^ 2 * jumpKernel (physical ε w) ^ 2 *
            ∑' x, (g (x + w) - g x) ^ 2) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_mul]
      _ ≤ _ := variance_sum_le hd hε0 hK.le hgK
  set Kp : Set (Fin d × Site d) := {k | 0 < V k} with hKp
  have hX0 : ∀ k ∉ Kp, ∀ ω, X k ω = 0 := by
    intro k hk ω
    have hVk : V k = 0 := le_antisymm (not_lt.mp hk) (hV0 k)
    simp only [hXdef]
    rw [forcingField_eq_sum_edges hd hε0]
    rcases mul_eq_zero.mp hVk with h | h
    · refine Finset.sum_eq_zero fun e he => ?_
      have hc : edgeCoeff hd ε g k.1 k.2 e ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h e he
      rw [pow_eq_zero_iff two_ne_zero |>.mp hc, zero_mul]
    · rw [hθ] at h
      have hl : lam⁻¹ = lam := by
        have := pow_eq_zero_iff two_ne_zero |>.mp h
        linarith
      have h1 : lam = 1 := by
        have hm : lam * lam = 1 := by
          nth_rewrite 2 [← hl]
          exact mul_inv_cancel₀ hlam.1.ne'
        nlinarith [hlam.1]
      refine Finset.sum_eq_zero fun e _ => ?_
      have hb := hA.bounds ω e
      rw [h1, inv_one] at hb
      rw [show a ω e = 1 by linarith [hb.1, hb.2], sub_self, mul_zero]
  have hident : ∀ ω, ∑ i, latticeNormSq ε (forcingField ε (a ω) g i) =
      ε ^ d * ∑' j : Kp, X j.1 ω ^ 2 := by
    intro ω
    have hXs : Summable fun k : Fin d × Site d => X k ω ^ 2 := by
      rw [summable_prod_of_nonneg fun _ => sq_nonneg _]
      exact ⟨fun i => hMem ω i, .of_finite⟩
    rw [tsum_subtype_eq_of_support_subset (s := Kp) (f := fun k => X k ω ^ 2) ?_,
      hXs.tsum_prod, tsum_fintype, Finset.mul_sum]
    · rfl
    · intro k hk
      rw [Function.mem_support] at hk
      by_contra hkK
      exact hk (by rw [hX0 k hkK ω]; norm_num)
  have hsum := isOq_tsum (P := P) (ι := Kp) one_ne_zero (X := fun j ω => X j.1 ω ^ 2)
    (fun _ _ => sq_nonneg _) (A := fun j => 6 * V j.1)
    (fun j => mul_pos (by norm_num) j.2) ((hVs.subtype Kp).mul_left 6)
    (fun j => isOq_one_sq_forcingField hd hA hε0 g j.1.1 j.1.2 j.2)
  have hO := hsum.2.const_mul (pow_pos hε0 d)
  have hle : ε ^ d * ∑' j : Kp, 6 * V j.1 ≤
      (Real.sqrt (3 * d * θ * radialSum d + 1) * K) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    calc ε ^ d * ∑' j : Kp, 6 * V j.1 ≤ ε ^ d * ∑' k, 6 * V k :=
          mul_le_mul_of_nonneg_left (Summable.tsum_subtype_le (fun k => 6 * V k) Kp
            (fun k => mul_nonneg (by norm_num) (hV0 k)) (hVs.mul_left 6)) (pow_nonneg hε0.le d)
      _ ≤ ε ^ d * ∑' k, 12 * θ * W k :=
          mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun k => by linarith [hVW k])
            (hVs.mul_left 6) (hWs.mul_left _)) (pow_nonneg hε0.le d)
      _ = 12 * θ * (ε ^ d * ∑' k, W k) := by
          rw [tsum_mul_left]
          ring
      _ ≤ 12 * θ * (d / 4 * radialSum d * K ^ 2) :=
          mul_le_mul_of_nonneg_left hWb (mul_nonneg (by norm_num) hθ0)
      _ ≤ (3 * d * θ * radialSum d + 1) * K ^ 2 := by nlinarith [sq_nonneg K]
  rcases isEmpty_or_nonempty Kp with hE | hNE
  · have h0 : ∀ ω, Real.sqrt (∑ i, latticeNormSq ε (forcingField ε (a ω) g i)) = 0 := by
      intro ω
      rw [hident ω, tsum_empty, mul_zero, Real.sqrt_zero]
    refine ⟨aemeasurable_const.congr (Eventually.of_forall fun ω => (h0 ω).symm), ?_⟩
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (Real.sqrt (∑ i, latticeNormSq ε
          (forcingField ε (a ω) g i))) 0 / (Real.sqrt (3 * d * θ * radialSum d + 1) * K)) ^ 2))
          ∂P = ∫⁻ _, 1 ∂P := lintegral_congr fun ω => by simp [h0 ω]
      _ ≤ 2 := by simp
  · obtain ⟨j₀⟩ := hNE
    have hA0 : 0 < ε ^ d * ∑' j : Kp, 6 * V j.1 :=
      mul_pos (pow_pos hε0 d) (((hVs.subtype Kp).mul_left 6).tsum_pos
        (fun j => mul_nonneg (by norm_num) (hV0 _)) j₀ (mul_pos (by norm_num) j₀.2))
    have h1 : IsOq P 1 (fun ω => ∑ i, latticeNormSq ε (forcingField ε (a ω) g i))
        ((Real.sqrt (3 * d * θ * radialSum d + 1) * K) ^ 2) := by
      rw [show (fun ω => ∑ i, latticeNormSq ε (forcingField ε (a ω) g i)) =
        fun ω => ε ^ d * ∑' j : Kp, X j.1 ω ^ 2 from funext hident]
      exact hO.mono hA0 hle
    rw [isOq_two_iff fun ω => Real.sqrt_nonneg _]
    convert h1 using 2
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      mul_nonneg (pow_nonneg hε0.le d) (tsum_nonneg fun _ => sq_nonneg _))

end

end LongRangeHeat
