import LongRange.Scaling.Dirichlet
import LongRange.Walk.Pairing
import LongRange.TwoScale.Approximate
import LatticeProb.Analysis.Elliptic.Examples

/-!
# Analytic ingredients of the deterministic scaling obstruction

A nonzero classical solution with zero boundary data has a positive limiting lattice norm.
All lattice norms retain the physical volume factor and the original Euclidean kernel.
-/

namespace LongRange.Scaling

open Filter MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- Zero extension of continuous Dirichlet data on a bounded domain has compact support. -/
theorem continuous_compact_zero_extension {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {u : (Fin d → ℝ) → ℝ}
    (hc : ContinuousOn u (closure U)) (hz : ∀ x ∈ frontier U, u x = 0) :
    Continuous (U.indicator u) ∧ HasCompactSupport (U.indicator u) := by
  classical
  constructor
  · exact continuous_piecewise hz hc continuousOn_const
  · apply hU.isCompact_closure.of_isClosed_subset isClosed_closure
    exact closure_mono Set.support_indicator_subset

/-- A nonzero classical source solution has a strictly positive limiting sampled squared norm.
Nonvanishing in the domain is the source's nonzero solution condition, not an extra norm premise. -/
theorem classical_sample_norm_limit_pos {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {a₀ : ℝ} {f u : (Fin d → ℝ) → ℝ}
    (hu : Elliptic.IsClassicalDirichletSolution U 0 a₀ f u)
    (hne : ∃ x ∈ U, u x ≠ 0) :
    ∃ I : ℝ, 0 < I ∧ Tendsto
      (fun ε => l2NormSq ε U (fun q => u (physical ε q)))
      (𝓝[>] (0 : ℝ)) (𝓝 I) := by
  classical
  obtain ⟨hc, hs⟩ := continuous_compact_zero_extension hU hu.2.1 hu.2.2.1
  let F := U.indicator u
  have hF : Continuous F := hc
  have hFs : HasCompactSupport F := hs
  have hsquare : HasCompactSupport (fun x => F x ^ 2) := by
    have heq : (fun x => F x ^ 2) = F * F := by
      funext x
      exact sq (F x)
    rw [heq]
    exact hFs.mul_right
  obtain ⟨x, hx, hux⟩ := hne
  have hFx : F x ^ 2 ≠ 0 := by
    dsimp only [F]
    rw [Set.indicator_of_mem hx]
    exact pow_ne_zero 2 hux
  have hI : 0 < ∫ x, F x ^ 2 :=
    (hF.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      hsquare (fun _ => sq_nonneg _) hFx
  have hzero : ∀ y, y ∉ U → F y = 0 := fun y hy => Set.indicator_of_notMem hy u
  have ht := tendsto_l2NormSq_sample hF hFs hzero
  have hi : (∫ x in U, F x ^ 2) = ∫ x, F x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hzero y hy, zero_pow (by decide)])
  rw [hi] at ht
  refine ⟨_, hI, ?_⟩
  convert ht using 1
  funext ε
  unfold l2NormSq
  congr 1
  apply tsum_congr
  intro q
  exact congrArg (fun x : ℝ => x ^ 2)
    (Set.indicator_of_mem (show physical ε q ∈ U from q.property) u).symm

/-- Source regularity and nonvanishing produce a positive uniform lattice norm at small scales. -/
theorem classical_sample_norm_eventually_pos {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {a₀ : ℝ} {f u : (Fin d → ℝ) → ℝ}
    (hu : Elliptic.IsClassicalDirichletSolution U 0 a₀ f u)
    (hne : ∃ x ∈ U, u x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      m ≤ l2Norm ε U (fun q => u (physical ε q)) := by
  obtain ⟨I, hI, ht⟩ := classical_sample_norm_limit_pos hU hu hne
  refine ⟨Real.sqrt (I / 2), Real.sqrt_pos.mpr (by linarith), ?_⟩
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      I / 2 < l2NormSq ε U (fun q => u (physical ε q)) :=
    ht.eventually (eventually_gt_nhds (by linarith : I / 2 < I))
  filter_upwards [he] with ε hε
  exact Real.sqrt_le_sqrt hε.le

/-- Scalar multiplication has the usual absolute-value factor in the source lattice norm. -/
theorem l2Norm_const_mul (ε : ℝ) (U : Set (Fin d → ℝ)) (b : ℝ)
    (g : Site d → ℝ) : l2Norm ε U (fun q => b * g q) = |b| * l2Norm ε U g := by
  unfold l2Norm l2NormSq
  simp_rw [mul_pow]
  rw [tsum_mul_left, ← mul_assoc, mul_comm (ε ^ d) (b ^ 2), mul_assoc,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The norm on the half-domain has exactly the square-root volume factor. -/
theorem l2Norm_halfDomain (ε : ℝ) (U : Set (Fin d → ℝ)) (g : Site d → ℝ) :
    l2Norm (ε / 2) (halfDomain U) g =
      Real.sqrt ((2 : ℝ)⁻¹ ^ d) * l2Norm ε U g := by
  unfold l2Norm
  rw [l2NormSq_halfDomain, Real.sqrt_mul (by positivity)]

/-- A triangle inequality compares both source errors with the normalization mismatch.
The discrete solution identity is derived from the actual equations. -/
theorem source_error_comparison (hd : 1 ≤ d) {ε lam : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) (hlam : 0 < lam) {a : Edge d → ℝ}
    (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (f ū : (Fin d → ℝ) → ℝ) {u v : Site d → ℝ}
    (hu : SupportedIn ε U u) (hv : SupportedIn (ε / 2) (halfDomain U) v)
    (heu : ∀ q ∈ latticeSet ε U, -generator ε a u q = f (physical ε q))
    (hev : ∀ q ∈ latticeSet (ε / 2) (halfDomain U),
      -generator (ε / 2) a v q = 4 * f ((2 : ℝ) • physical (ε / 2) q)) :
    |kappa d (ε / 2) - kappa d ε| *
        l2Norm ε U (fun q => ū (physical ε q)) ≤
      kappa d (ε / 2) * l2Norm ε U (fun q => u q - ū (physical ε q)) +
      kappa d ε / Real.sqrt ((2 : ℝ)⁻¹ ^ d) *
        l2Norm (ε / 2) (halfDomain U)
          (fun q => v q - ū ((2 : ℝ) • physical (ε / 2) q)) := by
  have hh : ε / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hid := dirichlet_half_scaling hd hε hU hlam ha f hu hv heu hev
  have heq : (fun q => (kappa d (ε / 2) - kappa d ε) * ū (physical ε q)) =
      fun q => (-kappa d (ε / 2)) * (u q - ū (physical ε q)) +
        kappa d ε * (v q - ū ((2 : ℝ) • physical (ε / 2) q)) := by
    funext q
    rw [hid, twice_physical_half]
    field_simp [(kappa_pos hd hε).ne']
    ring
  rw [← l2Norm_const_mul, heq]
  have ht := l2Norm_add_le hε.1 hU
    (fun q => (-kappa d (ε / 2)) * (u q - ū (physical ε q)))
    (fun q => kappa d ε * (v q - ū ((2 : ℝ) • physical (ε / 2) q)))
  rw [l2Norm_const_mul, l2Norm_const_mul, abs_neg,
    abs_of_pos (kappa_pos hd hh), abs_of_pos (kappa_pos hd hε)] at ht
  rw [l2Norm_halfDomain]
  have hs : Real.sqrt ((2 : ℝ)⁻¹ ^ d) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  convert ht using 1
  field_simp [hs]

/-- The sum of the two actual source errors, multiplied by `|log ε|`, stays bounded below
at arbitrarily small scales. The positive constant may depend on the fixed source problem. -/
theorem source_errors_frequently_lower_bound (hd : 1 ≤ d) {lam : ℝ}
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (f ū : (Fin d → ℝ) → ℝ) {a₀ : ℝ}
    (hū : Elliptic.IsClassicalDirichletSolution U 0 a₀ f ū)
    (hne : ∃ x ∈ U, ū x ≠ 0) (u v : ℝ → Site d → ℝ)
    (hu : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε U (u ε))
    (hv : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn (ε / 2) (halfDomain U) (v ε))
    (heu : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet ε U,
      -generator ε a (u ε) q = f (physical ε q))
    (hev : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet (ε / 2) (halfDomain U),
      -generator (ε / 2) a (v ε) q = 4 * f ((2 : ℝ) • physical (ε / 2) q)) :
    ∃ b : ℝ, 0 < b ∧ ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ,
      ε ∈ Set.Ioo (0 : ℝ) (min δ 1) ∧
      b ≤ |Real.log ε| *
        (l2Norm ε U (fun q => u ε q - ū (physical ε q)) +
          l2Norm (ε / 2) (halfDomain U)
            (fun q => v ε q - ū ((2 : ℝ) • physical (ε / 2) q))) := by
  obtain ⟨c, hc, hinc⟩ := kappa_half_increment_frequently_pos hd
  obtain ⟨m, hm, hnorm⟩ := classical_sample_norm_eventually_pos hU hū hne
  obtain ⟨r, hr, hnormr⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnorm
  obtain ⟨C, hC, hupper⟩ := kappa_le d
  obtain ⟨K, hK, hratio⟩ := kappa_ratio_bound hd
  let s := Real.sqrt ((2 : ℝ)⁻¹ ^ d)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  let H := 2 * K + s⁻¹
  have hH : 0 < H := by dsimp only [H]; positivity
  let b := c * m / (2 * C * H)
  have hb : 0 < b := div_pos (mul_pos hc hm) (by positivity)
  refine ⟨b, hb, ?_⟩
  intro δ hδ
  obtain ⟨ε, hεsmall, hgap⟩ := hinc (min δ (min r (Real.exp (-1))))
    (lt_min hδ (lt_min hr (Real.exp_pos _)))
  have hε : ε ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hεsmall.1, hεsmall.2.trans_le (min_le_right _ _)⟩
  have hsmall : ε < min δ (min r (Real.exp (-1))) :=
    hεsmall.2.trans_le (min_le_left _ _)
  have hεδ : ε < δ := hsmall.trans_le (min_le_left _ _)
  have hεr : ε < r :=
    (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hεexp : ε < Real.exp (-1) :=
    (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hL : 1 ≤ |Real.log ε| := by
    have hl := Real.log_le_log hε.1 hεexp.le
    rw [Real.log_exp] at hl
    rw [abs_of_neg (Real.log_neg hε.1 hε.2)]
    linarith
  have hκ : kappa d ε ≤ 2 * C * |Real.log ε| :=
    (hupper ε hε).trans (by nlinarith only [hL, hC])
  have hh : ε / 2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hκhalf : kappa d (ε / 2) ≤ 2 * K * kappa d ε := by
    have he := hratio 2 (by norm_num) ε (ε / 2) hε hh (by linarith)
    nlinarith only [he]
  let E := l2Norm ε U (fun q => u ε q - ū (physical ε q))
  let F := l2Norm (ε / 2) (halfDomain U)
    (fun q => v ε q - ū ((2 : ℝ) • physical (ε / 2) q))
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  have hcomp := source_error_comparison hd hε hU hlam ha f ū
    (hu ε hε) (hv ε hε) (heu ε hε) (hev ε hε)
  have hN := hnormr ⟨hε.1, hεr⟩
  have hgapabs : c ≤ |kappa d (ε / 2) - kappa d ε| := hgap.trans (le_abs_self _)
  have hcm : c * m ≤ kappa d (ε / 2) * E + kappa d ε / s * F :=
    (mul_le_mul hgapabs hN hm.le (abs_nonneg _)).trans hcomp
  have hcoeffE : kappa d (ε / 2) ≤ kappa d ε * H := by
    have hp : 0 ≤ kappa d ε * s⁻¹ := mul_nonneg (kappa_pos hd hε).le (inv_nonneg.mpr hs.le)
    dsimp only [H]
    nlinarith only [hκhalf, hp]
  have hcoeffF : kappa d ε / s ≤ kappa d ε * H := by
    have hp : 0 ≤ kappa d ε * (2 * K) :=
      mul_nonneg (kappa_pos hd hε).le (by positivity)
    dsimp only [H]
    rw [div_eq_mul_inv]
    nlinarith only [hp]
  have hbound : c * m ≤ (2 * C * H) * (|Real.log ε| * (E + F)) := by
    calc
      c * m ≤ kappa d (ε / 2) * E + kappa d ε / s * F := hcm
      _ ≤ (kappa d ε * H) * E + (kappa d ε * H) * F :=
        add_le_add (mul_le_mul_of_nonneg_right hcoeffE hE)
          (mul_le_mul_of_nonneg_right hcoeffF hF)
      _ = kappa d ε * (H * (E + F)) := by ring
      _ ≤ (2 * C * |Real.log ε|) * (H * (E + F)) :=
        mul_le_mul_of_nonneg_right hκ (mul_nonneg hH.le (add_nonneg hE hF))
      _ = _ := by ring
  refine ⟨ε, ⟨hε.1, lt_min hεδ hε.2⟩, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * C * H)).mpr
  simpa only [mul_comm] using hbound

/-- The introductory deterministic obstruction for the same realization, zero mass, domains
`U` and `U/2`, and forcings `f` and `4 f(2x)`. The continuum half-solution is produced from
its classical equation; the two actual discrete errors cannot both be little-o of `1/|log ε|`. -/
theorem source_scaling_obstruction (hd : 1 ≤ d) {lam : ℝ}
    {U : Set (Fin d → ℝ)} (hU : Bornology.IsBounded U) (hlam : 0 < lam)
    {a : Edge d → ℝ} (ha : ∀ e, lam ≤ a e ∧ a e ≤ lam⁻¹)
    (f ū : (Fin d → ℝ) → ℝ) {a₀ : ℝ}
    (hū : Elliptic.IsClassicalDirichletSolution U 0 a₀ f ū)
    (hne : ∃ x ∈ U, ū x ≠ 0) (u v : ℝ → Site d → ℝ)
    (hu : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε U (u ε))
    (hv : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn (ε / 2) (halfDomain U) (v ε))
    (heu : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet ε U,
      -generator ε a (u ε) q = f (physical ε q))
    (hev : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ latticeSet (ε / 2) (halfDomain U),
      -generator (ε / 2) a (v ε) q = 4 * f ((2 : ℝ) • physical (ε / 2) q)) :
    Elliptic.IsClassicalDirichletSolution (halfDomain U) 0 a₀
        (fun x => 4 * f ((2 : ℝ) • x)) (fun x => ū ((2 : ℝ) • x)) ∧
      ¬ (Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
          (fun ε => l2Norm ε U (fun q => u ε q - ū (physical ε q)))
          (fun ε => 1 / |Real.log ε|) ∧
        Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
          (fun ε => l2Norm (ε / 2) (halfDomain U)
            (fun q => v ε q - ū ((2 : ℝ) • physical (ε / 2) q)))
          (fun ε => 1 / |Real.log ε|)) := by
  refine ⟨classical_dirichlet_half hū, ?_⟩
  rintro ⟨hfirst, hsecond⟩
  obtain ⟨b, hb, hbound⟩ :=
    source_errors_frequently_lower_bound hd hU hlam ha f ū hū hne u v hu hv heu hev
  have hfirst' := hfirst.bound (by linarith : 0 < b / 4)
  have hsecond' := hsecond.bound (by linarith : 0 < b / 4)
  obtain ⟨r, hr, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hfirst'.and hsecond')
  obtain ⟨ε, hε, hlower⟩ := hbound r hr
  have he : ε ∈ Set.Ioo (0 : ℝ) 1 := ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  obtain ⟨hE, hF⟩ := hsmall ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hL : 0 < |Real.log ε| := abs_pos.mpr (Real.log_neg he.1 he.2).ne
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ l2Norm ε U _ from Real.sqrt_nonneg _),
    Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hL)] at hE
  rw [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ l2Norm (ε / 2) (halfDomain U) _ from Real.sqrt_nonneg _),
    Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hL)] at hF
  have hE' := mul_le_mul_of_nonneg_left hE hL.le
  have hF' := mul_le_mul_of_nonneg_left hF hL.le
  have hcancel : |Real.log ε| * (b / 4 * (1 / |Real.log ε|)) = b / 4 := by
    field_simp [hL.ne']
  rw [hcancel] at hE' hF'
  nlinarith only [hlower, hE', hF', hb]

/-- A concrete source-admissible application on the one-dimensional Euclidean unit ball:
unit conductances, diffusion `1/2`, datum `1`, and homogenized solution `1 - x²`.
The discrete solutions exist at every admissible spacing and their source errors have a
positive logarithmically normalized lower bound at arbitrarily small scales. -/
theorem quadratic_source_application :
    ∃ u v : ℝ → Site 1 → ℝ,
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1, SupportedIn ε (Elliptic.unitBall 1) (u ε) ∧
        ∀ q ∈ latticeSet ε (Elliptic.unitBall 1),
          -generator ε (fun _ => 1) (u ε) q = 1) ∧
      (∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        SupportedIn (ε / 2) (halfDomain (Elliptic.unitBall 1)) (v ε) ∧
        ∀ q ∈ latticeSet (ε / 2) (halfDomain (Elliptic.unitBall 1)),
          -generator (ε / 2) (fun _ => 1) (v ε) q = 4) ∧
      ∃ b : ℝ, 0 < b ∧ ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ,
        ε ∈ Set.Ioo (0 : ℝ) (min δ 1) ∧
        b ≤ |Real.log ε| *
          (l2Norm ε (Elliptic.unitBall 1)
              (fun q => u ε q - (1 - (physical ε q 0) ^ 2)) +
            l2Norm (ε / 2) (halfDomain (Elliptic.unitBall 1))
              (fun q => v ε q - (1 - ((2 : ℝ) • physical (ε / 2) q) 0 ^ 2))) := by
  classical
  have hU : Bornology.IsBounded (Elliptic.unitBall 1) :=
    Elliptic.isBounded_radius_sublevel 1
  have ha : ∀ e : Edge 1, (1 : ℝ) ≤ (fun _ => (1 : ℝ)) e ∧
      (fun _ => (1 : ℝ)) e ≤ (1 : ℝ)⁻¹ := fun _ => ⟨le_rfl, by norm_num⟩
  have hex (W : Set (Fin 1 → ℝ)) (hW : Bornology.IsBounded W) (g : Site 1 → ℝ) :
      ∀ ε : ℝ, ∃ u : Site 1 → ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 →
        SupportedIn ε W u ∧ ∀ q ∈ latticeSet ε W,
          -generator ε (fun _ => 1) u q = g q := by
    intro ε
    by_cases he : ε ∈ Set.Ioo (0 : ℝ) 1
    · obtain ⟨u, hu, _⟩ := existsUnique_dirichlet (d := 1) le_rfl he hW
        zero_lt_one ha g
      exact ⟨u, fun _ => hu⟩
    · exact ⟨fun _ => 0, fun h => (he h).elim⟩
  choose u hu using hex (Elliptic.unitBall 1) hU (fun _ => 1)
  choose w hw using hex (halfDomain (Elliptic.unitBall 1)) (halfDomain_isBounded hU)
    (fun _ => 4)
  let v : ℝ → Site 1 → ℝ := fun ε => w (ε / 2)
  have hv (ε : ℝ) (he : ε ∈ Set.Ioo (0 : ℝ) 1) :=
    hw (ε / 2) (show ε / 2 ∈ Set.Ioo (0 : ℝ) 1 from
      ⟨by linarith [he.1], by linarith [he.2]⟩)
  have hclass : Elliptic.IsClassicalDirichletSolution (Elliptic.unitBall 1) 0 (1 / 2)
      (fun _ => 1) (fun x => 1 - x 0 ^ 2) := by
    norm_num only [Fin.sum_univ_one, Nat.cast_one, zero_mul, zero_add] at *
    simpa using
      (Elliptic.quadratic_isClassicalDirichletSolution (d := 1) 0 (1 / 2))
  have hne : ∃ x ∈ Elliptic.unitBall 1, (1 - x 0 ^ 2 : ℝ) ≠ 0 := by
    refine ⟨0, ?_, by norm_num⟩
    simp [Elliptic.unitBall, radius]
  refine ⟨u, v, hu, hv, ?_⟩
  exact source_errors_frequently_lower_bound (d := 1) le_rfl hU zero_lt_one ha
    (fun _ => 1) (fun x => 1 - x 0 ^ 2) hclass hne u v
    (fun ε he => (hu ε he).1) (fun ε he => (hv ε he).1)
    (fun ε he => (hu ε he).2) (fun ε he => by
      simpa only [mul_one] using (hv ε he).2)

end

end LongRange.Scaling
