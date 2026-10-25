import LongRange.Dirichlet.LongPart
import LongRange.Dirichlet.ShortMean
import LongRange.Dirichlet.ShortConcentration
import LongRange.Dirichlet.NearestNeighbour
import LongRange.Corrector.Definition
import LongRange.Poincare.Inequality

/-!
# Corrector energy estimates

The short and long defect estimates give the normalized corrector energy bound.
The Poincaré inequality then controls the square norm of coordinate correctors.
-/

namespace LongRange

open MeasureTheory LatticeProb LatticeProb.Euclidean.Lattice Dirichlet

noncomputable section

/-- Splitting the flux defect bounds its nearest-neighbour energy by the two parts. -/
private theorem nnEnergy_flux_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) {U : Set (Fin d → ℝ)}
    (hU : Bornology.IsBounded U) {a : Edge d → ℝ} {A : ℝ}
    (ha : ∀ e, |a e| ≤ A) (m : ℝ) (p : Fin d → ℝ) :
    nnEnergy ε (latticeSet_finite hε.1 hU).toFinset (fluxDefect ε U a m p) ≤
      2 * nnEnergy ε (latticeSet_finite hε.1 hU).toFinset (shortDefect ε U a m p) +
      2 * nnEnergy ε (latticeSet_finite hε.1 hU).toFinset (longDefect ε U a m p) := by
  unfold nnEnergy
  have halgebra (q s l : ℝ) : 2 * (q * s) + 2 * (q * l) =
      q * (2 * s + 2 * l) := by ring
  rw [halgebra]
  apply mul_le_mul_of_nonneg_left _
    (div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le)
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro i _
  have hx' : x ∈ latticeSet ε U := by
    simpa only [Set.Finite.mem_toFinset] using hx
  rw [fluxDefect_eq_short_add_long hd hε.1 hU ha m p hx' (unit_ne_zero i),
    fluxDefect_eq_short_add_long hd hε.1 hU ha m p hx' (neg_ne_zero.mpr (unit_ne_zero i))]
  nlinarith only [sq_add_le_two_mul (shortDefect ε U a m p x (unit i))
    (longDefect ε U a m p x (unit i)),
    sq_add_le_two_mul (shortDefect ε U a m p x (-unit i))
    (longDefect ε U a m p x (-unit i))]

/-- Proposition 3.3 with the normalization valid at every scale in `(0,1)`. -/
theorem corrector_energy_bound_kappa (d : ℕ) (lam R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ U : Set (Fin d → ℝ), Bornology.IsBounded U → euclideanDiam U ≤ R →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ p : Fin d → ℝ,
      ∀ φ : Ω → Site d → ℝ, (∀ ω, IsCorrectorMinimizer ε U (a ω) p (φ ω)) →
      ∃ X₁ X₂ : Ω → ℝ, Measurable X₁ ∧ Measurable X₂ ∧
        OsBound P 1 (C * radius p ^ 2 * ε ^ d / kappa d ε) X₁ ∧
        OsBound P 2 (C * radius p ^ 2 * ε ^ ((d : ℝ) / 2)) X₂ ∧
        ∀ ω, correctorEnergy ε U (a ω) p + h1CritSq ε (φ ω) ≤
          C * radius p ^ 2 / kappa d ε + X₁ ω + X₂ ω := by
  classical
  obtain ⟨L, hL, hl⟩ := longPart_osBound d lam R
  obtain ⟨M, hM, hm⟩ := shortPart_integral_le d lam R
  obtain ⟨B, hB, hb⟩ := shortPart_concentration d lam R
  let c := 2 * lam⁻¹ * (1 + 2 * lam⁻¹)
  let C := c * (L + M + B) + 1
  by_cases hlam : 0 < lam
  · have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨C, by dsimp [C]; positivity, ?_⟩
    intro Ω _ P a hA U hU hR ε hε p φ hφ
    have heps := hε.1
    have hkap := kappa_pos hA.one_le_dim hε
    let S := (latticeSet_finite hε.1 hU).toFinset
    let m := meanConductance P hA.one_le_dim a
    let FL := fun ω => nnEnergy ε S (longDefect ε U (a ω) m p)
    let FS := fun ω => nnEnergy ε S (shortDefect ε U (a ω) m p)
    have hFL : Measurable FL := by
      dsimp [FL, nnEnergy]
      exact measurable_const.mul (Finset.measurable_sum _ (fun x _ =>
        Finset.measurable_sum _ (fun i _ =>
          ((measurable_longDefect hA.measurable ε U m p x _).pow_const 2).add
            ((measurable_longDefect hA.measurable ε U m p x _).pow_const 2))))
    have hFS : Measurable FS := by
      dsimp [FS, nnEnergy]
      exact measurable_const.mul (Finset.measurable_sum _ (fun x _ =>
        Finset.measurable_sum _ (fun i _ =>
          ((measurable_shortDefect hA.measurable ε U m p x _).pow_const 2).add
            ((measurable_shortDefect hA.measurable ε U m p x _).pow_const 2))))
    have hCL : c * L ≤ C := by dsimp [C]; nlinarith
    have hCM : c * M ≤ C := by dsimp [C]; nlinarith
    have hCB : c * B ≤ C := by dsimp [C]; nlinarith
    refine ⟨fun ω => c * FL ω, fun ω => c * |FS ω - ∫ ω', FS ω' ∂P|,
      measurable_const.mul hFL, measurable_const.mul ((hFS.sub measurable_const).abs),
      ?_, ?_, ?_⟩
    · have hs := osBound_const_mul (hl hA ε hε U hU hR p) hc.le
      apply OsBound.mono (Y := fun ω => c * FL ω) _ _ (fun _ => le_rfl) hs
      · calc
          _ = (c * L) * radius p ^ 2 * ε ^ d / kappa d ε := by ring
          _ ≤ _ := by gcongr
      · positivity
    · have hs := osBound_const_mul (hb hA ε hε U hU hR p) hc.le
      apply OsBound.mono (Y := fun ω => c * |FS ω - ∫ ω', FS ω' ∂P|)
        _ _ (fun _ => le_rfl) hs
      · calc
          _ = (c * B) * radius p ^ 2 * ε ^ ((d : ℝ) / 2) := by ring
          _ ≤ _ := by gcongr
      · positivity
    · intro ω
      have hcomp := (correctorEnergy_comparison hA.one_le_dim hε hU hlam
        (hA.bounds ω) p (hφ ω).1 (hφ ω).2).1
      have hcrit : h1CritSq ε (φ ω) ≤ 2 * lam⁻¹ * correctorEnergy ε U (a ω) p := by
        calc
          _ = (2 * lam⁻¹) * (lam / 2 * h1CritSq ε (φ ω)) := by
            field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hcomp (by positivity)
      have hflux := correctorEnergy_le_fluxDefect hA.one_le_dim hε hU hlam
        (hA.bounds ω) m p
      have hsplit := nnEnergy_flux_le hA.one_le_dim hε hU
        (fun e => (abs_of_nonneg (hlam.le.trans (hA.bounds ω e).1)).symm ▸
          (hA.bounds ω e).2) m p
      have henergy : correctorEnergy ε U (a ω) p ≤
          lam⁻¹ * (2 * FS ω + 2 * FL ω) := by
        calc
          _ ≤ lam⁻¹ * nnEnergy ε S (fluxDefect ε U (a ω) m p) := by
            simpa only [nnEnergy, mul_assoc] using hflux
          _ ≤ _ := mul_le_mul_of_nonneg_left hsplit (by positivity)
      have htotal : correctorEnergy ε U (a ω) p + h1CritSq ε (φ ω) ≤
          c * (FS ω + FL ω) := by
        calc
          _ ≤ (1 + 2 * lam⁻¹) * correctorEnergy ε U (a ω) p := by linarith
          _ ≤ (1 + 2 * lam⁻¹) * (lam⁻¹ * (2 * FS ω + 2 * FL ω)) :=
            mul_le_mul_of_nonneg_left henergy (by positivity)
          _ = _ := by dsimp [c]; ring
      have hmean := (hm hA ε hε U hU hR p).2
      have hdev : FS ω ≤ (∫ ω', FS ω' ∂P) + |FS ω - ∫ ω', FS ω' ∂P| := by
        linarith only [le_abs_self (FS ω - ∫ ω', FS ω' ∂P)]
      calc
        _ ≤ c * (FS ω + FL ω) := htotal
        _ ≤ c * ((∫ ω', FS ω' ∂P) + |FS ω - ∫ ω', FS ω' ∂P| + FL ω) :=
          mul_le_mul_of_nonneg_left (add_le_add hdev le_rfl) hc.le
        _ ≤ c * (M * radius p ^ 2 / kappa d ε) + c * FL ω +
            c * |FS ω - ∫ ω', FS ω' ∂P| := by
          nlinarith only [mul_le_mul_of_nonneg_left hmean hc.le]
        _ ≤ _ := by
          have hdet : c * (M * radius p ^ 2 / kappa d ε) ≤
              C * radius p ^ 2 / kappa d ε := by
            calc
              _ = (c * M) * radius p ^ 2 / kappa d ε := by ring
              _ ≤ _ := div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hCM (sq_nonneg _))
                (kappa_pos hA.one_le_dim hε).le
          linarith only [hdet]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hlam hA.lam_pos).elim

/-- Proposition 3.3 in its printed logarithmic normalization. -/
theorem corrector_energy_bound (d : ℕ) (lam : ℝ) (U : Set (Fin d → ℝ))
    (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ p : Fin d → ℝ,
      ∀ φ : Ω → Site d → ℝ, (∀ ω, IsCorrectorMinimizer ε U (a ω) p (φ ω)) →
      ∃ X₁ X₂ : Ω → ℝ, Measurable X₁ ∧ Measurable X₂ ∧
        OsBound P 1 (C * radius p ^ 2 * ε ^ d / |Real.log ε|) X₁ ∧
        OsBound P 2 (C * radius p ^ 2 * ε ^ ((d : ℝ) / 2)) X₂ ∧
        ∀ ω, correctorEnergy ε U (a ω) p + h1CritSq ε (φ ω) ≤
          C * radius p ^ 2 / |Real.log ε| + X₁ ω + X₂ ω := by
  by_cases hd : 1 ≤ d
  · obtain ⟨K, hK, hk⟩ := corrector_energy_bound_kappa d lam (euclideanDiam U)
    obtain ⟨c, hc, hlo⟩ := le_kappa hd
    let C := K * (1 + 1 / c)
    have hC : 0 < C := by dsimp [C]; positivity
    have hKC : K ≤ C := by dsimp [C]; nlinarith [div_pos zero_lt_one hc]
    refine ⟨C, hC, ?_⟩
    intro Ω _ P a hA ε hε p φ hφ
    have heps := hε.1
    have hkap := kappa_pos hd hε
    obtain ⟨X₁, X₂, hm₁, hm₂, ho₁, ho₂, hbound⟩ :=
      hk P a hA U hU le_rfl ε hε p φ hφ
    have hlog : 0 < |Real.log ε| := abs_pos.mpr (ne_of_lt (Real.log_neg hε.1 hε.2))
    have hratio : K / kappa d ε ≤ C / |Real.log ε| := by
      apply (div_le_div_iff₀ (kappa_pos hd hε) hlog).mpr
      have hlow : c * |Real.log ε| ≤ kappa d ε := by
        calc
          _ ≤ c * (1 + |Real.log ε|) := by nlinarith
          _ ≤ _ := hlo ε hε
      have hdiv : |Real.log ε| ≤ kappa d ε / c :=
        (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hlow)
      have hKC' : K / c ≤ C := by
        calc
          _ ≤ K + K / c := le_add_of_nonneg_left hK.le
          _ = _ := by dsimp [C]; ring
      calc
        K * |Real.log ε| ≤ K * (kappa d ε / c) :=
          mul_le_mul_of_nonneg_left hdiv hK.le
        _ = (K / c) * kappa d ε := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKC' (kappa_pos hd hε).le
    have hscale (t : ℝ) (ht : 0 ≤ t) : K * t / kappa d ε ≤ C * t / |Real.log ε| := by
      simpa only [div_mul_eq_mul_div, mul_comm K t, mul_comm C t] using
        mul_le_mul_of_nonneg_right hratio ht
    refine ⟨X₁, X₂, hm₁, hm₂, ?_, ?_, ?_⟩
    · apply OsBound.mono _ (by positivity) (fun _ => le_rfl) ho₁
      simpa only [mul_assoc] using
        hscale (radius p ^ 2 * ε ^ d) (by positivity)
    · exact OsBound.mono (by gcongr) (by positivity) (fun _ => le_rfl) ho₂
    · intro ω
      exact (hbound ω).trans (add_le_add
        (add_le_add (hscale (radius p ^ 2) (sq_nonneg _)) le_rfl) le_rfl)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hd hA.one_le_dim).elim

/-- Proposition 5.1: the critical and square norms of each coordinate corrector. -/
theorem corrector_domain_bound (d : ℕ) (lam : ℝ) (U : Set (Fin d → ℝ))
    (hUo : IsOpen U) (hU : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (a : Ω → Edge d → ℝ), AssumptionU P lam a →
      ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ i : Fin d,
      ∀ φ : Ω → Site d → ℝ,
      (∀ ω, IsCorrectorSolution ε U (a ω) (Pi.single i 1) (φ ω)) →
      ∃ X₁ X₂ : Ω → ℝ, Measurable X₁ ∧ Measurable X₂ ∧
        OsBound P 1 (C * ε ^ d / kappa d ε) X₁ ∧
        OsBound P 2 (C * ε ^ ((d : ℝ) / 2)) X₂ ∧
        ∀ ω, h1CritSq ε (φ ω) + l2NormSq ε U (φ ω) ≤
          C / kappa d ε + X₁ ω + X₂ ω := by
  by_cases hd : 1 ≤ d
  · obtain ⟨K, hK, hk⟩ := corrector_energy_bound_kappa d lam (euclideanDiam U)
    obtain ⟨B, hB, hb⟩ := poincare d hd (euclideanDiam U)
    let c := 1 + B
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c * K, mul_pos hc hK, ?_⟩
    intro Ω _ P a hA ε hε i φ hφ
    have heps := hε.1
    have hlam := hA.lam_pos
    have hmin (ω : Ω) := (hφ ω).isCorrectorMinimizer hd hε hU hA.lam_pos (hA.bounds ω)
    obtain ⟨X₁, X₂, hm₁, hm₂, ho₁, ho₂, hbound⟩ :=
      hk P a hA U hU le_rfl ε hε (Pi.single i 1) φ hmin
    have hr : radius (Pi.single i (1 : ℝ)) = 1 := by
      simp [radius, Pi.single_apply]
    simp only [hr, one_pow, mul_one] at ho₁ ho₂ hbound
    refine ⟨fun ω => c * X₁ ω, fun ω => c * X₂ ω,
      measurable_const.mul hm₁, measurable_const.mul hm₂, ?_, ?_, ?_⟩
    · convert osBound_const_mul ho₁ hc.le using 1
      ring
    · convert osBound_const_mul ho₂ hc.le using 1
      ring
    · intro ω
      have hnorm : 0 ≤ h1CritSq ε (φ ω) := by
        unfold h1CritSq
        exact mul_nonneg
          (div_nonneg (pow_nonneg hε.1.le _) (kappa_pos hd hε).le)
          (tsum_nonneg (fun _ => mul_nonneg (jumpKernel_nonneg _) (sq_nonneg _)))
      have henergy : 0 ≤ correctorEnergy ε U (a ω) (Pi.single i 1) :=
        (mul_nonneg (by positivity) hnorm).trans
          (correctorEnergy_comparison hd hε hU hA.lam_pos (hA.bounds ω)
            (Pi.single i 1) (hmin ω).1 (hmin ω).2).1
      have hp := hb U hUo hU le_rfl ε hε (φ ω) (hφ ω).1
      calc
        _ ≤ c * h1CritSq ε (φ ω) := by dsimp [c]; linarith only [hp]
        _ ≤ c * (correctorEnergy ε U (a ω) (Pi.single i 1) +
            h1CritSq ε (φ ω)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left henergy) hc.le
        _ ≤ c * (K / kappa d ε + X₁ ω + X₂ ω) :=
          mul_le_mul_of_nonneg_left (hbound ω) hc.le
        _ = _ := by ring
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Ω _ P a hA
    exact (hd hA.one_le_dim).elim

end

end LongRange
